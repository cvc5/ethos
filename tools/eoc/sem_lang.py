"""The language the signatures under semantics are written in.

  semantics/smt.eos  compiles to tools/eoc/out/smt_defs.eo
  semantics/development-cpc.eos  compiles to tools/eoc/out/user_defs.eo

Each set is one file: a heading, then its theories one to a section. This
module is the whole of the language -- how a file is read, what it may hold,
and what each form compiles to. What the compiler *writes* is not here, see
sem_target.py; what a run does with the result is in sem_compile.py.

A file is read as *text* as well as as terms: a form keeps the source it was
written with, so that a place read as the source it is -- a pattern at a place
of the input -- reaches the generated file untouched, exactly as
plugins/model_smt/defs_reader.cpp keeps a block of a definitions file.

What a set has is a sequence of *blocks*, each named after the symbol it is of.
A block holds *pieces*, and every piece is an entry the compiler expands:
nothing is carried over as the text it is, so what a set names the compiler has
read and can check, order and trim with the rest. A `; -- X` comment line opens
a block and gathers what follows into it; without one, each form is a block of
its own, named after what it defines.
"""

import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import report  # noqa: E402


def die(msg):
  """What the configuration got wrong, said the way every tool of the pipeline
  says one, see report.error."""
  report.error(msg)
  sys.exit(1)


# -----------------------------------------------------------------------------
# Reading a file
# -----------------------------------------------------------------------------

class Node:
  """One s-expression, together with the source it was written with.

  A list also keeps the whitespace that stood before each of its items and
  before its closing bracket. That is what lets a form be rewritten -- a name
  of the surface put where a name of the embedding was -- and come out laid out
  as it was written, however many lines it runs to.
  """

  __slots__ = ('kind', 'val', 'items', 'raw', 'gaps', 'tail')

  def __init__(self, kind, val=None, items=None, raw='', gaps=None, tail=''):
    # kind is one of 'list', 'sym', 'str', 'kw', 'int', and 'pre' for text
    # the compiler has already rendered
    self.kind = kind
    self.val = val
    self.items = items or []
    self.raw = raw
    self.gaps = gaps if gaps is not None else []
    self.tail = tail

  def laid_out(self, parts):
    """The parts of this list, put back with the whitespace it was written
    with. A list the compiler built rather than read has none, and falls back
    to one space between."""
    if len(self.gaps) != len(parts):
      return '(%s)' % ' '.join(parts)
    return '(%s%s)' % (''.join(g + p for g, p in zip(self.gaps, parts)),
                       self.tail)

  def is_sym(self, name=None):
    return self.kind == 'sym' and (name is None or self.val == name)

  def head(self):
    """The first item, if this is a non-empty list."""
    return self.items[0] if self.kind == 'list' and self.items else None

  def __repr__(self):
    if self.kind == 'list':
      return '(' + ' '.join(repr(i) for i in self.items) + ')'
    return str(self.val)


_DELIM = set('()') | set(' \t\r\n') | {';', '"', '|'}


class Reader:
  """Reads one surface file into forms, each with the comments above it."""

  def __init__(self, text, path='<input>'):
    self.t = text
    self.n = len(text)
    self.i = 0
    self.path = path

  def error(self, msg):
    line = self.t.count('\n', 0, self.i) + 1
    raise SyntaxError('%s:%d: %s' % (self.path, line, msg))

  def read_all(self):
    """Every top-level form, as (doc_lines, node) pairs."""
    out = []
    doc = []
    while True:
      doc = self._skip_space(doc)
      if self.i >= self.n:
        return out
      out.append((doc, self._read()))
      doc = []

  def _skip_space(self, doc):
    """Skip whitespace and comments, keeping the comment block last seen.

    A blank line ends a comment block, which is what lets a file carry a
    heading of its own without it becoming the first form's documentation.
    """
    while self.i < self.n:
      c = self.t[self.i]
      if c == ';':
        end = self.t.find('\n', self.i)
        end = self.n if end < 0 else end
        doc.append(self.t[self.i:end].rstrip())
        self.i = end
      elif c == '\n':
        # A blank line, i.e. a newline with only space before the next one.
        j = self.i + 1
        while j < self.n and self.t[j] in ' \t\r':
          j += 1
        if j < self.n and self.t[j] == '\n':
          doc = []
        self.i += 1
      elif c in ' \t\r':
        self.i += 1
      else:
        return doc
    return doc

  def _read(self):
    start = self.i
    c = self.t[self.i]
    if c == '(':
      self.i += 1
      items, gaps = [], []
      while True:
        before = self.i
        self._skip_space([])
        gap = self.t[before:self.i]
        if self.i >= self.n:
          self.i = start
          self.error('unterminated list')
        if self.t[self.i] == ')':
          self.i += 1
          return Node('list', items=items, raw=self.t[start:self.i],
                      gaps=gaps, tail=gap)
        gaps.append(gap)
        items.append(self._read())
    if c == ')':
      self.error('unexpected )')
    if c == '|':
      self.error('a bar delimits nothing here; every form of a set is '
                 'written as an s-expression')
    if c == '"':
      self.i += 1
      # A backslash escapes the character after it, which is what lets a
      # string hold a quote: the Lean an implementation is written as holds
      # its own strings, see :lean-impl.
      while self.i < self.n and self.t[self.i] != '"':
        self.i += 2 if self.t[self.i] == '\\' else 1
      if self.i >= self.n:
        self.error('unterminated string')
      self.i += 1
      raw = self.t[start:self.i]
      return Node('str', val=unescape(raw[1:-1]), raw=raw)
    while self.i < self.n and self.t[self.i] not in _DELIM:
      self.i += 1
    raw = self.t[start:self.i]
    if raw.startswith(':'):
      return Node('kw', val=raw, raw=raw)
    if raw.isdigit():
      return Node('int', val=int(raw), raw=raw)
    return Node('sym', val=raw, raw=raw)


def unescape(text):
  """What a string literal stands for: a backslash takes the character after
  it as it is written. Only the two that have to be escaped are given a
  meaning, so a backslash before anything else is that backslash.
  """
  out = []
  i, n = 0, len(text)
  while i < n:
    if text[i] == '\\' and i + 1 < n and text[i + 1] in '\\"':
      out.append(text[i + 1])
      i += 2
    else:
      out.append(text[i])
      i += 1
  return ''.join(out)


def read_text(path):
  """The text of a file, read the one way the compiler reads one.

  A file is UTF-8 whatever the machine says, and its lines end however they
  end: reading in text mode is what makes both spellings of a line ending one
  thing, so what the compiler sees does not depend on how a tree was checked
  out. See write_text for the other half.
  """
  with open(path, encoding='utf-8') as f:
    return f.read()


def write_text(path, text):
  """Write the text of a file, on the same terms and with lines ending in one
  newline, whatever the machine would end them with of its own accord."""
  with open(path, 'w', encoding='utf-8', newline='\n') as f:
    f.write(text)


def read_file(path):
  return Reader(read_text(path), path).read_all()


def applied(head, xs):
  """A symbol given its arguments, or the symbol itself if it takes none."""
  return '(%s%s)' % (head, ''.join(' ' + x for x in xs)) if xs else head


# The line that opens a block and names it.
MARK = re.compile(r'^; -- (\S+)\s*$')


# -----------------------------------------------------------------------------
# Blocks
# -----------------------------------------------------------------------------

class Block:
  """One block of a generated signature, i.e. `; -- X` and what follows it.

  The pieces are rendered in the order they were read, so a program a symbol
  names comes out above the symbol that names it, exactly as the file says.
  """

  def __init__(self, name, origin):
    self.name = name
    self.origin = origin        # the file it was read from, for messages
    self.pieces = []

  def add(self, piece):
    self.pieces.append(piece)

  def entries(self):
    """The entries the block holds. Every piece is one: a set carries no text
    of its own, see read_config."""
    return list(self.pieces)

  def defines(self):
    """The names this block defines, whether written out or compiled."""
    out = set()
    for p in self.pieces:
      out.update(getattr(p, 'defines', set)())
    return out

  def render(self, ctx):
    body = [b for b in (p.render(ctx) for p in self.pieces) if b]
    # A block whose whole of what it says reaches another file -- the Lean
    # text of a method does -- is no block of this one.
    return '; -- %s\n%s' % (self.name, '\n'.join(body)) if body else ''


def reserved_by(name, decls):
  """What a name is where it is one the compiler writes, and nothing if it is
  the file's own to write.

  Which names those are is settled by what the set compiles to and so is read
  off its shape, see Shape.reserved; the longest prefix is the one that says
  what the name is, the way it does for a block.
  """
  for pre, what in decls.reserved():
    if name.startswith(pre):
      return pre, what
  return None


def check_own_name(name, path, decls):
  """A file writes out a program of its own, never one the compiler writes.

  A name the compiler gives is given to what the compiler writes there: a
  program written by hand under one stands where that would have stood, and is
  reached by naming a symbol rather than by naming itself, which is the whole
  of what a name of a body means. A helper is named as itself instead, and the
  case that reaches for it names it as itself too.
  """
  found = reserved_by(name, decls)
  if found is None:
    return
  die('%s: %s is %s, which the compiler writes for itself, so no file writes '
      'one out under that name; a program of the set is named as itself, and '
      'a case names it as itself in turn' % (os.path.basename(path), name,
                                             found[1]))


def read_config(paths, decls):
  """Read one configuration set into blocks, in the order the files give them.

  `decls` is what the central file of the set declared, which is what says how
  a symbol of it is read and what it compiles to. Every form of a set is one of
  those, a program, a macro or a section, and a form that is none of them is
  refused rather than carried over as the text it is. define-macro is common to
  both sets: it names an idiom the bodies of that file would otherwise repeat,
  and reaches no generated file.

  An entry written under a `; -- X` line whose name it carries joins that
  block, which is how a symbol keeps the programs its cases name in the block
  that is kept or dropped with it. Any other entry opens a block of its own.
  """
  entries = dict(PROGRAM_ENTRY,
                 **{kw: parser(shape)
                    for kw, shape in decls.parsers().items()})
  blocks, macros, seen = [], {}, {}
  for path in paths:
    open_block = None
    for doc, node in read_file(path):
      head = node.head()
      kind = head.val if head is not None and head.kind == 'sym' else None
      mark = next((MARK.match(d) for d in doc if MARK.match(d)), None)
      if kind == 'section':
        # A section is where one theory ends and the next begins. It closes
        # whatever block is open, so that a program at the head of a theory
        # opens one of its own rather than joining the theory before it.
        if len(node.items) != 2 or node.items[1].kind != 'str':
          die('%s: a section is written (section "Title")' % path)
        open_block = None
        continue
      if kind == 'define-macro':
        # A macro may be written with the ones above it, so its body is
        # expanded as it is read and what is kept is already flat.
        macros[node.items[1].val] = (
            [i.val for i in node.items[2].items],
            expand_macros(node.items[3], macros, node.items[1].val))
        open_block = None
        continue
      if mark is not None:
        # A comment above the `; -- X` line documents the surface; one below it
        # is the block's own text.
        doc = doc[[bool(MARK.match(d)) for d in doc].index(True) + 1:]
      if kind in entries:
        # A program is emitted as itself, so the comment above it is what its
        # block says for itself. Any other entry compiles to something else --
        # a constructor, a case of an aggregate -- so a comment above it
        # documents the *configuration* and what the block says is :doc.
        piece = entries[kind](node, path, macros)
        if kind in PROGRAM_ENTRY:
          check_own_name(piece.name, path, decls)
        piece.doc = doc
        # An entry belongs to the block already open when that block is named
        # after it, or when it belongs to no symbol -- as a program does -- and
        # so belongs to whichever block it stands in.
        joins = (open_block is not None
                 and (open_block.name == piece.name
                      or getattr(piece, 'joins_open_block', False)))
        name = piece.block_name or piece.name
      else:
        # Every form of a set is an entry it declares, a program, a macro or a
        # section. Nothing else is carried over: a form emitted as the text it
        # is would put into the generated file something the compiler never
        # read, so what it names could not be checked, ordered or trimmed with
        # the rest. A declaration of the embedding is therefore written in
        # plugins/model_smt/model_smt.eo, which is where the embedding says
        # what it is built from; a set says what a theory *does* with it.
        die('%s: %s is not a form of a configuration set, which takes %s'
            % (path, kind if kind is not None else node.raw[:40],
               ', '.join(sorted(entries))
               + ', define-macro, section and the declarations of the set'))
      if mark is not None:
        # A `; -- X` line opens a block of its own and gathers what follows.
        name, joins = mark.group(1), False
      elif joins:
        open_block.add(piece)
        continue
      if name is None:
        die('%s: cannot tell what block %s belongs to; open one with a '
            '`; -- name` line' % (path, node.raw[:40]))
      block = Block(name, path)
      block.add(piece)
      open_block = block if mark is not None else None
      if block.name in seen:
        die('%s: %s is given twice, see %s'
            % (os.path.basename(path), block.name,
               os.path.basename(seen[block.name])))
      seen[block.name] = path
      blocks.append(block)
  # A macro is matched by its whole name, before a name is read as a symbol, so
  # one named after a symbol of the set would shadow it silently.
  for m in macros:
    if m in seen:
      die('%s is both a macro and a symbol of this set' % m)
  return blocks


# -----------------------------------------------------------------------------
# The levels, i.e. the vocabularies a term of the embedding is written in
# -----------------------------------------------------------------------------

# A term of the embedding is written in one of four vocabularies, and which one
# is said by the *type of the place it stands in*: a native is applied to
# natives, an evaluator to values, a symbol of the signature to terms, a type
# constructor to types. What a bare name and a whole number mean is the whole
# of the difference; a native in quotes and a $-name of the embedding are what
# they are wherever they stand.
LEVELS = {'$smt_Value': 'value', '$smt_Term': 'term', '$smt_Type': 'type'}

# The family a bare name belongs to at each level. A level not named here has
# none, so a bare name standing there is an error rather than a guess.
FAMILY = {'value': '$smtx_model_eval_', 'term': '$sm_', 'type': '$tsm_'}

# The level the *subject* of an aggregate is written at, read off the family
# prefix its cases match under: a case of one is matched against terms of that
# level, so a pattern it gives is cast the way a body at that level is. An
# aggregate that matches under no family prefix has a subject of the input,
# whose patterns are taken as the input wrote them.
MATCH_LEVEL = {fam: lvl for lvl, fam in FAMILY.items()}

# What a whole number is at each level, i.e. what wraps the native it denotes.
NUMERAL = {'value': '$vsm_Numeral', 'term': '$sm_Numeral'}

# What a term of the *input* becomes where a term or a type of the embedding is
# wanted, which is the aggregate of that level applied to it. It is read off the
# declarations of the set, see Decls.transform_into, so no file of the
# configuration names it: a name of the input simply stands where the embedding
# is wanted, and the compiler puts the transformation in.

# One name of a body, read the way the reader reads a symbol: up to whitespace,
# a bracket, a quote or a bar. Matching whole names is what keeps a parameter
# called `s` from being found inside $sm_str.len.
TOKEN = re.compile(r'[^\s()|";]+')


class Scope:
  """What the names of a body stand for.

  A name the entry declares stands for what `names` says; one the body itself
  binds stands for itself. A name of the *input* -- an argument an entry gives
  raw, or one a case matched at a place the signature says is of the input --
  is transformed wherever a term or a type of the embedding is wanted, and
  stands for itself everywhere else. That is the same reading the rest of the
  surface has: the place says what is written there.
  """

  __slots__ = ('names', 'bound', 'surface', 'used', 'into')

  def __init__(self, names=None, bound=(), surface=(), used=None, into=None):
    self.names = names or {}
    self.bound = frozenset(bound)
    self.surface = frozenset(surface)
    # What a name of the input becomes at each level, i.e. the aggregate of
    # that level applied to it. Empty where the set has no names of the input.
    self.into = into or {}
    # The levels each name was read at, which is what says what a name an
    # eo::define binds has to be. It is shared down the scopes of one body.
    self.used = {} if used is None else used

  def binding(self, name, afresh=False):
    """The same scope, with one more name standing for itself."""
    return Scope(self.names, self.bound | {name}, self.surface,
                 {} if afresh else self.used, self.into)

  def standing(self, name, text):
    """The same scope, with one more name standing for a term already cast."""
    return Scope(dict(self.names, **{name: text}), self.bound, self.surface,
                 self.used, self.into)

  def stands_for(self, name, level, entry):
    """What a name of the scope is written as at a level, or None if it is not
    one of the scope's."""
    if name in self.names:
      text = self.names[name]
    elif name in self.bound:
      text = name
    else:
      return None
    self.used.setdefault(name, set()).add(level)
    if name in self.surface and level in self.into:
      return self.into[level] % text
    return text

  def level_of_use(self, name):
    """The level a body read a name at, where it read it at just one."""
    at = self.used.get(name, ())
    return next(iter(at)) if len(at) == 1 else None

  def names_of(self, node, declared):
    """The same scope, with what an input pattern matched taken as the input's.

    A case binds only what its own pattern matches, and a pattern at a place of
    the input is read as the input wrote it, so what it binds is of the input.
    """
    found = {t for t in TOKEN.findall(node.raw) if t in declared}
    return Scope(self.names, self.bound, self.surface | found, self.used,
                 self.into)


def smt_type(name):
  """The type of the embedding a name of the surface stands for, or None.

  A type is named without the `$smt_` it is declared under, the way a native is
  named without its `$native_`: SmtValue is $smt_Value. Nothing else in a
  signature is spelt that way, so a bare name is a type of the *input* and is
  taken as the input wrote it.
  """
  return ('$smt_' + name[3:] if name[:3] == 'Smt' and len(name) > 3
          and name[3].isupper() else None)


def level_of(node):
  """The vocabulary a term of this type is written in.

  None where the type is one of the *input*, whose terms are taken as the input
  wrote them; 'embedding' where it is one of the embedding that has no bare
  names of its own, as $smt_Map has none.
  """
  head = node.items[0] if node.kind == 'list' and node.items else node
  if head.kind == 'str':
    return 'native'             # a native type, named the way a native is
  name = head.val if head.kind == 'sym' else ''
  # A configuration names a type of the embedding by itself, the file that
  # declares it by the name it is declared under; both are that type.
  name = smt_type(name) or name
  if name.startswith('$native_'):
    return 'native'
  if name in LEVELS:
    return LEVELS[name]
  return 'embedding' if name.startswith('$smt_') else None


def sig_level(node):
  """The same, for a place a *signature* declares.

  A signature says what a program takes, so a type it names that is not one of
  the embedding is one of the input, where a parameter of a native declaring a
  type variable -- the branches of ite -- says nothing and takes the level
  around it.
  """
  return level_of(node) or 'input'


# -----------------------------------------------------------------------------
# The vocabulary of the embedding
# -----------------------------------------------------------------------------

class Vocab:
  """Every $-name the embedding defines, and what each takes.

  A file of the configuration never writes a $native_ name out: it names the
  native in quotes, `"ite"` for $native_ite, and the compiler puts the name
  back. Reading the vocabulary from the files that define it is what lets a
  misspelt or misapplied native be caught here rather than by ethos.

  The same reading says what *level* each argument of a name is of, so that a
  bare name or a whole number standing under one is read in the vocabulary of
  the place it stands in and in no other. Nothing states this twice: the
  declaration is already there.
  """

  def __init__(self):
    self.args = {}            # $name -> the level of each argument
    self.types = {}           # $name -> the type each argument is declared as
    self.ops = {}             # the operator a native is defined as -> it
    self.ints = {}            # (level, value) -> what the embedding calls it
    self.aliases = []         # the apply each native is defined as, and it

  def __contains__(self, name):
    return name in self.args

  def arity(self, name):
    return len(self.args[name])

  def arg_level(self, name, i, level):
    """Which vocabulary the i'th argument of a name is written in.

    A declaration that says nothing -- a branch of ite, whose type is whatever
    stands around it -- leaves the level as it was.
    """
    ls = self.args.get(name)
    if ls is None or i >= len(ls):
      return level
    return ls[i] or level

  def numeral(self, value, level, entry):
    """A whole number, as the vocabulary of a level writes one.

    A native is the constant the embedding names it by where it has one, and
    the operator it stands for otherwise; at any other level it is the numeral
    of that native, likewise named where the embedding names it.
    """
    if (level, value) in self.ints:
      return self.ints[(level, value)]
    return numeral_wrap(
        self.ints.get(('native', value), '($native_apply_0 "%d")' % value),
        level, entry)

  def extended(self, blocks):
    """The same vocabulary, together with what one set writes out.

    A program a symbol's cases name is written in the set rather than in the
    embedding, so what it takes is read off it here, the same way and for the
    same reason. So is the constructor of an entity the set declares: a value
    of the embedding is one, and a pattern that takes one apart is read off
    what it says its arguments are.
    """
    out = Vocab()
    out.args, out.ops = dict(self.args), self.ops
    out.types, out.ints, out.aliases = dict(self.types), self.ints, self.aliases
    for b in blocks:
      for p in b.entries():
        if isinstance(p, Program):
          out.args[p.name] = [sig_level(t) for t in p.sig.items]
        elif isinstance(p, Symbol) and p.decls.constructor is not None:
          macro = p.decls.constructor.macro.format(symbol=p.name)
          out.args[macro] = [level_of(t) if t else None for t in p.types]
          out.types[macro] = list(p.types)
    return out


def read_vocabulary(paths):
  """Read the vocabulary of the embedding out of the files that define it."""
  out = Vocab()
  for path in paths:
    for _doc, node in read_file(path):
      if node.kind != 'list' or len(node.items) < 2 \
              or node.items[0].kind != 'sym' or node.items[1].kind != 'sym' \
              or not node.items[1].val.startswith('$'):
        continue
      head, name = node.items[0].val, node.items[1].val
      if head == 'declare-const':
        out.args[name] = []
      elif head == 'program':
        # A program says what it takes in its signature rather than in the
        # parameters its cases are matched with.
        sig = next((node.items[i + 1] for i in range(2, len(node.items) - 1)
                    if node.items[i].kind == 'kw'
                    and node.items[i].val == ':signature'), None)
        if sig is not None and sig.kind == 'list':
          out.args[name] = [sig_level(t) for t in sig.items]
      elif head in ('define', 'declare-parameterized-const') \
              and len(node.items) > 2 and node.items[2].kind == 'list':
        # An implicit parameter is worked out rather than written.
        params = [p for p in node.items[2].items
                  if p.kind == 'list' and not any(
                      i.kind == 'kw' and i.val == ':implicit' for i in p.items)]
        out.args[name] = [level_of(p.items[1]) if len(p.items) > 1 else None
                          for p in params]
        out.types[name] = [p.items[1] if len(p.items) > 1 else None
                           for p in params]
        if head == 'define' and len(node.items) > 3:
          read_spelling(out, name, [p.items[0].val for p in params],
                        node.items[3])
  return out


def pattern_binds(node, declared, entry, ctx):
  """What a pattern binds, and what each name is declared as.

  A bare name matches anything and is of the type the place it stands at is
  declared with, which comes back as None since only the caller knows it;
  anything else is an application, and what it binds is read off the
  declaration of what it is applied to. Nothing states this twice: the
  embedding already says what $vsm_binary takes.
  """
  if node.kind == 'sym':
    if node.val.startswith('$'):
      # A constructor of the embedding that carries nothing, e.g. $vsm_true.
      # It matches itself, so nothing is bound and nothing is declared for it.
      return []
    return [(node.val, declared)]
  if node.kind != 'list' or not node.items or node.items[0].kind != 'sym':
    die('%s: a pattern is a name or an application, got %s'
        % (entry.name, node.raw[:40]))
  head = node.items[0].val
  types = ctx.vocab.types.get(head)
  if types is None:
    die('%s: %s declares nothing, so what a pattern of it binds cannot be read'
        % (entry.name, head))
  if len(types) != len(node.items) - 1:
    die('%s: %s takes %d argument%s, not %d'
        % (entry.name, head, len(types), '' if len(types) == 1 else 's',
           len(node.items) - 1))
  out = []
  for a, t in zip(node.items[1:], types):
    out.extend(pattern_binds(a, t, entry, ctx))
  return out


def read_spelling(out, name, params, body):
  """The other way the embedding spells what a name it defines stands for.

  A native is defined as the raw operator it applies, so that is the operator
  the configuration is to name it by, and a file which wrote the one and a file
  which writes the other are seen to say the same thing. A value the embedding
  names is the numeral of a native, which is what a whole number written where
  a value is wanted compiles to.
  """
  if body.kind != 'list' or len(body.items) < 1 \
          or body.items[0].kind != 'sym':
    return
  head, args = body.items[0].val, body.items[1:]
  if name.startswith('$native_') and head.startswith('$native_apply_') \
          and args and args[0].kind == 'str' \
          and [i.val for i in args[1:]] == params:
    op, n = args[0].val, len(params)
    out.ops[op] = name
    out.aliases.append(('($native_apply_%d "%s")' % (n, op), name) if not n
                       else ('($native_apply_%d "%s" ' % (n, op),
                             '(%s ' % name))
    # A whole number the embedding has a name for, e.g. $native_z_zero.
    if not n and op.isdigit():
      out.ints[('native', int(op))] = name
    return
  # A whole number of another level, e.g. $vsm_z_zero for ($vsm_numeral 0).
  for level, wrap in NUMERAL.items():
    if head == wrap and not params and len(args) == 1 \
            and args[0].kind == 'sym':
      for (lv, value), n in list(out.ints.items()):
        if lv == 'native' and n == args[0].val:
          out.ints[(level, value)] = name


def read_macros(paths):
  """Each constructor of the embedding and the macro that applies it.

  `(define $sm_apply ((x ..) (y ..)) ($emb_sm.Apply x y))` says that $sm_apply
  is how $emb_sm.Apply is written. The configuration names the macro, so this
  is what lets naming the constructor instead be caught and answered with the
  name to use.
  """
  out = {}
  for path in paths:
    for _doc, node in read_file(path):
      if node.kind != 'list' or len(node.items) != 4 \
              or not node.items[0].is_sym('define'):
        continue
      name, ps, body = node.items[1].val, node.items[2], node.items[3]
      if ps.kind != 'list':
        continue
      args = [p.items[0].val for p in ps.items if p.kind == 'list'
              and not any(i.kind == 'kw' and i.val == ':implicit'
                          for i in p.items)]
      if body.kind == 'sym' and body.val.startswith('$emb_') and not args:
        out[body.val] = name
      elif body.kind == 'list' and body.items \
              and body.items[0].kind == 'sym' \
              and body.items[0].val.startswith('$emb_') \
              and [i.val for i in body.items[1:]] == args:
        out[body.items[0].val] = name
  return out


def lean_clauses(blocks):
  """What each entry of a set says the generated Lean is to be told.

  One is the name of the program the clause is of, the prose written above the
  entry, and the clause itself as the Lean text it is. They come back in the
  order the set gives them, which is the order the file is written in.
  """
  out = []
  for b in blocks:
    for e in b.entries():
      if isinstance(e, Symbol) and e.has('lean'):
        out.append((e.name, [d[1:].strip() for d in e.doc], e.get('lean').val))
  return out


def counts(blocks):
  """How much of each thing a set holds, for a run to say what it compiled."""
  out = collections.Counter()
  for b in blocks:
    for e in b.entries():
      if not isinstance(e, Symbol):
        out['programs'] += 1
        continue
      out[e.decls.noun + 's'] += 1
      for a in ('exclude', 'lean'):
        if e.has(a):
          out[a] += 1
      if e.has('keep') or e.decls.keep:
        out['keep'] += 1
  return out


def defined_names(blocks):
  """Every name the text of a configuration set defines.

  This is what says a helper a symbol reaches for is one some file writes out,
  and what tells a symbol that a rule of its own stands above it.
  """
  out = set()
  for b in blocks:
    out.update(b.defines())
  return out


# -----------------------------------------------------------------------------
# Casting a term of the surface into the deep embedding
# -----------------------------------------------------------------------------

def cast(expr, scope, entry, ctx, level):
  """What a term of the surface means in the deep embedding.

  A bare name is one of the family the *level* is of: the symbol $sm_X of the
  SMT-LIB signature where a term is wanted, its evaluator $smtx_model_eval_X
  where a value is, the type constructor $tsm_X where a type is. A whole number
  is likewise read as the level it stands at. Everything else is the same
  wherever it stands: a `$`-name is used as itself and a name in quotes is a
  native.

  The level of an argument is read off the declaration of what it stands under,
  so a value applied to a value and a native applied to a native each read as
  what they are, and a place the declaration leaves open -- a branch of ite --
  is of the level around it.

  Beside those, eo::define binds a name over the rest. Nothing else is builtin:
  a bit-vector literal and the width of one are macros of the set that uses
  them, since a macro is what an idiom of a file is.
  """
  if expr.kind == 'pre':
    return expr.val
  if expr.kind == 'sym':
    v = expr.val
    stands = scope.stands_for(v, level, entry)
    if stands is not None:
      return stands
    if v in entry.params_declared:
      die('%s: %s is named but this case does not bind it'
          % (entry.name, v))
    if v.startswith('$'):
      return embedded(v, entry, ctx)
    return named(v, level, entry)
  if expr.kind == 'int':
    return ctx.vocab.numeral(expr.val, level, entry)
  if expr.kind == 'str':
    return apply_native(expr, expr.val, [], scope, entry, ctx, level)
  if expr.kind != 'list' or not expr.items:
    die('%s: a term is a name, a literal or an application' % entry.name)
  h = expr.items[0]
  if h.is_sym('eo::define'):
    return cast_define(expr, scope, entry, ctx, level)
  if h.kind == 'str':
    return apply_native(expr, h.val, expr.items[1:], scope, entry, ctx,
                        level)
  if h.kind != 'sym':
    die('%s: the head of an application is a name or a native' % entry.name)
  head = (embedded(h.val, entry, ctx) if h.val.startswith('$')
          else named(h.val, level, entry))
  return expr.laid_out([head] + [
      cast(a, scope, entry, ctx, ctx.vocab.arg_level(head, i, level))
      for i, a in enumerate(expr.items[1:])])


def numeral_wrap(native, level, entry):
  """A native whole number, as the vocabulary of a level writes one."""
  if level == 'native':
    return native
  if level not in NUMERAL:
    die('%s: a whole number is not a term of the %s vocabulary'
        % (entry.name, level))
  return '(%s %s)' % (NUMERAL[level], native)


def named(name, level, entry):
  """A bare name, i.e. one of the family the level it stands at is of."""
  if level not in FAMILY:
    die('%s: %s is neither bound here nor a name of the %s vocabulary, which '
        'has none of its own' % (entry.name, name, level))
  return FAMILY[level] + name


def apply_native(node, name, args, scope, entry, ctx, level):
  """A native, named in quotes.

  The embedding gives most of its natives a name of their own, and that name is
  the one the configuration writes; a native it names is applied through it,
  and which of its arguments are natives themselves is read off its
  declaration. Naming instead the *operator* it is defined as is answered with
  the name to use, the same way naming a constructor is.

  A native the embedding gives no name is the raw operator of the value layer,
  applied through $native_apply_N. Only a set that builds values may name one:
  the signature of an input builds terms, so a name it gives that the embedding
  does not have is a misspelling rather than an operator.
  """
  full = '$native_' + name
  if full in ctx.vocab:
    if ctx.vocab.arity(full) != len(args):
      die('%s: %s takes %d argument%s, not %d'
          % (entry.name, full, ctx.vocab.arity(full),
             '' if ctx.vocab.arity(full) == 1 else 's', len(args)))
    if not args:
      return full
    return node.laid_out([full] + [
        cast(a, scope, entry, ctx, ctx.vocab.arg_level(full, i, level))
        for i, a in enumerate(args)])
  if name in ctx.vocab.ops:
    die('%s: write "%s", the native, rather than the operator %s it is '
        'defined as' % (entry.name, ctx.vocab.ops[name][8:], name))
  if not ctx.raw_operators:
    die('%s: there is no native called %s' % (entry.name, full))
  # The raw operator of the value layer, which has no name of its own.
  return node.laid_out(['$native_apply_%d "%s"' % (len(args), name)]
                       + [cast(a, scope, entry, ctx, 'native')
                          for a in args]) \
      if args else '($native_apply_0 "%s")' % name


# The aggregates a set compiles its cases *into*. A file never names one: a
# name of the input stands for what it transforms into wherever the embedding
# is wanted, and an argument of an :eval-case stands for its value, both by the
# place they stand in. Naming one is a case reaching for the thing it is a part
# of, so it is answered with the reading to rely on instead.
AGGREGATES = {
    '$eo_to_smt': 'a name of the input stands for what it transforms into '
                  'wherever a term of the embedding is wanted',
    '$eo_to_smt_type': 'a name of the input stands for what it transforms into '
                       'wherever a type of the embedding is wanted',
    '$smtx_model_eval': 'an argument of an :eval-case stands for its value in '
                        'the model',
}


def embedded(name, entry, ctx):
  """A `$`-name as the configuration is to write it.

  A constructor of the embedding is written with the macro that applies it,
  which is how every hand-written program of the files spells it. Naming the
  constructor is answered with the name to use rather than passed through, and
  so is naming a native, which the configuration names in quotes, or an
  aggregate, which the place a name stands in already says.
  """
  if name in AGGREGATES:
    die('%s: %s is the aggregate this case is a part of, so no case names it: '
        '%s' % (entry.name, name, AGGREGATES[name]))
  if name.startswith('$emb_') and name in ctx.macros:
    die('%s: write %s, the macro of the embedding, rather than the '
        'constructor %s it applies' % (entry.name, ctx.macros[name], name))
  if name.startswith('$sm_'):
    die('%s: write %s, the symbol of the signature, rather than the macro %s '
        'that applies its constructor' % (entry.name, name[4:], name))
  if name.startswith('$native_'):
    die('%s: write "%s", the native, rather than the name %s it is defined '
        'under' % (entry.name, name[8:], name))
  if name.startswith('$smt_'):
    die('%s: write %s, the type of the embedding, rather than the name %s it '
        'is declared under' % (entry.name, 'Smt' + name[5:], name))
  if name.startswith('$tsm_'):
    # A bare name where a type is wanted is already the type constructor, so
    # nothing writes one out. A place that has no level -- under a native the
    # embedding gives no name of its own, applied through $native_apply_N --
    # would be the exception, and the answer there is to give that native a
    # name, the way $native_model_lookup is named in model_smt.eo.
    die('%s: write %s, the type constructor, rather than the macro %s that '
        'applies it' % (entry.name, name[5:], name))
  found = reserved_by(name, ctx.decls)
  if found is not None:
    # A name the compiler writes is named after the symbol it was written for,
    # and naming the symbol is how a body reaches it: writing the name out
    # instead reaches the same program by a name that says nothing of where it
    # came from, and would go on reaching it were the symbol to say its value
    # another way.
    die('%s: write %s, the symbol of the signature, rather than %s, %s'
        % (entry.name, name[len(found[0]):], name, found[1]))
  # A name that is not the embedding's is a helper of the set, so some file
  # of the set has to write it out; the compiler notes it here and Ctx.check
  # says at the end whether every one was.
  if name not in ctx.vocab:
    ctx.need(name, entry.name)
  return name


def declared_type(node, entry, ctx):
  """A type as a parameter list or a signature writes one.

  Three vocabularies meet here and each is named as it is named everywhere: a
  native in quotes, a type of the embedding without its `$smt_`, and a type of
  the *input* as the input writes it, which is what is left.
  """
  if node.kind == 'str':
    return apply_native(node, node.val, [], Scope(), entry, ctx, 'native')
  if node.kind == 'sym':
    smt = smt_type(node.val)
    if smt is not None:
      if smt not in ctx.vocab:
        die('%s: there is no type of the embedding called %s'
            % (entry.name, node.val))
      return smt
    if node.val.startswith('$'):
      return embedded(node.val, entry, ctx)
    return node.raw
  if node.kind == 'list':
    return node.laid_out([declared_type(i, entry, ctx) for i in node.items])
  return node.raw


def cast_define(expr, scope, entry, ctx, level):
  """An eo::define, which binds one name over the rest of the body.

  What it binds is already of the embedding, so the name stands for itself
  wherever the body names it. A program declares such a name, which is what
  :params is for where the name is not the result's own T.
  """
  if len(expr.items) != 3 or expr.items[1].kind != 'list' \
          or len(expr.items[1].items) != 1:
    die('%s: an eo::define binds one name, written (eo::define ((v e)) body)'
        % entry.name)
  b = expr.items[1].items[0]
  if b.kind != 'list' or len(b.items) != 2:
    die('%s: an eo::define binding is written (v e)' % entry.name)
  name, body = b.items[0].val, expr.items[2]
  # A name an eo::define binds is of the level the body reads it at, which is
  # what says what it has to be; where the body reads it at none of its own it
  # is of the level around it. :params is for a name a *pattern* binds, which
  # has no use to read it off.
  inner = scope.binding(name, afresh=True)
  text = cast(body, inner, entry, ctx, level)
  at = entry.bound_levels.get(name) or inner.level_of_use(name) or level
  value = cast(b.items[1], scope, entry, ctx, at)
  if inlined(value, body, name):
    return cast(body, scope.standing(name, value), entry, ctx, level)
  return '(eo::define ((%s %s)) %s)' % (name, value, text)


def inlined(value, body, name):
  """Whether a binding is written where it stands rather than bound.

  A binding is there to say a thing once and read it back, so one that names
  something already atomic, or that the body reads back at most once, is only a
  name for a name. The term is the same either way, since what an eo::define
  binds is a term and nothing else.
  """
  return '(' not in value or occurrences(body, name) <= 1


def occurrences(node, name):
  """How often a body names something."""
  if node.kind == 'sym':
    return 1 if node.val == name else 0
  return sum(occurrences(i, name) for i in node.items)

# -----------------------------------------------------------------------------
# Entries
# -----------------------------------------------------------------------------

class Entry:
  """What a body is cast against.

  Casting reports against `name`, answers a name the case does not bind against
  `params_declared`, and reads the level of a name an eo::define binds off
  `bound_levels`. Every kind of entry gives those three, however it is written,
  and this is where that is said.
  """

  # A name the entry declares the type of, and so the vocabulary an eo::define
  # binding it is written in. An entry that declares none leaves it to the
  # level around the binding.
  bound_levels = {}
  params_declared = frozenset()
  attrs = {}
  # What the block it opens is called, which is its own name unless the kind
  # it is of says otherwise.
  block_name = None
  # The comment written above the entry, which read_config puts there.
  doc = ()

  def has(self, a):
    return a in self.attrs

  def get(self, a, default=None):
    return self.attrs.get(a, default)

def parse_attrs(node, start, name, path, known, expand, macros,
                repeated=None):
  """The `:key value` pairs an entry ends with.

  `known` maps each attribute to how many values follow it, which may be a
  number or, where an attribute takes an optional one, what reads the rest and
  says. An attribute of no values is a flag and comes back as True. One named
  in `expand` has the macros of its file rewritten out of it before anything
  else sees it, and one named in `repeated` comes back as
  the list of what each occurrence gave; every attribute that gives a case is
  one, since each occurrence adds a case.
  """
  repeated = expand if repeated is None else repeated
  attrs, it, i = {}, node.items, start
  while i < len(it):
    k = it[i]
    if k.kind != 'kw':
      die('%s: %s: expected an attribute, got %s' % (path, name, k.raw))
    key = k.val[1:]
    if key not in known:
      die('%s: %s: unknown attribute :%s' % (path, name, key))
    arity = known[key]
    if callable(arity):
      arity = arity(it[i + 1:])
    if i + arity >= len(it):
      die('%s: %s: :%s takes %d value%s'
          % (path, name, key, arity, '' if arity == 1 else 's'))
    vals = it[i + 1:i + 1 + arity]
    if key in expand:
      vals = [expand_macros(v, macros, name) for v in vals]
    # An attribute of no values is a flag, and says what it says by being there.
    val = True if not arity else vals[0] if arity == 1 else vals
    if key in repeated:
      attrs.setdefault(key, []).append(val)
    elif key in attrs:
      die('%s: %s: :%s is given twice' % (path, name, key))
    else:
      attrs[key] = val
    i += 1 + arity
  return attrs


def expand_macros(node, macros, where):
  """Rewrite every application of a macro, innermost first.

  A macro of no arguments stands for its body wherever its name stands, since
  there is no application to recognise it by: `emb.not_value` is a name for a
  value, not for a call.
  """
  if node.kind == 'sym' and node.val in macros and not macros[node.val][0]:
    return macros[node.val][1]
  if node.kind != 'list' or not node.items:
    return node
  items = [expand_macros(i, macros, where) for i in node.items]
  h = items[0]
  if h.kind == 'sym' and h.val in macros:
    params, body = macros[h.val]
    if len(params) != len(items) - 1:
      die('%s: the macro %s takes %d arguments' % (where, h.val, len(params)))
    return substitute(body, dict(zip(params, items[1:])))
  # Rewriting a form leaves the whitespace it was written with, so what a
  # macro is expanded in still comes out laid out as it was written.
  return relaid(node, items)


def relaid(node, items):
  """A list rebuilt from new items, with the text it is written as.

  A place read as the source it is -- a pattern at a place of the *input*, and
  what such a pattern binds -- goes on `raw`, so a form whose items were
  rewritten has to carry the text of what it now says rather than of what it
  said before.
  """
  parts = [i.raw if i.raw != '' else str(i.val) for i in items]
  return Node('list', items=items, raw=node.laid_out(parts),
                        gaps=node.gaps, tail=node.tail)


def substitute(node, env):
  if node.kind == 'sym' and node.val in env:
    return env[node.val]
  if node.kind != 'list':
    return node
  return relaid(node, [substitute(i, env) for i in node.items])


# -----------------------------------------------------------------------------
# A program of the embedding
# -----------------------------------------------------------------------------

class Program(Entry):
  """One program of the embedding, i.e. a block a symbol's cases name.

  It is written as a definitions file writes one, `(program NAME (param...)
  :signature (T...) R (case...))`, and what it compiles to is that form with
  the *terms of its cases* cast: a symbol of the theory put where $sm_X was, a
  native where $native_X was. Everything else -- the parameters, the signature,
  the whitespace, a comment between two cases -- comes out as it was written.

  Its parameters stand for themselves, being of the embedding already, which is
  what makes a case of it read like the term it is.
  """

  # A program belongs to no symbol, so it belongs to the block it stands in.
  joins_open_block = True

  def __init__(self, node, params, sig, ret, cases, keep=False):
    self.node = node
    self.name = node.items[1].val
    # Whether the block it stands in is taken whatever the input declares. A
    # program is otherwise taken only where a block already taken names it,
    # which is right for a helper of a symbol and wrong for one the *template*
    # names, see $EO_TO_SMT_AUX$ in plugins/model_smt/model_smt.eo.
    self.keep = keep
    self.params = params        # what each parameter is called
    self.sig = sig              # the type of each argument, as written
    self.ret = ret              # the type of the result, as written
    self.cases = cases          # what it does, case by case
    self.doc = []               # the comment above it, which is its own
    self.params_declared = set(params)
    self.bound_levels = {p.items[0].val: level_of(p.items[1])
                         for p in node.items[2].items
                         if p.kind == 'list' and len(p.items) > 1}

  def defines(self):
    return {self.name}

  def case(self, case, ctx):
    """One case, i.e. the application it matches and what that returns."""
    if case.kind != 'list' or len(case.items) != 2:
      die('%s: a case is written (<application> <return>)' % self.name)
    args, ret = case.items
    if args.kind != 'list' or not args.items \
            or not args.items[0].is_sym(self.name):
      die('%s: a case matches an application of the program, so it is written '
          '((%s <argument>...) <return>)' % (self.name, self.name))
    given = args.items[1:]
    if len(given) != len(self.sig.items):
      die('%s: a case takes %d argument%s, not %d'
          % (self.name, len(self.sig.items),
             '' if len(self.sig.items) == 1 else 's', len(given)))
    # The signature is what says how a case is read: each place is of the
    # vocabulary its declared type names, and a place whose type is one of the
    # input is taken as the input wrote it -- so what such a place *matches* is
    # of the input too, and is transformed where a term of the embedding is
    # wanted.
    scope = Scope(bound=self.params_declared, into=ctx.decls.transform_into())
    parts = []
    for a, lv in zip(given, [level_of(t) for t in self.sig.items]):
      if lv:
        parts.append(cast(a, scope, self, ctx, lv))
      else:
        parts.append(a.raw)
        scope = scope.names_of(a, self.params_declared)
    lv = level_of(self.ret)
    body = cast(ret, scope, self, ctx, lv) if lv else ret.raw
    return case.laid_out([args.laid_out([self.name] + parts), body])

  def render(self, ctx):
    parts = ['program', self.name, declared_type(self.node.items[2], self, ctx),
             ':signature', declared_type(self.sig, self, ctx),
             declared_type(self.ret, self, ctx),
             self.cases.laid_out([self.case(c, ctx)
                                  for c in self.cases.items])]
    out = list(self.doc)
    if self.keep:
      # The same directive a symbol of the embedding writes, see
      # DefsBlock::d_keep: the stage reads it and takes the block whatever the
      # input declares.
      out.append('(echo "eoc-keep symbol %s")' % self.name)
    return '\n'.join(out + [self.node.laid_out(parts)])


def parse_program(node, path, macros):
  it = node.items
  # :keep may stand between the parameters and the signature, and says the
  # block is taken whatever the input declares.
  keep = len(it) > 3 and it[3].kind == 'kw' and it[3].val == ':keep'
  if keep:
    it = it[:3] + it[4:]
  if len(it) < 7 or it[2].kind != 'list' or it[3].kind != 'kw' \
          or it[3].val != ':signature' or it[4].kind != 'list':
    die('%s: a program is written (program NAME (param...) [:keep] '
        ':signature (T...) R (case...))' % path)
  params = [p.items[0].val for p in it[2].items
            if p.kind == 'list' and p.items]
  if len(it) < 7 or it[6].kind != 'list':
    die('%s: %s: a program says what it does, case by case, as a list'
        % (path, it[1].val))
  # A macro is an idiom the bodies of a file would otherwise repeat, and the
  # cases of a program are bodies like any other.
  cases = expand_macros(it[6], macros, it[1].val)
  return Program(node, params, it[4], it[5], cases, keep)


# A program belongs to no symbol and is an entry of either set. It is written
# the way a definitions file writes one, since that is what it compiles to.
PROGRAM_ENTRY = {'program': parse_program}


# -----------------------------------------------------------------------------
# One symbol of a set
# -----------------------------------------------------------------------------

# How an argument is written, and so how it reaches a case. A name on its own
# is of the kind the aggregate reads by default; one annotated the way SMT-LIB
# annotates a term, `(! v :type)`, says the argument is a type rather than a
# term, and `(! v :raw)` that it reaches a case as it was written.
KINDS = (':raw', ':type')
PLAIN = 'plain'

# What a symbol says of an aggregate it contributes nothing to, so that no case
# and no program is written for it. A symbol that says nothing at all would
# take the aggregate's default instead, which is what this is for.
NOTHING = 'none'


class Symbol(Entry):
  """One symbol of a set: its arguments, and one case per aggregate."""

  def __init__(self, name, params, kinds, types, attrs, decls):
    # What the symbol is called: its own name, unless :overload says it is
    # written under another, as an overload the desugar stage named is.
    self.name = attrs['overload'].val if 'overload' in attrs else name
    self.params = params
    self.kinds = kinds
    # The type each parameter says it is of, where its kind does not say.
    self.types = types
    self.block_name = decls.block.format(symbol=self.name)
    self.attrs = attrs
    self.decls = decls
    self.params_declared = set(params)

  def cases_of(self, key):
    """What one attribute gave, each as (what it matches, what it returns)."""
    return [(v[0], v[1]) if isinstance(v, list) else (None, v)
            for v in self.get(key, ())]

  def says_nothing(self, key):
    """Whether the symbol said it contributes nothing to this aggregate."""
    cases = self.cases_of(key)
    return (len(cases) == 1 and cases[0][0] is None
            and cases[0][1].kind == 'sym' and cases[0][1].val == NOTHING)

  def defines(self):
    out = set()
    c = self.decls.constructor
    if c is not None:
      out.add(c.name.format(symbol=self.name))
      out.add(c.macro.format(symbol=self.name))
    for key, agg in self.decls.aggregates.items():
      if self.says_nothing(key):
        continue
      if self.has(key) or self._defaulted(key):
        out.add(agg.program_of(self))
      if agg.helper is not None and self.has(agg.helper_attr):
        out.add(agg.helper_of(self))
    return out

  def _defaulted(self, key):
    """Whether an aggregate this symbol says nothing about still takes a case.

    The one it does is the aggregate a symbol contributes to by being one, i.e.
    the primary; a symbol that contributes to a sole aggregate contributes to
    that one alone.
    """
    agg = self.decls.aggregates[key]
    if self.has(key) or agg.default is None:
      return False
    if agg.primary:
      return not any(self.has(k) for k, a in self.decls.aggregates.items()
                     if a.sole)
    return self.has(agg.helper_attr) if agg.helper is not None else False

  def slots(self, agg, ctx):
    """What a case of this aggregate calls each of the arguments.

    A parameter that says the type it is of is called after that type, since
    the program the cases are spliced into declares each name once and two
    types cannot share one: a value built over a native integer and one built
    over a map stand in the same place and are not the same thing.
    """
    return [agg.slot(i, kind, declared_type(t, self, ctx) if t else None)
            for i, (kind, t) in enumerate(zip(self.kinds, self.types))]

  # -- what it compiles to ----------------------------------------------------

  def render(self, ctx):
    if self.has('exclude'):
      # The compilation has no place for this one, so instead of a model it
      # says so: the desugar stage reads a directive of the generated file and
      # drops what it names, whether that is a symbol, a method or a rule.
      return '(echo "eoc-exclude %s %s")' % (self.decls.noun, self.name)
    out = []
    if self.has('keep') or self.decls.keep:
      # The entry is the embedding's own, so its block stands whether or not
      # the input declares it: the stage reads the directive, see
      # DefsBlock::d_keep, the way the desugar stage reads an exclusion. A
      # kind of entity may be the embedding's own throughout, as its types
      # are, and then every entry of it says this without writing it.
      out.append('(echo "eoc-keep symbol %s")' % self.name)
    if self.decls.constructor is not None:
      out.extend(self.decls.constructor.render(self, ctx))
    for key in self.decls.order:
      agg = self.decls.aggregates[key]
      if agg.helper is not None and self.has(agg.helper_attr):
        out.append(self._helper(agg, ctx))
    for key in self.decls.order:
      agg = self.decls.aggregates[key]
      if self.says_nothing(key):
        continue
      if self.has(key):
        out.append(self._case(agg, ctx))
      elif self._defaulted(key):
        out.append(self._default(agg, ctx))
    if not out:
      # What it says may reach a file other than the definitions one, as the
      # Lean text of a method does; what says nothing at all is an error.
      if self.has('lean'):
        return ''
      die('%s: says nothing, so nothing is written for it' % self.name)
    return '\n'.join(out)

  # -- a case of an aggregate -------------------------------------------------

  def _case(self, agg, ctx):
    """The per-symbol program of one aggregate, from the cases the entry gave.

    A case that gives no pattern matches the symbol applied to its arguments
    and is written with the names the entry gives them; one that gives a
    pattern binds what that pattern matches, and the program declares one
    parameter per name the pattern bound, in the order it bound them.
    """
    cases, width = [], 0
    for pat, term in self.cases_of(agg.key):
      if pat is None:
        xs = self.slots(agg, ctx)
        head = agg.head(self, xs)
      else:
        places = _places(pat, self, agg)
        xs = [places.get(p) for p in self.params]
        level = MATCH_LEVEL.get(agg.matches)
        if level is None:
          # The subject is of the input, so the pattern is taken as the input
          # wrote it, with the parameters of the program put for the names the
          # entry gave them.
          head = TOKEN.sub(lambda m: places.get(m.group(0), m.group(0)),
                           pat.raw)
        else:
          # The subject is of the embedding, so the pattern is cast the way a
          # body at that level is -- a bare name is one of the family that
          # level is of -- with what it binds standing for the parameters.
          head = cast(pat, Scope(dict(places)), self, ctx, level)
      width = max(width, len([x for x in xs if x is not None]))
      env, surface = agg.scope(self, xs)
      if agg.level == 'input':
        # A body of the input is not cast at all: the vocabulary it is written
        # in is the input's own, so what it says reaches the case as it stands,
        # with the names the entry gave put for the ones the program declares.
        rhs = TOKEN.sub(lambda m: env.get(m.group(0), m.group(0)), term.raw)
      else:
        # What a case is given beside the term -- the model of an evaluation,
        # the type a transformation is of -- stands for itself.
        bound = [v for v, _ in agg.context] + [v for v, _ in agg.own]
        rhs = cast(term, Scope(env, bound=bound, surface=surface,
                               into=ctx.decls.transform_into()),
                   self, ctx, agg.level)
      cases.append((head, rhs))
    return agg.render(self, cases, ctx, width)

  def _default(self, agg, ctx):
    """The case of an aggregate a symbol that says nothing about it takes."""
    n = len(self.params)
    xs = self.slots(agg, ctx)
    env, surface = agg.scope(self, xs)
    # A name of the input reaches the default the way it reaches a case: as
    # itself where the input is wanted, transformed where the embedding is.
    into = ctx.decls.transform_into()
    stands = [into[agg.level] % env[v]
              if v in surface and agg.level in into else env[v]
              for v in self.params]
    rhs = applied(agg.default + self.name, stands)
    return agg.render(self, [(agg.head(self, xs), rhs)], ctx, n)

  # -- the program written over what the arguments evaluate to ----------------

  def _helper(self, agg, ctx):
    """The program a case hands its work to, i.e. one written over values.

    Its cases are ordinary cases: what they match is one pattern per argument,
    and what a pattern binds is read off the declaration of what it is applied
    to, so the program declares each name without the entry saying its type.
    """
    cases, params, total = [], [], False
    for pats, body in self.cases_of(agg.helper_attr):
      if pats is None:
        die('%s: :%s says what it matches -- one pattern per argument -- '
            'before what it gives' % (self.name, agg.helper_attr))
      if pats.kind != 'list' or len(pats.items) != len(self.params):
        die('%s: :%s says %s pattern%s for %d argument%s'
            % (self.name, agg.helper_attr,
               len(pats.items) if pats.kind == 'list' else 'no',
               '' if pats.kind == 'list' and len(pats.items) == 1 else 's',
               len(self.params), '' if len(self.params) == 1 else 's'))
      bound = []
      for p in pats.items:
        bound.extend(pattern_binds(p, None, self, ctx))
      names = [v for v, _ in bound]
      # A type read off the embedding's own declaration is already of the
      # embedding and is written as it stands; a name that matched anything is
      # of the type the aggregate says each argument is, which the set wrote.
      arg = agg.helper_arg
      params.extend('(%s %s)' % (v, arg if t is None
                                 else declared_type(t, self, ctx))
                    for v, t in bound)
      # A case matching nothing but names it binds leaves nothing over, so the
      # one for what is left could never be reached. A constructor that carries
      # nothing is a name too, and matches only itself, so it leaves the rest.
      total = total or all(p.kind == 'sym' and not p.val.startswith('$')
                           for p in pats.items)
      cases.append((' '.join(cast(p, Scope(bound=names), self, ctx, 'value')
                             for p in pats.items),
                    cast(body, Scope(bound=names), self, ctx, agg.level)))
    return agg.render_helper(self, cases, params, ctx, len(self.params), total)


# -- reading one --------------------------------------------------------------


def _places(pat, entry, agg):
  """What each name a pattern binds is called in the program it compiles to.

  The parameters are scoped to the case: a case binds what its own pattern
  matches, and the program declares one per name, so the name that appears
  first is the first parameter whatever the entry calls it. A name keeps the
  kind its declaration gave it, which is what says what the program declares
  its parameter as where the aggregate tells its arguments apart by kind, the
  way the width of a bit-vector is told from a type.
  """
  order = []
  for tok in TOKEN.findall(pat.raw):
    if tok in entry.params_declared and tok not in order:
      order.append(tok)
  kinds = [entry.kinds[entry.params.index(n)] for n in order]
  if ((agg.slots or isinstance(agg.declares, dict))
          and kinds != list(entry.kinds[:len(order)])):
    # The program declares its parameters by the kinds of the first arguments,
    # see Aggregate.params, so a pattern whose bound names are of any other
    # kinds would declare one thing and match another.
    die('%s: the pattern binds %s, whose kinds are not those of the first '
        '%d argument%s of %s; bind the arguments in the order they are '
        'declared' % (entry.name, ', '.join(order), len(order),
                      '' if len(order) == 1 else 's', entry.name))
  return {n: agg.slot(i, k) for i, (n, k) in enumerate(zip(order, kinds))}


def parse_params(node, name, path):
  """The parameters of an entity, i.e. what its cases are written with.

  A parameter is a name, a name marked with the kind it reaches a case as, or
  a name with the type it is of -- written the way a program's parameter list
  writes one, since it is the same thing. A kind of entity whose arguments are
  not all of one type says the type of each: what a value of the embedding is
  built over is a native of one sort or another.
  """
  if node.kind != 'list':
    die('%s: %s: the parameters of an entity are a list of names'
        % (path, name))
  names, kinds, types = [], [], []
  for a in node.items:
    if a.kind == 'sym':
      names.append(a.val)
      kinds.append(PLAIN)
      types.append(None)
    elif (a.kind == 'list' and len(a.items) == 3 and a.items[0].is_sym('!')
          and a.items[2].val in KINDS):
      names.append(a.items[1].val)
      kinds.append(a.items[2].val[1:])
      types.append(None)
    elif (a.kind == 'list' and len(a.items) == 2
          and a.items[0].kind == 'sym' and not a.items[0].is_sym('!')):
      names.append(a.items[0].val)
      kinds.append(PLAIN)
      types.append(a.items[1])
    else:
      die('%s: %s: a parameter is written `v`, `(! v :raw)` or `(v T)`, '
          'got %s' % (path, name, a.raw))
  if len(set(names)) != len(names):
    die('%s: %s: a parameter is named twice' % (path, name))
  return names, kinds, types


def parser(decls):
  """What reads an entity of the kind these declarations describe."""
  known = decls.attrs()
  # :overload, :exclude, :keep, :lean, :lean-impl and :needs give no case, so
  # none is a term to expand macros in; the last three are Lean text and the
  # scope it wants, neither of them a term at all.
  expanded = frozenset(k for k in known
                       if k not in ('overload', 'exclude', 'keep', 'lean',
                                    'lean-impl', 'needs'))

  def read(node, path, macros):
    # An entity that writes nothing of its own names no arguments: what is
    # said about a method or a proof rule is said about the whole of it.
    start = 3 if decls.params else 2
    if len(node.items) < start:
      die('%s: a %s is written (%s NAME %s...)'
          % (path, decls.noun, decls.keyword,
             '(param...) ' if decls.params else ''))
    name = node.items[1].val
    params, kinds, types = (parse_params(node.items[2], name, path)
                            if decls.params else ([], [], []))
    attrs = parse_attrs(node, start, name, path, known, expanded, macros)
    return Symbol(name, params, kinds, types, attrs, decls)
  return read
