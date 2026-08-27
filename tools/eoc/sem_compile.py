#!/usr/bin/env python3
"""Compiles the configuration sets under semantics into the
signatures written directly in the deep embedding, i.e.

  semantics/smt.eos  ->  tools/eoc/out/smt_defs.eo
                      what each SMT-LIB symbol means to the model
  semantics/development-cpc.eos  ->  tools/eoc/out/user_defs.eo
                      how each symbol of the input transforms into the
                      SMT-LIB one

Each set has a central file, the one named above, which declares the shape of
what the set compiles to -- its aggregates, its constructor and its shapes, see
sem_decl.py -- and then says what it compiles to and which files it is made of.
Nothing else is read while a set is compiled, so a form belongs to one
signature by the set it stands in and by nothing else.

What is left here is the reading of s-expressions, the four levels and the
naming conventions of the embedding; everything about what a set compiles to is
said by the set. The language the sets are written in is documented in full in
semantics/README.md.

  usage: sem_compile.py [--out-dir DIR] [--check] [-v] [CONFIG...]

The eoc pipeline runs this before the model-smt stage, see
compile_signatures in tools/eoc/driver.py, so the generated files are current
whenever that stage reads them. A file is written only when its text changes,
so a run with nothing to do leaves the tree alone.

With --check the generated text is compared against what is checked in, block
by block, which is what says the configuration still means what the embedding
did.
"""

import argparse
import collections
import itertools
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import sem_target  # noqa: E402
from sem_lang import (counts, defined_names, die,  # noqa: E402
                      lean_clauses, read_config, read_macros, read_text,
                      read_vocabulary, write_text)

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SEM = os.path.join(HERE, 'semantics')

# Where the two signatures the model-smt stage reads are written. Neither is
# said by a configuration: the SMT-LIB one is the target of the compilation and
# so is fixed, and the stage reads one signature of the input whichever input a
# run compiles, so there is one file for that too.
OUT = os.path.join(HERE, 'out')
SMT_TARGET = os.path.join(OUT, 'smt_defs.eo')
INPUT_TARGET = os.path.join(OUT, 'user_defs.eo')
# Where what a set says the generated Lean is to be told is written. The
# lean-meta stage reads the first for itself, since the programs of the deep
# embedding are compiled through whichever the input is, and is given the
# second with --lean-config.
SMT_LEAN_TARGET = os.path.join(OUT, 'smt_termination.lean')
INPUT_LEAN_TARGET = os.path.join(OUT, 'user_termination.lean')
# The set that is the SMT-LIB signature, which is the one that is the target.
SMT_SET = 'smt'

# The file each set stands in. A set is one file: it holds its theories in the
# order their blocks are emitted, one to a section.
CONFIGS = (os.path.join(SEM, 'smt.eos'), os.path.join(SEM, 'development-cpc.eos'))

# Where the vocabulary of the embedding is defined. A file of the configuration
# names a native in quotes and a type of the embedding without its $smt_, and
# the compiler puts the name back, so this is what says one exists, what it
# takes, and what each of its places is of.
VOCAB_FILES = (os.path.join(ROOT, 'plugins', 'desugar', 'native_embed.eo'),
               os.path.join(ROOT, 'plugins', 'desugar', 'eo_desugar.eo'),
               os.path.join(ROOT, 'plugins', 'model_smt', 'model_smt.eo'))

# Where the constructors of the embedding are declared together with the macros
# that apply them. A file of the configuration writes the macro, so this is
# what lets writing the constructor instead be answered with the name to use.
MACRO_FILES = (os.path.join(ROOT, 'plugins', 'model_smt', 'model_smt.eo'),)

GENERATED = """\
; GENERATED FILE -- do not edit.
;
; Compiled from %s by tools/eoc/sem_compile.py,
; which is where a symbol is to be changed or added. The eoc pipeline runs it
; before the model-smt stage, so this file is current whenever that stage reads
; it; to run it by hand:
;
;   python3 tools/eoc/sem_compile.py            to write this file
;   python3 tools/eoc/sem_compile.py --check    to compare it with the surface
;
"""


LEAN_GENERATED = """\
-- GENERATED FILE -- do not edit.
--
-- Compiled from %s by tools/eoc/sem_compile.py,
-- which is where a clause is to be changed or added: it is what a method of
-- that set says under :lean. The eoc pipeline runs the compiler before the
-- lean-meta stage, so this file is current whenever that stage reads it.
--
-- Lean has to be told why a recursive definition terminates whenever it cannot
-- see this for itself, and no measure a compiler could guess would do for the
-- programs below. So the clause is said as the Lean text it is, and the
-- lean-meta plugin appends it verbatim to the definition of the program named,
-- see LeanMetaReduce::readTerminationClauses.
--
-- A block runs from a line naming one or more programs, written `-- $name ...`,
-- to the next comment line. Naming several programs in one block gives them
-- all the same clause; prose may be written between blocks, since a clause is
-- Lean text and holds no comment of its own.
--
%s"""

# What each of the two Lean files is for, which is what the set it comes from
# is: the programs of the deep embedding are compiled through whichever the
# input is, so the stage reads that file for itself and is given the other.
# Written as it is to be read, since text a run wraps for itself is text a run
# could wrap differently.
LEAN_WHICH = {
    SMT_SET: """\
-- This file is for the programs of the deep embedding, which every input is
-- compiled through. A program of an input signature is named in a file of its
-- own, which the compiler is given with --lean-config.""",
    None: """\
-- This file is for the programs of one input signature, and is what
-- --lean-config names. The programs of the deep embedding are in
-- tools/eoc/out/smt_termination.lean.""",
}


def render_lean(config):
  """What a set says the generated Lean is to be told, as the file the
  lean-meta stage reads.

  Methods that stand together and say the same thing come out under one
  heading, which is what naming several programs in one is for: the four
  helpers regular expression inclusion descends through share a measure.
  """
  out = [LEAN_GENERATED % (named(config.path),
                          LEAN_WHICH[SMT_SET if config.is_target else None])]
  blocks = []
  for name, doc, text in config.clauses:
    if blocks and not doc and blocks[-1][1] == text:
      blocks[-1][0].append(name)
    else:
      blocks.append(([name], text, doc))
  for names, text, doc in blocks:
    if doc:
      out.append('\n'.join(('-- ' + d).rstrip() for d in doc))
    out.append('-- %s\n%s' % (' '.join(names), text))
  # A blank line between blocks, which is what ends one for the stage that
  # reads them and what a paragraph of prose stands apart by.
  return '\n\n'.join(out) + '\n'


def summary(config):
  """How much of each thing a set holds, in the words of its kinds."""
  c = config.counts
  # The kinds a set holds, in the order its shape gives them, and last the
  # programs, which are what a set holds beside its entities.
  nouns = [shape.noun + 's' for shape in config.decls.shapes] + ['programs']
  kinds = ['%d %s' % (c[k], k if c[k] != 1 else k[:-1])
           for k in nouns if c[k]]
  said = ['%d %s' % (c[k], w) for k, w in (('keep', 'kept'),
                                           ('exclude', 'left out'),
                                           ('lean', 'annotated')) if c[k]]
  return ', '.join(kinds) + ('; ' + ', '.join(said) if said else '')


def named(path):
  """A path as a generated file names one, i.e. from the root and with the one
  separator, whatever the machine underneath spells one with."""
  return os.path.relpath(path, ROOT).replace(os.sep, '/')


def header(config):
  """What the generated file says for itself: how it came about, and then what
  the central file of its set says about the set."""
  rel = named(config.path)
  return GENERATED % rel + ''.join(l + '\n' for l in config.doc)


class Ctx:
  """What one configuration set knows while its blocks are rendered.

  A symbol never says which helper it reaches for: the compiler notes what a
  block came to name and then checks that some file of the same set writes it
  out, which is what keeps the two halves from leaning on each other silently.
  """

  def __init__(self, written, what, vocab, macros, decls):
    self.written = written
    self.what = what
    self.vocab = vocab
    self.macros = macros
    self.decls = decls
    # Whether a name in quotes the embedding does not have is an operator of
    # the value layer or a misspelling, which is read off whether the set has a
    # value layer at all. See Decls.raw_operators.
    self.raw_operators = decls.raw_operators
    self.missing = []

  def need(self, name, who, why='names'):
    if name not in self.written:
      self.missing.append('%s: %s %s, which no file of %s writes out'
                          % (who, why, name, self.what))

  def check(self):
    if self.missing:
      die('\n            '.join(self.missing))


class Config:
  """One set: the file it stands in, and the shape of what it writes."""

  def __init__(self, path, decls, files, doc):
    self.path = path
    self.decls = decls          # the shape of what it writes
    self.files = files          # the file it stands in
    self.doc = doc              # what the central file says about the set
    # What compiling it came to beside its blocks: what its methods say the
    # generated Lean is to be told, and how much of each thing it holds.
    self.clauses = []
    self.counts = {}

  @property
  def name(self):
    return name_of(self.path)

  @property
  def is_target(self):
    """Whether the set is the SMT-LIB signature, which is the target of the
    compilation, rather than the signature of an input.

    Which one a set is is said by what it is called, since the two compile to
    different things and a run has to know which before it reads a line.
    """
    return self.name == SMT_SET

  def _beside(self, target):
    """Where one of the files it compiles to is written.

    The sets the tool ships with compile into tools/eoc/out, which is where the
    stages read them from and which nothing checks in: what is kept is the
    configuration. Any other set compiles *beside itself*, since where it
    stands is the only place the tool knows of, so one that lives in another
    tree writes what it compiles to into that tree.
    """
    if any(same_file(self.path, c) for c in CONFIGS):
      return target
    return os.path.join(os.path.dirname(self.path), os.path.basename(target))

  @property
  def target(self):
    """The signature in the deep embedding it compiles to."""
    return self._beside(SMT_TARGET if self.is_target else INPUT_TARGET)

  @property
  def lean_target(self):
    """Where what its methods say the generated Lean is to be told is written,
    on the same terms."""
    return self._beside(
        SMT_LEAN_TARGET if self.is_target else INPUT_LEAN_TARGET)


def same_file(a, b):
  """Whether two paths name one file, which neither has to exist to answer:
  a set is compared with the ones the tool ships with before anything is
  written."""
  return os.path.realpath(a) == os.path.realpath(b)


def name_of(path):
  """The set a file is of, which is what it is called."""
  return os.path.splitext(os.path.basename(path))[0]


def read_config_file(path):
  """Read the file a set stands in.

  A set is one file. What it compiles to is fixed by the tool, see
  Config.target, and so is the shape of what it writes, see sem_target.py, so
  the file holds nothing but the theories themselves.
  """
  # The heading of the file, which is what the generated file says about
  # itself: the two describe the same signature.
  doc = list(itertools.takewhile(lambda l: l.startswith(';'),
                                 read_text(path).split('\n')))
  return Config(path, sem_target.of(name_of(path) == SMT_SET), [path], doc)


def is_config(path):
  """True if the file is a set rather than a signature written out.

  What tells them apart is that a set says what its symbols mean, which a
  signature written out never does: it is written in the embedding throughout.
  """
  try:
    return any(line.startswith('(define-symbol ')
               for line in read_text(path).split('\n'))
  except OSError:
    return False


def compile_config(config, vocab, macros):
  """Render every block one set holds, in the order its files give them.

  A block whose whole of what it says reaches another file is no block of this
  one and is left out, which a method that only says :lean is.
  """
  blocks = read_config(config.files, config.decls)
  ctx = Ctx(defined_names(blocks), 'semantics/' + config.name,
            vocab.extended(blocks), macros, config.decls)
  out = [(b.name, t) for b, t in ((b, b.render(ctx)) for b in blocks) if t]
  ctx.check()
  config.clauses = lean_clauses(blocks)
  config.counts = counts(blocks)
  return out


def target_blocks(paths):
  """The blocks of the set that is the target, for the vocabulary of the rest.

  An input is compiled *through* the target, so a symbol the target declares is
  one an input may name -- the bit-vector literal is, and so is each binder --
  and what each place of that symbol is of is what says how an argument written
  there is transformed. Reading the target is what puts that in reach; without
  it an argument falls back to the level around it, and a native written under
  a symbol that takes one comes out wrapped as a term.

  The target is read whether or not this run compiles it, since an input set
  compiled on its own is written against it just the same.
  """
  path = next((p for p in paths if name_of(p) == SMT_SET),
              next((c for c in CONFIGS if name_of(c) == SMT_SET), None))
  if path is None:
    return []
  config = read_config_file(path)
  return read_config(config.files, config.decls)


def compile_all(paths):
  """Every set, as (config, blocks) pairs."""
  vocab, macros = read_vocabulary(VOCAB_FILES), read_macros(MACRO_FILES)
  target = target_blocks(paths)
  out = []
  for p in paths:
    config = read_config_file(p)
    base = vocab if name_of(p) == SMT_SET else vocab.extended(target)
    out.append((config, compile_config(config, base, macros)))
  return out


# -----------------------------------------------------------------------------
# Checking against what is checked in
# -----------------------------------------------------------------------------

# Every pair that spells the same term two ways. Filled in by main once the
# vocabulary has been read, see build_aliases.
ALIASES = []


def build_aliases(vocab, macros):
  """Each way of spelling a term, and the one the configuration compiles to.

  Nothing is listed by hand. A native is folded into the name the embedding
  defines it under and a constructor into the macro that applies it, both read
  out of the files that define them, so a block that differs from what is
  checked in only by one of these is unchanged. The last pair is the rule for a
  constructor the SMT-LIB configuration declares rather than model_smt.eo:
  $emb_sm.X is applied by $sm_X, so it needs no entry of its own.
  """
  pairs = vocab.aliases + list(macros.items())
  return (sorted(pairs, key=lambda kv: (-len(kv[0]), kv[0]))
          + [('$emb_sm.', '$sm_')])


def unalias(text):
  for a, b in ALIASES:
    text = text.replace(a, b)
  return text


def despace(text):
  """The text as the stream of tokens it is.

  A bracket ends a token whether or not a space stands between it and its
  neighbour, so comparing the streams is what says two spellings are the same
  term. The file written by hand has a case with no space in it that no
  generated one would have.
  """
  return re.sub(r'\s+', ' ', re.sub(r'([()])', r' \1 ', text)).strip()


def normalize(text):
  return despace(unalias(text))


def split_blocks(text):
  """A definitions file as (symbol, text) pairs, in the order it gives them."""
  parts = re.split(r'^(; -- .*)$', text, flags=re.M)
  return [(parts[i][5:].strip(), (parts[i] + parts[i + 1]).strip('\n'))
          for i in range(1, len(parts), 2)]


DEF_RE = re.compile(r'\((?:program|define|declare-const|'
                    r'declare-parameterized-const) (\S+)')
USE_RE = re.compile(r'[\$@][\w.@$+*/<>=^!?-]+|\b[\w.]+\b')


def check_order(blocks, name, exempt=()):
  """Every name a block uses must be defined by that block or an earlier one.

  This is what the ordering of a definitions file is for, and the only thing
  the configuration has to give up in exchange for not stating it: the compiler
  emits in the order the files read and then checks the constraint holds.

  Two things are exempt, which is what `exempt` names. A program written over
  values, since the stage forward declares every one of them before it defines
  any, see DefsBlock::d_evalFwd; and the constructor of an entity and its
  macro, since the stage writes every constructor before it writes any case, so
  the default of a type may name the value it is whichever block comes first.
  """
  owner = {}
  for i, (_sym, text) in enumerate(blocks):
    for d in DEF_RE.findall(text):
      owner.setdefault(d, i)
  bad = 0
  for i, (sym, text) in enumerate(blocks):
    # A name in a comment is not a use: what the block says about itself may
    # well name a block that comes after it.
    body = re.sub(r';[^\n]*', '', DEF_RE.sub('', text))
    for u in sorted(set(USE_RE.findall(body))):
      if any(u.startswith(p) for p in exempt):
        continue
      if u in owner and owner[u] > i:
        print('  %s: %s uses %s, which block %s defines later'
              % (name, sym, u, blocks[owner[u]][0]))
        bad += 1
  print('  %-20s %d blocks, %d out-of-order uses' % (name, len(blocks), bad))
  return bad


def forms_of(text):
  """The top-level forms of text, in order, a comment stepped over."""
  out, i, n = [], 0, len(text)
  while i < n:
    c = text[i]
    if c == ';':
      while i < n and text[i] != '\n':
        i += 1
    elif c == '(':
      depth, j = 0, i
      while j < n:
        if text[j] == '"':
          j += 1
          while j < n and text[j] != '"':
            j += 1
        elif text[j] == ';':
          while j < n and text[j] != '\n':
            j += 1
        elif text[j] == '(':
          depth += 1
        elif text[j] == ')':
          depth -= 1
          if depth == 0:
            break
        j += 1
      out.append(text[i:j + 1])
      i = j
    i += 1
  return out


def check_forms(blocks, path):
  """Compare the *forms* of the generated file with those of the file at path.

  A block is a grouping, not a meaning: what the stage that reads the file goes
  on is the forms and the names each defines and uses, so a program moving
  between a block of its own and the block of the symbol whose cases name it
  changes nothing. This is what says the two files hold the same programs
  however they are grouped, and it compares the files whole rather than block
  by block, since a grouping that changes is exactly what it is there to see
  through.
  """
  gen = collections.Counter(normalize(x)
                            for _s, t in blocks for x in forms_of(t))
  mine = collections.Counter(normalize(x) for x in forms_of(read_text(path)))
  missing = mine - gen
  extra = gen - mine
  for k, v in list(missing.items())[:6]:
    print('  form missing (%d): %s' % (v, k[:110]))
  for k, v in list(extra.items())[:6]:
    print('  form added   (%d): %s' % (v, k[:110]))
  print('  %-20s %d forms, %d missing, %d added'
        % (os.path.basename(path), sum(gen.values()), sum(missing.values()),
           sum(extra.values())))
  return sum(missing.values()) + sum(extra.values())


def check_lean(config):
  """Compare the Lean the set says with what is checked in beside it."""
  name = os.path.basename(config.lean_target)
  text = render_lean(config)
  have = read_text(config.lean_target)
  print('  %-20s %d clauses, %s'
        % (name, len(config.clauses),
           'unchanged' if have == text else 'DIFFERS'))
  return 0 if have == text else 1


def check(blocks, path, verbose):
  """Compare generated blocks against those of the file at path.

  A block that agrees only after normalize is reported apart, since it spells
  the same term with a macro the file wrote out or with different whitespace.
  """
  checked_in = split_blocks(read_text(path))
  have = dict(checked_in)
  order = [s for s, _ in checked_in]
  same = respelt = moved = bad = 0
  for sym, text in blocks:
    if sym not in have:
      # A block of a program that used to stand inside a symbol's own.
      moved += 1
      if verbose:
        print('  %-28s new block (a program of its own)' % sym)
    elif have[sym] == text:
      same += 1
    elif normalize(have[sym]) == normalize(text):
      respelt += 1
      if verbose:
        why = []
        if unalias(have[sym]) != unalias(text):
          why.append('spacing')
        if despace(have[sym]) != despace(text):
          why.append('macro')
        print('  %-28s respelt (%s)' % (sym, ' and '.join(why)))
    elif not (collections.Counter(normalize(f) for f in forms_of(text))
              - collections.Counter(normalize(f) for f in forms_of(have[sym]))):
      # The block holds fewer forms than it did, the rest having moved into
      # blocks of their own; check_forms is what says none was lost.
      moved += 1
      if verbose:
        print('  %-28s regrouped' % sym)
    else:
      print('  %-28s DIFFERS' % sym)
      bad += 1
      for line in _diff(have[sym], text):
        print('      ' + line)
  pos = [order.index(s) for s, _ in blocks if s in order]
  print('  %-20s %d identical, %d respelt, %d regrouped, %d differing%s'
        % (os.path.basename(path), same, respelt, moved, bad,
           ', order differs' if pos != sorted(pos) else ', same order'))
  return bad


def _diff(a, b):
  import difflib
  return list(difflib.unified_diff(a.split('\n'), b.split('\n'),
                                   'checked-in', 'generated', lineterm='',
                                   n=1))[2:]


def render(blocks, config):
  return (header(config) + '\n'
          + '\n\n'.join(t for _, t in blocks) + '\n')


def write_if_changed(text, path):
  """Write the file only when its text changes.

  The pipeline compiles the configuration before every run, so a run that has
  nothing to do has to leave the tree as it found it.
  """
  if os.path.exists(path) and read_text(path) == text:
    return False
  d = os.path.dirname(path)
  if d:
    os.makedirs(d, exist_ok=True)
  write_text(path, text)
  return True


def compile_to_files(paths=CONFIGS, out_dir=None):
  """Compile each set and write what it compiles to, where it changed.

  This is what tools/eoc/driver.py calls before the model-smt stage. It gives
  back what each set compiled to, so the caller need not know the layout.
  """
  out = {}
  for config, blocks in compile_all(paths):
    target, lean_target = config.target, config.lean_target
    if out_dir is not None:
      target = os.path.join(out_dir, os.path.basename(target))
      lean_target = os.path.join(out_dir, os.path.basename(lean_target))
    write_if_changed(render(blocks, config), target)
    write_if_changed(render_lean(config), lean_target)
    out[config.path] = target
  return out


def main():
  ap = argparse.ArgumentParser(
      description='Compile the configuration of the model-smt signatures.')
  ap.add_argument('configs', nargs='*', metavar='CONFIG',
                  help='the central file of a set; both by default')
  ap.add_argument('--out-dir', default=None,
                  help='write the generated files here instead')
  ap.add_argument('--check', action='store_true',
                  help='compare with what is checked in rather than writing')
  ap.add_argument('-v', '--verbose', action='store_true')
  a = ap.parse_args()
  paths = a.configs or list(CONFIGS)
  global ALIASES
  ALIASES = build_aliases(read_vocabulary(VOCAB_FILES),
                          read_macros(MACRO_FILES))
  if a.check:
    bad = 0
    for config, blocks in compile_all(paths):
      name = os.path.basename(config.target)
      bad += check(blocks, config.target, a.verbose)
      bad += check_forms(blocks, config.target)
      bad += check_order(blocks, name,
                         config.decls.helper_prefixes()
                         + config.decls.constructor_prefixes())
      bad += check_lean(config)
    sys.exit(1 if bad else 0)
  for config, blocks in compile_all(paths):
    target, lean_target = config.target, config.lean_target
    if a.out_dir is not None:
      target = os.path.join(a.out_dir, os.path.basename(target))
      lean_target = os.path.join(a.out_dir, os.path.basename(lean_target))
    changed = write_if_changed(render(blocks, config), target)
    lean_changed = write_if_changed(render_lean(config), lean_target)
    print('%s %d blocks to %s'
          % ('wrote' if changed else 'unchanged,', len(blocks),
             os.path.relpath(target, ROOT)))
    print('%s %d clauses to %s'
          % ('wrote' if lean_changed else 'unchanged,', len(config.clauses),
             os.path.relpath(lean_target, ROOT)))
    print('  %s' % summary(config))


if __name__ == '__main__':
  main()
