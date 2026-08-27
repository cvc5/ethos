"""The shape of what the compiler writes, which is not what a signature says.

A signature says what its symbols mean. What the *files it compiles to* look
like -- which programs there are, what each declares and matches, and which
aggregate its cases are spliced into -- is settled by the stage that reads
them: see DefsFile::read in plugins/model_smt/defs_reader.cpp, which takes a
definitions file apart by the name of each program. That is a contract between
this compiler and that stage, not a knob, so it is written here rather than in
a file of the configuration.

There are two shapes, one per kind of set. The SMT-LIB signature is the target
of the compilation: its symbols are constants of the embedding, and each says
its type and its value. A signature of an *input* declares no constant -- the
constants are the target's -- and each of its symbols says what it becomes.

Everything below is text with holes, written with `str.format`:

  {symbol}   the name of the symbol the form is being written for
  {i}        the number of an argument, in text written once per argument

and `%s` in a `stands_for` for the parameter one argument was given. The two
shapes themselves are at the foot of the file.
"""

from sem_lang import FAMILY, applied, declared_type, die


# What an argument written as the input wrote it stands for: itself where the
# input is wanted, and transformed where the embedding is.
INPUT = 'input'


def spread(text, n):
  """One line per argument, from text written with {i}."""
  return [text.format(i=i + 1) for i in range(n)]


# -----------------------------------------------------------------------------
# The constant a symbol is declared as
# -----------------------------------------------------------------------------

class Constructor:
  """What every symbol of a set is declared as, where its set declares one.

  A set whose constants are another's -- the signature of an input, whose
  constants are the target's -- has none.
  """

  def __init__(self, name, macro, argument, returns, opaque=False,
               macro_reserved=True):
    self.name = name            # the constructor, e.g. $emb_sm.{symbol}
    self.macro = macro          # the macro that applies it
    self.argument = argument    # the type of an argument, by how it was written
    self.returns = returns
    self.opaque = opaque
    # Whether the macro is the compiler's name to write and no one else's. A
    # value has no bare name of its own -- what a body writes for one is a
    # macro of the set, `smt.bool` -- so the vocabulary block of the set names
    # the macro that applies each value, and the namespace is shared.
    self.macro_reserved = macro_reserved

  def type_of(self, kind, entry):
    if not self.argument:
      die('%s: every argument of a %s says the type it is of'
          % (entry.name, entry.decls.noun))
    if kind not in self.argument:
      die('%s: no argument of a constructor is %s' % (entry.name, kind))
    return self.argument[kind]

  def render(self, entry, ctx=None):
    """The constructor of a symbol together with the macro that applies it.

    An argument is of the type its parameter says, where it says one, and of
    what the kind it was written as stands for otherwise.
    """
    xs = [SLOT % (i + 1) for i in range(len(entry.params))]
    ts = [declared_type(t, entry, ctx) if t else self.type_of(k, entry)
          for k, t in zip(entry.kinds, entry.types)]
    con = self.name.format(symbol=entry.name)
    tail = ' :opaque' if self.opaque else ''
    return ['(declare-parameterized-const %s (%s) %s)'
            % (con, ' '.join('(%s %s%s)' % (x, t, tail)
                             for x, t in zip(xs, ts)), self.returns),
            '(define %s (%s) %s)'
            % (self.macro.format(symbol=entry.name),
               ' '.join('(%s %s)' % (x, t) for x, t in zip(xs, ts)),
               applied(con, xs))]


# -----------------------------------------------------------------------------
# One attribute a symbol may carry, and the program writing it produces
# -----------------------------------------------------------------------------

# What the i'th argument of a symbol is called in the program written for it.
SLOT = 'x%d'


class Aggregate:
  """One attribute a symbol may carry, and what writing it produces.

  A symbol says one case and the compiler writes the program around it. Most of
  what follows describes that program; `program` alone says where its cases
  then go.
  """

  def __init__(self, key, case, declares, signature, stands_for, level,
               program=None, matches=None, context=(), own=(), default=None,
               primary=False, sole=False, helper=None, helper_attr=None,
               helper_arg=None, helper_gives=None, otherwise=None, slots=None):
    self.key = key                  # the attribute a symbol writes
    self.case = case                # the program written for the symbol
    self.declares = declares        # what it declares, once per argument
    self.takes, self.gives = signature
    self.stands = stands_for        # what an argument means in a body, by kind
    self.level = level              # the vocabulary a body is written in
    self.program = program          # the aggregate its cases are spliced into
    # The prefix a case matches the symbol under where it gives no pattern of
    # its own: $sm_ for the macro of the target, empty for the symbol itself.
    # None where the subject is not the symbol applied to its arguments, and
    # every case then says what it matches.
    self.matches = matches
    self.context = context          # what a case is given beside the term
    self.own = own                  # what the program declares beside those
    # The prefix a symbol that says nothing about this attribute is applied
    # under, which is the case it then takes.
    self.default = default
    self.primary = primary          # the aggregate a symbol contributes to by
    self.sole = sole                # being one, and one it contributes to alone
    # The program a case may hand its work to, i.e. one written over what the
    # arguments evaluate to rather than over the arguments themselves.
    self.helper = helper
    self.helper_attr = helper_attr
    self.helper_arg = helper_arg
    self.helper_gives = helper_gives
    self.otherwise = otherwise      # (name, type, what it gives) for the rest
    # What a case calls the parameter of an argument, by how the argument was
    # written. A kind of entity whose arguments are not all of one type names
    # them apart, since the program the cases are spliced into declares each
    # name once: the width of a bit-vector and the element type of a sequence
    # stand in the same place and are not the same thing.
    self.slots = slots

  # -- the names a case is written with ---------------------------------------

  def slot(self, i, kind=None, declared=None):
    """What a case calls the parameter of its i'th argument.

    A parameter that says the type it is of is called after that type, so that
    the program the cases are spliced into can declare each name once; one that
    does not is called after its kind, or x<i> where the kind says nothing.
    """
    if declared is not None:
      return '%s%d' % (declared.split('_')[-1].lower(), i + 1)
    fmt = self.slots.get(kind, SLOT) if self.slots else SLOT
    return fmt % (i + 1)

  def params(self, entry, ctx, n):
    """What the program of a case declares.

    One line per argument, from what `declares` says. A kind of entity whose
    arguments are not all of one type says so by kind, the way a constructor
    says what it takes: a type of the embedding is built over types, except
    where an index is written raw, as the width of a bit-vector is.
    """
    out = ['(%s %s)' % (v, t) for v, t in self.context]
    out += ['(%s %s)' % (v, t) for v, t in self.own]
    if entry.types and any(t is not None for t in entry.types[:n]):
      # Each argument is of the type it says, and is declared under the name
      # that type gives it, see Aggregate.slot.
      for i, t in enumerate(entry.types[:n]):
        declared = declared_type(t, entry, ctx) if t else None
        out.append('(%s %s)' % (self.slot(i, entry.kinds[i], declared),
                                declared))
    elif isinstance(self.declares, dict):
      for i, kind in enumerate(entry.kinds[:n]):
        if kind not in self.declares:
          die('%s: no argument of %s is %s' % (entry.name, self.key, kind))
        out.append(self.declares[kind].format(i=i + 1))
    else:
      for line in self.declares:
        out += spread(line, n)
    return ' '.join(out)

  def head(self, entry, xs):
    """What a case matches where it gives no pattern of its own."""
    if self.matches is None:
      die('%s: every case of %s says what it matches, since the subject of '
          'one is not this symbol applied to its arguments'
          % (entry.name, self.key))
    return applied(self.matches + entry.name, xs)

  def scope(self, entry, xs):
    """What each name the entry declares stands for in a body of this
    aggregate: an argument reaches a case the way the shape says, and which way
    is said by how the argument was written."""
    env, surface = {}, set()
    for v, kind, x in zip(entry.params, entry.kinds, xs):
      if x is None:
        continue
      if kind not in self.stands:
        die('%s: no argument of %s is %s' % (entry.name, self.key, kind))
      t = self.stands[kind]
      if t == INPUT:
        env[v], surface = x, surface | {v}
      else:
        env[v] = t % x
    return env, surface

  # -- what it compiles to ----------------------------------------------------

  def program_of(self, entry):
    return self.case.format(symbol=entry.name)

  def render(self, entry, cases, ctx, n):
    """The per-symbol program a set writes for one attribute."""
    name = self.program_of(entry)
    given = ''.join(' ' + v for v, _ in self.context)
    body = '\n'.join('  ((%s%s %s) %s)' % (name, given, pat, rhs)
                     for pat, rhs in cases)
    return ('(program %s\n  (%s)\n  :signature %s %s\n  (\n%s\n  )\n)'
            % (name, self.params(entry, ctx, n), self.takes, self.gives, body))

  def helper_of(self, entry):
    return self.helper.format(symbol=entry.name)

  def render_helper(self, entry, cases, params, ctx, n, total=False):
    """The program written over what a symbol's arguments evaluate to.

    `total` says the cases already leave nothing over, in which case the one
    for what is left is not written: it could never be reached.
    """
    name = self.helper_of(entry)
    # Two cases may take a name apart the same way, and then declare it once:
    # the parameters of a program are of the program, not of a case of it.
    seen, kept = {}, []
    for p in params:
      v = p[1:].split()[0]
      if v not in seen:
        seen[v] = p
        kept.append(p)
      elif seen[v] != p:
        die('%s: %s is declared as %s and as %s'
            % (entry.name, v, seen[v], p))
    params = kept
    lines = ['  ((%s %s) %s)' % (name, pat, rhs) for pat, rhs in cases]
    if self.otherwise is not None and not total:
      v, t, gives = self.otherwise
      ts = spread('(%s %s)' % (v, t), n)
      params = params + ts
      lines.append('  ((%s %s) %s)'
                   % (name, ' '.join(x[1:].split()[0] for x in ts), gives))
    sig = ' '.join([self.helper_arg] * n)
    return ('(program %s\n  (%s)\n  :signature (%s) %s\n  (\n%s\n  )\n)'
            % (name, ' '.join(params), sig, self.helper_gives,
               '\n'.join(lines)))


# -----------------------------------------------------------------------------
# What one kind of set writes
# -----------------------------------------------------------------------------

class Shape:
  """One kind of entity a set declares: the attributes it may carry, in the
  order their programs are written, and the constant it is declared as.

  A set holds one kind or several -- the SMT-LIB signature declares its symbols
  and the types they are of -- and what they have in common is the file they
  stand in and the file they compile to, see Shapes."""

  def __init__(self, attributes, constructor=None, keyword='define-symbol',
               noun='symbol', params=True, keep=False, block='{symbol}'):
    self.aggregates = {a.key: a for a in attributes}
    self.order = [a.key for a in attributes]
    self.constructor = constructor
    self.primary = next((a.key for a in attributes if a.primary), None)
    # The form that declares one, which is what a set is read with.
    self.keyword = keyword
    # What one of them is, which is what it is counted as and what a directive
    # naming it says: a symbol, a type, a method or a rule.
    self.noun = noun
    # What the block of one is called, which is the name of the entity unless
    # a set holds two kinds that would name a block the same: Seq is a type
    # and a value both, and a block is named once.
    self.block = block
    # Whether an entity of this kind names the arguments it takes. One that
    # writes nothing of its own does not: what is said about a method or a
    # proof rule of the input is said about the whole of it.
    self.params = params
    # Whether every entity of this kind is the embedding's own, so that its
    # block stands whether or not the input declares the name, the way a
    # symbol that says :keep does. A type of the embedding is one: what is
    # written over the generated signature names its types whatever a calculus
    # trims away.
    self.keep = keep

  @property
  def raw_operators(self):
    """Whether a name in quotes the embedding does not have is an operator of
    the value layer rather than a misspelling.

    Most of the operators a model is evaluated with are SMT-LIB's own -- str.++,
    seq.extract, re.union -- and are forwarded to the backend by name, so there
    is no closed list of them to check against. Forwarding one is something only
    a set with a value layer can do, and a set has one exactly when it writes an
    attribute that gives a value back; nothing has to say so twice.
    """
    return any(a.level == 'value' for a in self.aggregates.values())

  def transform_into(self):
    """What a name of the input becomes where the embedding is wanted, i.e. the
    aggregate of that level applied to it."""
    return {a.level: '(%s %%s)' % a.program
            for a in self.aggregates.values() if a.program is not None}

  def prefixes(self):
    """The name the per-symbol program of each attribute is given, up to the
    symbol, longest first: a form written on its own is of the symbol its name
    ends with, and the longer prefix is the one that says so."""
    out = [a.case.split('{symbol}')[0] for a in self.aggregates.values()]
    return sorted(out, key=lambda p: (-len(p), p))

  def helper_prefixes(self):
    """The name each program written over values is given, up to the symbol.

    A case of one may name another whichever comes first, since the stage that
    reads the file forward declares every one of them before defining any.
    """
    return [a.helper.split('{symbol}')[0]
            for a in self.aggregates.values() if a.helper is not None]

  def reserved(self):
    """Every prefix the compiler gives a name under, and what a name under it
    is, longest first.

    These are the names the compiler writes for itself -- the case it writes
    for a symbol, the program a case hands its work to, the constant a symbol
    is declared as -- together with what a bare name of a body compiles to at
    each level, see FAMILY in sem_lang.py. The two are one list because they
    are one namespace: a program written by hand under `$smtx_model_eval_X` is
    what a body naming `X` reaches, so a helper would answer to a symbol that
    was never declared, and the name of a symbol that *is* declared would name
    the helper rather than the program the compiler wrote for it. An auxiliary
    program is named as itself instead, the way `$smtx_map_select` is.
    """
    out = {}
    for a in self.aggregates.values():
      out[a.case.split('{symbol}')[0]] = 'the case a symbol says of %s' % a.key
      if a.helper is not None:
        out[a.helper.split('{symbol}')[0]] = (
            'the program the %s of a symbol is worked out by' % a.key)
    if self.constructor is not None:
      out[self.constructor.name.split('{symbol}')[0]] = (
          'the constant a symbol is declared as')
      if self.constructor.macro_reserved:
        out[self.constructor.macro.split('{symbol}')[0]] = (
            'the macro that applies the constant of a symbol')
    for level, family in FAMILY.items():
      out.setdefault(family, 'what a bare name at %s level is' % level)
    return sorted(out.items(), key=lambda kv: (-len(kv[0]), kv[0]))

  def attrs(self):
    """The attributes a symbol of this set may carry, and how many values each
    takes; an attribute with a helper carries a second."""
    out = {}
    for k, a in self.aggregates.items():
      out[k] = _case_arity
      if a.helper is not None:
        out[a.helper_attr] = _case_arity
    # What the compilation has no place for at all. What says so is written on
    # the thing itself: a symbol, and the methods and the proof rules that
    # dropping one would leave behind.
    out['exclude'] = 0
    # The Lean text that follows the definition the lean-meta stage writes for
    # a method, i.e. what Lean has to be told and no compiler could derive.
    out['lean'] = 1
    # The other way round: a symbol the embedding names itself, whose block is
    # kept whether or not the input declares it. What is written over such a
    # symbol -- a hand-written proof about the generated Lean -- is written
    # whatever a signature trims away, see DefsBlock::d_keep.
    out['keep'] = 0
    # What a symbol is written under, where that is not its own name: a
    # signature may not declare one name twice, so the desugar stage gives an
    # overload of a symbol a name of its own, and the entry is written under
    # the name the input knows and says what that name is.
    out['overload'] = 1
    return out


class Shapes:
  """The kinds of entity one set declares, and what the set as a whole knows.

  A kind says what one entity of it compiles to; what is asked of the set --
  which forms declare an entity, which names the compiler writes for itself,
  what a bare name of a body may not be -- is asked of the kinds together.
  """

  def __init__(self, *shapes):
    self.shapes = shapes

  def parsers(self):
    """The form that declares an entity, and the kind it declares one of."""
    return {shape.keyword: shape for shape in self.shapes}

  @property
  def raw_operators(self):
    return any(shape.raw_operators for shape in self.shapes)

  def transform_into(self):
    out = {}
    for shape in self.shapes:
      out.update(shape.transform_into())
    return out

  def prefixes(self):
    out = [p for shape in self.shapes for p in shape.prefixes()]
    return sorted(out, key=lambda p: (-len(p), p))

  def helper_prefixes(self):
    return [p for shape in self.shapes for p in shape.helper_prefixes()]

  def constructor_prefixes(self):
    """The name each constructor and its macro is given, up to the entity.

    A block may name the constructor of one that stands after it, as the
    default value of a type names the value it is: the stage writes every
    constructor before it writes any case or program, so where the block of one
    stands says nothing about when its name may be used.
    """
    out = []
    for shape in self.shapes:
      if shape.constructor is not None:
        out.append(shape.constructor.name.split('{symbol}')[0])
        out.append(shape.constructor.macro.split('{symbol}')[0])
    return out

  def reserved(self):
    out = {}
    for shape in self.shapes:
      out.update(shape.reserved())
    return sorted(out.items(), key=lambda kv: (-len(kv[0]), kv[0]))


# An attribute that gives a case may give what it matches before what it
# returns, which is what a second value says: a value is never a keyword, so
# what follows tells the two apart without marking either.
def _case_arity(rest):
  return 2 if len(rest) > 1 and rest[1].kind != 'kw' else 1


# -----------------------------------------------------------------------------
# The two shapes
# -----------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# The SMT-LIB signature, the target of the compilation
# ---------------------------------------------------------------------------

# Every symbol is a constant of the embedding, applied by a macro of its own.
# An argument is a term, or a type where the symbol was given one.
CONSTANT = Constructor(
    name='$emb_sm.{symbol}',
    macro='$sm_{symbol}',
    argument={'plain': '$smt_Term', 'raw': '$smt_Term', 'type': '$smt_Type'},
    opaque=True,
    returns='$smt_Term')

# The type of a term. A symbol says one case of it, in which an argument stands
# for its type, and an index or a type for itself.
TYPEOF = Aggregate(
    key='typeof',
    program='$smtx_typeof',
    case='$eoc_typeof_{symbol}',
    matches='$sm_',
    declares=['(x{i} $smt_Term)'],
    signature=('($smt_Term)', '$smt_Type'),
    stands_for={'plain': '($smtx_typeof %s)', 'raw': '%s', 'type': '%s'},
    level='type')

# The value of a term in a model. A symbol says one case of it, in which an
# argument stands for its value and M for the model; a symbol that says none
# hands its work to the program below, which is written over values rather than
# over terms and so is what may take one apart.
VALUE = Aggregate(
    key='value',
    program='$smtx_model_eval',
    case='$eoc_eval_{symbol}',
    context=[('M', '$smt_Model')],
    matches='$sm_',
    declares=['(x{i} $smt_Term)'],
    signature=('($smt_Model $smt_Term)', '$smt_Value'),
    stands_for={'plain': '($smtx_model_eval M %s)',
                'raw': '($smtx_model_eval M %s)', 'type': '%s'},
    level='value',
    default='$smtx_model_eval_',
    helper='$smtx_model_eval_{symbol}',
    helper_attr='eval',
    helper_arg='$smt_Value',
    helper_gives='$smt_Value',
    otherwise=('t{i}', '$smt_Value', '$vsm_NotValue'))

# ---------------------------------------------------------------------------
# The signature of an input
# ---------------------------------------------------------------------------

# What a symbol of the input becomes. It is the aggregate a symbol contributes
# to by being one, so a symbol that says nothing about it still says this: it
# becomes the SMT-LIB symbol of the same name, applied to what its arguments
# become. That is what all but sixteen of them do.
TERM = Aggregate(
    key='term',
    primary=True,
    program='$eo_to_smt',
    case='$eoc_transform_{symbol}',
    matches='',
    own=[('T', 'Type')],
    declares=['(T{i} Type)', '(x{i} T{i})'],
    signature=('(T)', '$smt_Term'),
    stands_for={'plain': '($eo_to_smt %s)', 'type': '($eo_to_smt_type %s)',
                'raw': INPUT},
    default='$sm_',
    level='term')

# What a type constructor of the input becomes. A symbol that says a case of
# this says one of nothing else, since a type constructor is not a symbol of
# terms.
TYPE = Aggregate(
    key='type',
    sole=True,
    program='$eo_to_smt_type',
    case='$eoc_transform_type_{symbol}',
    matches='',
    declares=['(T{i} Type)', '(x{i} T{i})'],
    signature=('(Type)', '$smt_Type'),
    stands_for={'plain': '($eo_to_smt_type %s)', 'raw': INPUT},
    level='type')

# Whether a term is the nil of an n-ary symbol, which the desugar stage asks by
# name rather than by splicing a case. It is the one thing a block says to a
# stage other than the model, and its body is of the input throughout, so it is
# written as it stands. Its subject is one term rather than the symbol applied
# to its arguments, so every case says what it matches.
IS_LIST_NIL = Aggregate(
    key='is-list-nil',
    case='$eoc_is_list_nil_{symbol}',
    own=[('T', 'Type'), ('x1', 'T')],
    declares=[],
    signature=('(T)', 'Bool'),
    stands_for={'plain': '%s', 'type': '%s', 'raw': '%s'},
    level='input')

# ---------------------------------------------------------------------------
# The types of the SMT-LIB signature, which stand in the same file as its
# symbols
# ---------------------------------------------------------------------------

# Every type is a constructor of the embedding too, applied by a macro of its
# own. An argument is a type, or the index a type is built over where the
# signature wrote one raw, as the width of a bit-vector is.
TYPE_CONSTANT = Constructor(
    name='$emb_tsm.{symbol}',
    macro='$tsm_{symbol}',
    argument={'plain': '$smt_Type', 'raw': '$native_Nat'},
    opaque=True,
    returns='$smt_Type')

# What every case of a type says about it, i.e. the type applied to what it is
# built over, and what each argument stands for there: itself, since the whole
# of a type is already of the embedding.
TYPE_DECLARES = {'plain': '(x{i} $smt_Type)', 'raw': '(n{i} $native_Nat)'}
TYPE_STANDS = {'plain': '%s', 'raw': '%s'}
TYPE_SLOTS = {'plain': 'x%d', 'raw': 'n%d'}

# Whether a type is well-founded, i.e. whether the values of it are a set at
# all. A type that says nothing is: the recursion is what a type built over
# another has to answer for, and the rest answer for nothing.
TYPE_WF = Aggregate(
    key='wf',
    program='$smtx_type_wf_rec',
    case='$eoc_type_wf_{symbol}',
    matches='$tsm_',
    declares=TYPE_DECLARES,
    slots=TYPE_SLOTS,
    signature=('($smt_Type)', '$native_Bool'),
    stands_for=TYPE_STANDS,
    level='native')

# Whether a type has a bounded number of values, under the flag that says
# which bound is asked: exactly one value if it is true, finitely many if it
# is false. A type that says nothing has neither.
TYPE_BOUNDED = Aggregate(
    key='bounded',
    program='$smtx_type_bounded',
    case='$eoc_type_bounded_{symbol}',
    context=[('u', '$native_Bool')],
    matches='$tsm_',
    declares=TYPE_DECLARES,
    slots=TYPE_SLOTS,
    signature=('($native_Bool $smt_Type)', '$native_Bool'),
    stands_for=TYPE_STANDS,
    level='native')

# The first value of a type, which a model reaches for where it has to name
# one of a type it knows nothing else about. A type that says nothing has none.
TYPE_DEFAULT = Aggregate(
    key='default',
    program='$smtx_type_default',
    case='$eoc_type_default_{symbol}',
    matches='$tsm_',
    declares=TYPE_DECLARES,
    slots=TYPE_SLOTS,
    signature=('($smt_Type)', '$smt_Value'),
    stands_for=TYPE_STANDS,
    level='value')

# ---------------------------------------------------------------------------
# What a signature of an input holds beside its symbols
# ---------------------------------------------------------------------------

# A program written out in Eunoia rather than a symbol a proof applies: one of
# the embedding, in the target, and one the signature of an input writes out.
# It writes nothing into the definitions file, since what is said about a
# program is said to a stage rather than to the model: `:lean`, which is the
# text the lean-meta stage puts after the definition it writes, and `:exclude`.
METHODS = Shape([], keyword='define-method', noun='method', params=False)

# A proof rule of the input, which says only that it is left out.
RULES = Shape([], keyword='define-rule', noun='rule', params=False)

# ---------------------------------------------------------------------------
# The values of the SMT-LIB signature, which stand in the same file
# ---------------------------------------------------------------------------

# Every value is a constructor of the embedding too, applied by a macro of its
# own. What each is built over its parameters say, one by one: a value is built
# over natives of several sorts, over types, and over the shapes a map and a
# sequence are.
VALUE_CONSTANT = Constructor(
    name='$emb_vsm.{symbol}',
    macro='$vsm_{symbol}',
    argument={'plain': '$smt_Value'},
    opaque=True,
    macro_reserved=False,
    returns='$smt_Value')

# What each argument stands for in a body: itself, since a value is of the
# embedding already.
VALUE_STANDS = {'plain': '%s', 'raw': '%s'}

# The type a value is of, i.e. what a term it is the value of would be of. A
# value that says nothing is of no type at all.
VALUE_TYPEOF = Aggregate(
    key='typeof',
    program='$smtx_typeof_value',
    case='$eoc_value_typeof_{symbol}',
    matches='$vsm_',
    declares=['(x{i} $smt_Value)'],
    signature=('($smt_Value)', '$smt_Type'),
    stands_for=VALUE_STANDS,
    level='type')

# Whether a value is canonical, i.e. whether it is the one spelling of what it
# denotes. A value that says nothing is.
VALUE_CANONICAL = Aggregate(
    key='canonical',
    program='$smtx_value_canonical_bool',
    case='$eoc_value_canonical_{symbol}',
    matches='$vsm_',
    declares=['(x{i} $smt_Value)'],
    signature=('($smt_Value)', '$native_Bool'),
    stands_for=VALUE_STANDS,
    level='native')

# ---------------------------------------------------------------------------
# The literals of the embedding
# ---------------------------------------------------------------------------

# A literal is a term the embedding builds over a native -- a Boolean, a
# numeral, the width and the value of a bit-vector -- rather than over terms,
# so what its constructor takes is what its parameters say and there is no type
# of arguments to fall back on.
LITERAL_CONSTANT = Constructor(
    name='$emb_sm.{symbol}',
    macro='$sm_{symbol}',
    argument={},
    opaque=True,
    returns='$smt_Term')

# What an argument stands for in a body: itself, since what a literal carries
# is a native rather than a term whose type or value is asked for.
LITERAL_STANDS = {'plain': '%s'}

# The type a literal is of, and its value in a model, which are the two the
# symbols say as well: the cases of a literal are spliced into the same
# programs, and stand before them, see $SMT_LITERAL_CONSTRUCTORS$ in
# plugins/model_smt/model_smt.eo.
LITERAL_TYPEOF = Aggregate(
    key='typeof',
    program='$smtx_typeof',
    case='$eoc_typeof_{symbol}',
    matches='$sm_',
    declares={},
    signature=('($smt_Term)', '$smt_Type'),
    stands_for=LITERAL_STANDS,
    level='type')

LITERAL_VALUE = Aggregate(
    key='value',
    program='$smtx_model_eval',
    case='$eoc_eval_{symbol}',
    context=[('M', '$smt_Model')],
    matches='$sm_',
    declares={},
    signature=('($smt_Model $smt_Term)', '$smt_Value'),
    stands_for=LITERAL_STANDS,
    level='value')

SYMBOLS = Shape([TYPEOF, VALUE], constructor=CONSTANT)
# A literal is the embedding's own, as the types and the values are. Its block
# is named after the constructor it declares, which is what tells the stage
# that reads the file that the constructor is one of the embedding's own rather
# than one of a symbol written over them, see DefsFile::addBlock.
LITERALS = Shape([LITERAL_TYPEOF, LITERAL_VALUE], constructor=LITERAL_CONSTANT,
                 keyword='define-literal', noun='literal', keep=True,
                 block='$emb_sm.{symbol}')
# A value of the embedding is the embedding's own, as its types are.
VALUES = Shape([VALUE_TYPEOF, VALUE_CANONICAL], constructor=VALUE_CONSTANT,
               keyword='define-value', noun='value', keep=True,
               block='$emb_vsm.{symbol}')
# A type of the embedding is the embedding's own whatever a calculus declares,
# so its block is kept the way a symbol that says :keep is.
TYPES = Shape([TYPE_WF, TYPE_BOUNDED, TYPE_DEFAULT], constructor=TYPE_CONSTANT,
              keyword='define-sort', noun='type', keep=True)

INPUT_SYMBOLS = Shape([TERM, TYPE, IS_LIST_NIL])

TARGET = Shapes(SYMBOLS, LITERALS, TYPES, VALUES, METHODS)
INPUT_SET = Shapes(INPUT_SYMBOLS, METHODS, RULES)


def of(target):
  """The shape a set of this kind compiles to."""
  return TARGET if target else INPUT_SET
