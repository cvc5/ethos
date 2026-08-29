#!/usr/bin/env python3
"""Compiles the configuration sets under semantics into the
signatures written directly in the deep embedding, i.e.

  semantics/smt.eos  ->  tools/eoc/out/smt_defs.eo
                      what each SMT-LIB symbol means to the model
  semantics/development-cpc.eos  ->  tools/eoc/out/user_defs.eo
                      how each symbol of the input transforms into the
                      SMT-LIB one

Beside those it compiles the sets that are fixed rather than named by a run:
the native layer of each backend, and the aggregates of the deep embedding,
plugins/model_smt/model_smt.eos, which is written into the head of each of the
two files above and says how the stage that reads them is to take them apart.

Each set has a central file, the one named above, which declares the shape of
what the set compiles to -- its aggregates, its constructor and its shapes, see
sem_decl.py -- and then says what it compiles to and which files it is made of.
Nothing else is read while a set is compiled, so a form belongs to one
signature by the set it stands in and by nothing else.

What is left here is the reading of s-expressions, the four levels and the
naming conventions of the embedding; everything about what a set compiles to is
said by the set. The language the sets are written in is documented in full in
semantics/README.md.

  usage: sem_compile.py [--out-dir DIR] [--check] [--semantics CONFIG]
                        [--smt-semantics CONFIG] [CONFIG...]

The eoc pipeline runs this before the model-smt stage, see
compile_signatures in tools/eoc/driver.py, so the generated files are current
whenever that stage reads them. A file is written only when its text changes,
so a run with nothing to do leaves the tree alone.

With --check nothing is written: the ordering constraint of a definitions
file is checked instead, see check_order, and each generated file is compared
with what compiling would write, which is what says whether it is current.
"""

import argparse
import itertools
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import report  # noqa: E402
import sem_target  # noqa: E402
from sem_lang import (counts, defined_names, die,  # noqa: E402
                      excludes, lean_clauses, read_config, read_macros,
                      read_text, read_vocabulary, write_text)

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
# The file each set stands in. A set is one file: it holds its theories in the
# order their blocks are emitted, one to a section.
CONFIGS = (os.path.join(SEM, 'smt.eos'), os.path.join(SEM, 'development-cpc.eos'))

# The sets the tool ships with, each with its role: whether it is the SMT-LIB
# signature, which is the target of the compilation, rather than the signature
# of an input. The two compile to different things, so a run has to know which
# a set is before it reads a line, and the role is what says so: for these two
# it is fixed here, and for any other set it is said by the option that names
# it, --smt-semantics for a target and --semantics for an input -- never by
# what a file is called.
SHIPPED = ((CONFIGS[0], True), (CONFIGS[1], False))

# The native layer of the Lean backend: what the generated Lean is written over
# and no compiler writes. It is one set, and a fixed one -- there is one such
# layer, not one per input -- so it is compiled beside the two above rather
# than named by an option. It stands in the plugin that reads what it compiles
# to, since it is of that backend and of nothing else.
# The natives of the embedding: what a signature written in it may call that no
# compiler writes, and what each argument of one is. The desugar layer carries a
# declaration of each, which is what says one exists and what it takes; that
# declaration is written from this set rather than by hand, see render_natives.
# What a native *does* is said by a backend, in a native layer of its own, see
# LAYERS; the two are apart because a backend may implement a native the
# embedding does not have, and the embedding may have one a backend gets from
# its own language.
NATIVES_CONFIG = os.path.join(ROOT, 'plugins', 'desugar', 'natives.eos')
NATIVE_DEFS_TARGET = os.path.join(OUT, 'native_defs.eo')
# The same natives written as Eunoia, which is the native layer of the eo-meta
# backend: a signature desugared and then written back this way is stated over
# the primitives that set names and no others. A native it does not name keeps
# the body every other backend gives it, which no Eunoia evaluates.
EO_CONFIG = os.path.join(ROOT, 'plugins', 'eo_meta', 'eo.eos')
EO_DEFS_TARGET = os.path.join(OUT, 'native_eo_defs.eo')

# The aggregates of the deep embedding: which programs a symbol contributes a
# case to, and where the model-smt stage writes them. It is one set and a fixed
# one -- the shape of what is written is not something a run may name another
# of -- so it stands in the plugin that reads what it compiles to, as a native
# layer does, and is read whatever a run compiles. What it compiles to is no
# file of its own: it is written into the head of each generated signature,
# which is the file it is about.
AGGREGATE_CONFIG = os.path.join(ROOT, 'plugins', 'model_smt', 'model_smt.eos')
# The template of that stage, which is where the markers an entry names have
# to be for the cases to reach the generated file.
AGGREGATE_TEMPLATE = os.path.join(ROOT, 'plugins', 'model_smt', 'model_smt.eo')

NATIVE_CONFIG = os.path.join(ROOT, 'plugins', 'lean_meta', 'lean.eos')
NATIVE_TARGET = os.path.join(OUT, 'lean_native.lean')
VC_CONFIG = os.path.join(ROOT, 'plugins', 'smt_meta', 'smt-vc.eos')
VC_TARGET = os.path.join(OUT, 'smt_vc_native.smt2')

# Where the vocabulary of the embedding is defined. A file of the configuration
# names a native in quotes and a type of the embedding without its $smt_, and
# the compiler puts the name back, so this is what says one exists, what it
# takes, and what each of its places is of.
VOCAB_FILES = (os.path.join(ROOT, 'plugins', 'desugar', 'native_embed.eo'),
               os.path.join(ROOT, 'plugins', 'desugar', 'eo_desugar.eo'),
               os.path.join(ROOT, 'plugins', 'desugar', 'eo_desugar_native.eo'),
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
;   python3 tools/eoc/sem_compile.py --check    to say whether it is current
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
-- A clause may not name the native layer. It is appended to a generated
-- definition rather than written into a resource, so it is not one of the
-- blocks that layer is trimmed by and a name it gave would keep nothing
-- alive. Every native type abbreviates a Lean type, which is what a clause
-- writes instead. See LeanMetaReduce::useNative.
--
%s"""

# What each of the two Lean files is for, which is what the set it comes from
# is: the programs of the deep embedding are compiled through whichever the
# input is, so the stage reads that file for itself and is given the other.
# Written as it is to be read, since text a run wraps for itself is text a run
# could wrap differently. Keyed by whether the set is the target.
LEAN_WHICH = {
    True: """\
-- This file is for the programs of the deep embedding, which every input is
-- compiled through. A program of an input signature is named in a file of its
-- own, which the compiler is given with --lean-config.""",
    False: """\
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
  out = [LEAN_GENERATED % (named(config.path), LEAN_WHICH[config.is_target])]
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
  """One set: the file it stands in, the role it was given, and the shape of
  what it writes."""

  def __init__(self, path, decls, files, doc, is_target):
    self.path = path
    self.decls = decls          # the shape of what it writes
    self.files = files          # the file it stands in
    self.doc = doc              # what the central file says about the set
    # Whether the set is the SMT-LIB signature, which is the target of the
    # compilation, rather than the signature of an input. This is the role the
    # run gave the set, see SHIPPED.
    self.is_target = is_target
    # What compiling it came to beside its blocks: what its methods say the
    # generated Lean is to be told, what the compilation has no place for, and
    # how much of each thing it holds.
    self.clauses = []
    self.excludes = []
    self.counts = {}

  @property
  def name(self):
    return name_of(self.path)

  @property
  def target(self):
    """The signature in the deep embedding it compiles to.

    Where a set compiles to is said by its role and by nothing else, so the
    file has one name whatever the set is called and wherever it stands: a run
    compiles one set of each role, and the stages read the two files those
    wrote. Nothing checks them in; what is kept is the configuration.
    """
    return SMT_TARGET if self.is_target else INPUT_TARGET

  @property
  def lean_target(self):
    """Where what its methods say the generated Lean is to be told is written,
    on the same terms."""
    return SMT_LEAN_TARGET if self.is_target else INPUT_LEAN_TARGET


def same_file(a, b):
  """Whether two paths name one file, which neither has to exist to answer:
  a set is compared with the ones the tool ships with before anything is
  written."""
  return os.path.realpath(a) == os.path.realpath(b)


def name_of(path):
  """The set a file is of, which is what it is called."""
  return os.path.splitext(os.path.basename(path))[0]


def role_of(path):
  """The role of a set the tool ships with, or None for any other.

  Which shape a set compiles to is said by the role a run gives it, never by
  what its file is called: for the shipped sets the role is fixed, see
  SHIPPED, and any other is given one by the option that names it.
  """
  for c, is_target in SHIPPED:
    if same_file(path, c):
      return is_target
  return None


# -----------------------------------------------------------------------------
# The natives of the embedding
# -----------------------------------------------------------------------------

NATIVES_GENERATED = """\
; GENERATED FILE -- do not edit.
;
; The natives of the embedding, compiled from %s by
; tools/eoc/sem_compile.py, which is where one is to be changed or added. Each
; is a name a signature written in the embedding may call, declared as the
; operator it forwards to; what one *does* is said by a backend, see
; plugins/lean_meta/lean.eos and plugins/smt_meta/smt-vc.eos.
;
; The desugar stage puts this file where the `(include "native_defs.eo")` of
; plugins/desugar/native_embed.eo stands, see Pipeline.desugar in
; tools/eoc/driver.py.
;
"""


def read_natives(vocab, path=NATIVES_CONFIG):
  """Read the natives set, in the order it gives its entries.

  The type of each argument is named the way a type is named everywhere in the
  configuration, i.e. a native in quotes, and is checked against the vocabulary
  the hand-written files declare: those are what the aliases stand in, so a
  native may be written over them and none of them over a native.
  """
  out = []
  for b in read_config([path], sem_target.NATIVE_DECL_SET):
    for e in b.entries():
      what = 'natives: ' + e.name
      types = []
      for v, node in zip(e.params, e.types):
        if node is None or node.kind != 'str':
          die('%s: %s says the type it is of, written the way a native is, '
              'e.g. (%s "Int")' % (what, v, v))
        full = '$native_' + node.val
        if full not in vocab:
          die('%s: there is no type called %s' % (what, full))
        types.append(full)
      out.append((e, types))
  return out


def read_eo_impls(path=EO_CONFIG):
  """What each native is, said as Eunoia, keyed by the native it is of."""
  out = {}
  for b in read_config([path], sem_target.NATIVE_SET):
    for e in b.entries():
      if not e.has('eo-impl'):
        die('%s: %s says what it is under :eo-impl' % (named(path), e.name))
      out[e.name] = e.get('eo-impl').val
  return out


def render_natives(natives, impls=None):
  """The natives as the file a stage reads.

  A native is declared as the operator it forwards to, which is its own name
  unless :op says another: the embedding names the numeral zero $native_z_zero
  and forwards it as "0". Where `impls` gives one a body of its own, that body
  stands there instead, which is what the eo-meta backend is: the same
  declarations, written as Eunoia.
  """
  out = [(EO_GENERATED if impls is not None else NATIVES_GENERATED)
         % named(EO_CONFIG if impls is not None else NATIVES_CONFIG)]
  for e, types in natives:
    name = '$native_' + e.name
    op = e.get('op').val if e.has('op') else e.name
    doc = '\n'.join(e.doc) + '\n' if e.doc else ''
    ps = ' '.join('(%s %s)' % (v, t) for v, t in zip(e.params, types))
    body = (impls or {}).get(e.name) or '($native_apply_%d "%s"%s)' % (
        len(types), op, ''.join(' ' + v for v in e.params))
    if not types:
      out.append('%s(define %s () %s)' % (doc, name, body))
    else:
      out.append('%s(define %s (%s)\n  %s)' % (doc, name, ps, body))
  return '\n\n'.join(out) + '\n'


# -----------------------------------------------------------------------------
# The aggregates of the embedding
# -----------------------------------------------------------------------------

AGGREGATE_MANIFEST = """\
; What each name below is, and where the model-smt stage is to put it. The
; case a symbol says of an aggregate is written under <case>, and the stage
; writes those cases at <into>, which is a marker of its template. A line that
; says `whole` is a program emitted under the name of the aggregate rather
; than a case spliced into it, and a $eoc-helper line names the programs
; written over values that the cases of an aggregate hand their work to,
; together with where they are declared ahead of it.
;
; Compiled from plugins/model_smt/model_smt.eos, which is where an aggregate
; is to be changed or added. See DefsFile::read.
;
"""


# What a block of a signature says to a stage rather than to the model, which
# the head of the generated file is what carries: the compiler knows both, and
# a stage that had to read them out of the blocks would be taking the file
# apart a second way. See Pipeline.defs_head in tools/eoc/driver.py.
#
# The parameters a program of a block declares, and a name in head position.
# What is left when the second has the first taken out of it is what the block
# names, which over-approximates the symbols of the input it depends on: a name
# that is of no symbol has no definition to keep alive and is discarded by the
# stage, see resolveDependencies in plugins/trim_defs/trim_defs.cpp.
DEPENDS_PARAMS = re.compile(r'\(\((?:[^()]|\([^()]*\))*\)\)')
DEPENDS_HEAD = re.compile(r'\(([A-Za-z@_][^\s()]*)')
# A directive the block gives to a stage, which says nothing about the model
# and so names nothing.
DEPENDS_DIRECTIVE = re.compile(r'\(echo\s+"[^"]*"\)')


def depends(sym, text):
  """The symbols of the input one block names.

  A block may name a symbol of the input, as the transformation of
  @quantifiers_skolemize names forall in the pattern it matches. Trimming the
  input to one proof rule has to keep such a symbol, or the case the model-smt
  stage emits for the block would name something the trimmed signature no
  longer declares.

  One is a name in head position that no program of the block binds and that is
  neither of the embedding, which is written with a leading dollar, nor of
  Eunoia, which is written eo::.
  """
  body = DEPENDS_DIRECTIVE.sub('', text)
  body = re.sub(r';[^\n]*', '', body)
  bound = {sym, 'program', 'define', 'declare-const',
           'declare-parameterized-const'}
  for params in DEPENDS_PARAMS.findall(body):
    bound.update(DEPENDS_HEAD.findall(params))
  heads = set(DEPENDS_HEAD.findall(body))
  return sorted(h for h in heads - bound if not h.startswith('eo::'))


def head_lines(config, blocks):
  """What the head of a generated signature says to the stages beside the
  aggregates: what the compilation has no place for, and what each block names
  of the input.

  A set says the first on the entity itself -- a symbol, a method or a proof
  rule that says :exclude -- so it is taken from there rather than read back
  out of what was written for it. The second is of a signature of an input
  alone: the symbols of the target are the embedding's own and are trimmed by
  nothing.
  """
  out = []
  for name, kind in config.excludes:
    out.append('; $eoc-exclude %s %s' % (kind, name))
  if not config.is_target:
    for sym, text in blocks:
      named = depends(sym, text)
      if named:
        out.append('; $eoc-depends %s %s' % (sym, ' '.join(named)))
  return out


EO_GENERATED = """\
; GENERATED FILE -- do not edit.
;
; The natives of the embedding written as Eunoia, compiled from %s
; by tools/eoc/sem_compile.py. This is the native layer of the eo-meta
; backend: a signature desugared with this in place of native_defs.eo is
; stated over the Eunoia primitives that set names and no others, which is a
; smaller proof language than the one that went in.
;
; A native that set does not name keeps the body it has for every other
; backend, an application of $native_apply_N, which no Eunoia evaluates.
;
"""


class AggregateEntry:
  """One entry of the aggregate set, i.e. what this compiler and the model-smt
  stage agree on about one aggregate. How a case of it is *written* is no part
  of that and is said in sem_target.py, see sem_target.bind."""

  def __init__(self, name, case, into, helper, forward, whole):
    self.name = name
    self.case = case            # what a symbol's case is named, up to the symbol
    self.into = into            # the marker of the template the cases go at
    self.helper = helper        # the programs written over values, if any
    self.forward = forward      # where those are declared, ahead of the aggregate
    self.whole = whole          # emitted whole rather than spliced as cases

  def lines(self):
    """The entry as the stage reads it."""
    out = ['; $eoc-aggregate %s %s %s%s'
           % (self.name, self.case, self.into, ' whole' if self.whole else '')]
    if self.helper is not None:
      out.append('; $eoc-helper %s %s' % (self.helper, self.forward))
    return out


def read_aggregates(path=AGGREGATE_CONFIG):
  """Read the aggregate set, in the order it gives its entries.

  A marker an entry names has to be one the template has, since a case written
  at a marker that is not there would be compiled and then dropped without a
  word; and two entries may not share a name or a case, since the longest case
  a name begins with is what says which aggregate it belongs to.
  """
  template = read_text(AGGREGATE_TEMPLATE)
  out, cases, markers = {}, {}, {}
  for b in read_config([path], sem_target.AGGREGATE_SET):
    for e in b.entries():
      what = 'semantics/' + name_of(path) + ': ' + e.name
      for a in ('case', 'into'):
        if not e.has(a):
          die('%s: an aggregate says :%s' % (what, a))
      if e.has('helper') != e.has('forward'):
        die('%s: a program written over values is declared ahead of the '
            'aggregate, so :helper and :forward are said together' % what)
      entry = AggregateEntry(e.name, e.get('case').val, e.get('into').val,
                             e.get('helper').val if e.has('helper') else None,
                             e.get('forward').val if e.has('forward') else None,
                             e.has('whole'))
      for marker in (entry.into, entry.forward):
        if marker is not None and marker not in template:
          die('%s: %s names %s, which %s does not have'
              % (what, e.name, marker, named(AGGREGATE_TEMPLATE)))
      if e.name in out:
        die('%s: %s is declared twice' % (what, e.name))
      if entry.case in cases:
        die('%s: %s and %s are both written under %s, so a case of one would '
            'be read as a case of the other'
            % (what, cases[entry.case], e.name, entry.case))
      if entry.into in markers:
        die('%s: %s and %s are both written at %s, which is one place in one '
            'program: an aggregate is written at a marker of its own'
            % (what, markers[entry.into], e.name, entry.into))
      out[e.name], cases[entry.case] = entry, e.name
      markers[entry.into] = e.name
  return out


_NATIVES = None


def natives():
  """The natives set, read once, and what it compiles to.

  The types an entry names are the aliases the hand-written files declare, so
  the vocabulary is read from those first and the natives are checked against
  it; what they compile to then joins it, which is what puts them in reach of
  every set the run compiles.
  """
  global _NATIVES
  if _NATIVES is None:
    read = read_natives(read_vocabulary(VOCAB_FILES))
    # The same declarations twice: as the operator each forwards to, which is
    # what every backend but one reads, and as Eunoia, which is what the
    # eo-meta backend reads. See render_natives.
    _NATIVES = (read, render_natives(read),
                render_natives(read, read_eo_impls()))
  return _NATIVES


_AGGREGATES = None


def aggregates():
  """The aggregate set, read once and joined onto what sem_target.py writes.

  Every shape is read against it, so the two halves of an aggregate are known
  to be there before a line of a signature is compiled.
  """
  global _AGGREGATES
  if _AGGREGATES is None:
    _AGGREGATES = read_aggregates()
    sem_target.bind(_AGGREGATES)
  return _AGGREGATES


def read_config_file(path, is_target):
  """Read the file a set stands in, in the role the run gave it.

  A set is one file. What it compiles to is fixed by the tool, see
  Config.target, and so is the shape of what it writes, see sem_target.py, so
  the file holds nothing but the theories themselves; which of the two shapes
  is written is what `is_target` says, see role_of.
  """
  # The heading of the file, which is what the generated file says about
  # itself: the two describe the same signature.
  doc = list(itertools.takewhile(lambda l: l.startswith(';'),
                                 read_text(path).split('\n')))
  aggregates()
  return Config(path, sem_target.of(is_target), [path], doc, is_target)


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
  config.excludes = excludes(blocks)
  config.counts = counts(blocks)
  return out


def check_distinct(configs):
  """A run compiles one set of each role, and no more.

  Where a set compiles to is said by its role, see Config.target, so two of
  one role would write one file and what was written first would be read as
  what was written last. The run refuses instead.
  """
  seen = {}
  for config in configs:
    t = config.target
    if t in seen:
      die('%s and %s are both the %s, and a run compiles one of each: they '
          'would both write %s'
          % (seen[t], config.name,
             'SMT-LIB semantics' if config.is_target else 'input semantics',
             report.rel(t)))
    seen[t] = config.name


def target_blocks(sets):
  """The blocks of the set that is the target, for the vocabulary of the rest.

  An input is compiled *through* the target, so a symbol the target declares is
  one an input may name -- the bit-vector literal is, and so is each binder --
  and what each place of that symbol is of is what says how an argument written
  there is transformed. Reading the target is what puts that in reach; without
  it an argument falls back to the level around it, and a native written under
  a symbol that takes one comes out wrapped as a term.

  The target is read whether or not this run compiles it, since an input set
  compiled on its own is written against it just the same. Which set is the
  target is the role a run gave it, never what its file is called, see role_of.
  """
  path = next((p for p, t in sets if t),
              next((c for c, t in SHIPPED if t), None))
  if path is None:
    return []
  config = read_config_file(path, True)
  return read_config(config.files, config.decls)


def compile_all(sets):
  """Every set, as (config, blocks) pairs.

  `sets` is (path, is_target) pairs: which shape a set compiles to is said by
  the role the run gives it, see read_config_file. A set that is not the target
  is compiled against the target's own blocks as well as the vocabulary of the
  embedding, see target_blocks.
  """
  vocab = read_vocabulary(VOCAB_FILES,
                          [(NATIVE_DEFS_TARGET, natives()[1])])
  macros = read_macros(MACRO_FILES)
  configs = [read_config_file(p, t) for p, t in sets]
  check_distinct(configs)
  target = target_blocks(sets)
  return [(c, compile_config(c, vocab if c.is_target else vocab.extended(target),
                             macros))
          for c in configs]


# -----------------------------------------------------------------------------
# Checking what a compiled set has to satisfy
# -----------------------------------------------------------------------------

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
        report.error('%s: block %s uses %s, which block %s defines later'
                     % (name, sym, u, blocks[owner[u]][0]))
        bad += 1
  return bad


def check_current(text, path):
  """Whether the file at path holds what compiling writes.

  This is what says a generated file is current, which a tree where the
  configuration changed after the last run is not; the fix either way is to
  run the compiler. A file that is not there at all has simply never been
  written, which a fresh checkout has none of, so it is said apart rather
  than read.
  """
  if not os.path.exists(path):
    state, bad = 'missing', 1
  elif read_text(path) == text:
    state, bad = 'current', 0
  else:
    state, bad = 'stale', 1
  return state, bad


def written(blocks, config):
  """What compiling one set writes, in the order it is written: the signature
  in the deep embedding that the model-smt stage reads, and the clauses the
  lean-meta stage appends to the Lean it writes."""
  return ((render(blocks, config), config.target, '%d blocks' % len(blocks)),
          (render_lean(config), config.lean_target,
           '%d clauses' % len(config.clauses)))


def render(blocks, config):
  head = ['\n'.join(l for e in aggregates().values() for l in e.lines())]
  said = head_lines(config, blocks)
  if said:
    head.append('\n'.join(said))
  return (header(config) + AGGREGATE_MANIFEST + '\n;\n'.join(head)
          + '\n\n'
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


NATIVE_GENERATED = """\
GENERATED FILE -- do not edit.

Compiled from %s by tools/eoc/sem_compile.py, which is where a
definition of the layer is to be changed or added.

The layer is what the generated %s is allowed to call that the compiler
does not write itself. A block runs from its `$native` line to the next one
and is the unit the %s stage keeps or drops.

The line says everything the stage has to know about the block:

  $native <name> <needs> <calls>...

<name> is what the block defines and what a signature may reach; whatever
else its text defines has no name here and so is private to it. <needs> is
the narrowest scope the block can come out in, which is the one its own text
names. <calls> is the rest of the layer its text names, which is what the
stage takes the closure over, so that it is given the edges rather than the
text to find them in.

One further line, `$native-keep <name>...`, names the blocks kept whatever an
input reaches, which are the ones the resources of the stage name themselves.
See ethos::NativeLayer.
"""


def render_native(layer, config):
  """The native layer as the file its stage reads.

  A block is what one entry says under the layer's implementation attribute,
  under the name it declares, opened by a line that carries what the stage has
  to know about it: the name, the scope it needs, and what it calls. What is
  kept whatever an input reaches is a line of its own, since it is about the
  layer rather than about a block. See NATIVE_GENERATED.
  """
  say = lambda text: '\n'.join((layer.comment + ' ' + l).rstrip()
                               for l in text.split('\n'))
  out = [say(NATIVE_GENERATED % (named(config.path), layer.lang, layer.stage))]
  kept = [n for e in config.natives if e.keep for n in e.names]
  if kept:
    out.append('%s $native-keep %s' % (layer.comment, ' '.join(kept)))
  for e in config.natives:
    doc = '\n'.join((layer.comment + ' ' + d).rstrip() for d in e.doc)
    # The comment an entry carries stands under the line that opens the block
    # rather than over it, so that everything under that line is the block and
    # a block that is dropped takes what is said about it with it.
    out.append('%s $native %s %s%s\n%s%s'
               % (layer.comment,
                  ' '.join(e.names),
                  e.needs,
                  ''.join(' ' + d for d in e.deps),
                  doc + '\n' if doc else '',
                  e.text))
  return '\n\n'.join(out) + '\n'


class Native:
  """One entry of the native layer: what it defines, what it needs in scope,
  the Lean it is, and whether it is kept whatever an input reaches."""

  def __init__(self, names, needs, text, doc, keep):
    self.names = names
    self.needs = needs
    self.text = text
    self.doc = doc
    self.keep = keep
    # What this entry calls, which native_deps fills in once every name is
    # known: an entry is written before what it calls is read.
    self.deps = []


# A type of the SMT-LIB value embedding as the Lean backend spells it, which
# is the only part of the embedding that layer names today.
SMTM_NAME = re.compile(r"\bSmt[A-Z][A-Za-z0-9_]*")

# A datatype of the embedding as the SMT-LIB backend spells one: the sorts
# that plugins/smt_meta/smt_meta.smt2 declares together, under the prefix each
# level of the embedding is written with.
EMBED_NAME = re.compile(r"\b(eo|sm|tsm|vsm|msm|ssm)\.")

# A name as Lean writes one. The trailing characters are the ones that layer
# uses -- native_re_prefix_match_len? -- so a name cut short here would be an
# edge the stage never hears about.
LEAN_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'?!]*")

# A symbol as SMT-LIB writes one, which is what the names of that layer are
# spelled with: int.to_nat, nat.+, /_by_zero_id.
SMT_NAME = re.compile(r"[A-Za-z0-9~!@%^&*_+=<>.?/-]+")


def lean_needs(text):
  """The narrowest scope a block of the Lean layer can come out in.

  A block that names a type of the SMT-LIB value embedding cannot be written
  above the module that declares them, and one that names none of them wants
  nothing but Lean itself. That is what its Lean says, so it is read off the
  text rather than declared beside it: an annotation can drift from the text
  it is about, and the text cannot drift from itself.
  """
  return 'Smtm' if SMTM_NAME.search(text) else 'SmtEval'


def vc_needs(text):
  """The narrowest scope a block of the SMT-LIB layer can come out in.

  A verification condition is one file rather than a tree of modules, but it
  declares the datatypes of the embedding partway down it, so a block that
  names one of them cannot stand above that point and a block that names none
  of them can stand where SMT-LIB alone is what is in scope. Read off the
  text for the same reason as above.
  """
  return 'Embed' if EMBED_NAME.search(text) else 'Vc'


def native_deps(layer, natives):
  """Fill in what each entry of the layer calls.

  The text an entry is says what it calls by naming it, so the edges are read
  off that text -- there is nowhere else they are written -- and reading them
  here is what leaves the stage the closure rather than the text. A name the
  layer does not declare is one of the language's own and is no edge.
  """
  declared = {n for e in natives for n in e.names}
  for e in natives:
    named = declared.intersection(layer.token.findall(e.text))
    e.deps = sorted(named.difference(e.names))


class Layer:
  """One native layer: the set that says what a backend's generated text is
  allowed to call and no compiler writes, and how the file its stage reads is
  written.

  The two are the same thing said twice, in Lean and in SMT-LIB, so what is
  said about a block -- the scope it needs, what it calls, whether it is kept
  -- is worked out the same way for both and only the language differs. What
  differs is here: which attribute the text stands under, how a comment and a
  name are spelled, and where a block can come out.
  """

  def __init__(self, path, target, attr, comment, lang, stage, spell, needs,
               token):
    # The set, and what it compiles to.
    self.path, self.target = path, target
    # The attribute the text of a block stands under, and the language it is.
    self.attr, self.lang, self.stage = attr, lang, stage
    # What opens a comment in that language, which is what a line the stage
    # reads is written behind.
    self.comment = comment
    # How the generated text spells the name an entry declares.
    self.spell = spell
    # The narrowest scope a block can come out in, read off its text.
    self.needs = needs
    # What a name looks like in that language, see native_deps.
    self.token = token


LAYERS = (
    # The Lean backend names a native with the prefix the embedding gives it,
    # which an entry is written without: `ite` here is what `"ite"` names in a
    # set and what the compiler answers with native_ite.
    Layer(NATIVE_CONFIG, NATIVE_TARGET, 'lean-impl', '--', 'Lean',
          'lean-meta', lambda n: 'native_' + n, lean_needs, LEAN_NAME),
    # The SMT-LIB backend forwards the name itself, so an entry is written
    # under the name a set names it by.
    Layer(VC_CONFIG, VC_TARGET, 'smt-impl', ';', 'SMT-LIB', 'smt-meta',
          lambda n: n, vc_needs, SMT_NAME),
)


def compile_native(layer):
  """Read a native layer, which compiles to its own language and nothing
  else."""
  path = layer.path
  config = Config(path, sem_target.NATIVE_SET, [path],
                  list(itertools.takewhile(lambda l: l.startswith(';'),
                                           read_text(path).split('\n'))),
                  False)
  config.natives = []
  for b in read_config([path], config.decls):
    for e in b.entries():
      if not e.has(layer.attr):
        die('%s: a native says what it is under :%s' % (path, layer.attr))
      text = e.get(layer.attr).val
      # Where a block comes out is what an input reaches, so its text is read
      # by whoever reads the SMT-LIB side as readily as by whoever reads the
      # Eunoia one and may not name either side.
      if 'Eunoia' in text:
        die('%s: the native %s names Eunoia, which a block may not: it comes '
            'out wherever the compilation of an input reaches it'
            % (path, e.name))
      config.natives.append(Native([layer.spell(e.name)],
                                   layer.needs(text),
                                   text,
                                   [d[1:].strip() for d in e.doc],
                                   e.has('keep')))
  native_deps(layer, config.natives)
  return config


def compile_to_files(sets=SHIPPED, out_dir=None):
  """Compile each set and write what it compiles to, where it changed.

  This is what tools/eoc/driver.py calls before the model-smt stage. `sets` is
  (path, is_target) pairs, see compile_all. It gives back what each set
  compiled to -- its signature in the deep embedding and its termination
  clauses, in that order -- so the caller need not know the layout.
  """
  out = {}
  # The natives of the embedding, which every set is compiled against and no
  # option names another of.
  for text, target in zip(natives()[1:], (NATIVE_DEFS_TARGET, EO_DEFS_TARGET)):
    if out_dir is not None:
      target = os.path.join(out_dir, os.path.basename(target))
    write_if_changed(text, target)
  # A native layer is one set and a fixed one, so both are compiled whatever a
  # run names, see LAYERS.
  for layer in LAYERS:
    target = layer.target
    if out_dir is not None:
      target = os.path.join(out_dir, os.path.basename(target))
    write_if_changed(render_native(layer, compile_native(layer)), target)
  for config, blocks in compile_all(sets):
    target, lean_target = config.target, config.lean_target
    if out_dir is not None:
      target = os.path.join(out_dir, os.path.basename(target))
      lean_target = os.path.join(out_dir, os.path.basename(lean_target))
    write_if_changed(render(blocks, config), target)
    write_if_changed(render_lean(config), lean_target)
    out[config.path] = (target, lean_target)
  return out


def main():
  ap = argparse.ArgumentParser(
      description='Compile the configuration of the model-smt signatures.')
  ap.add_argument('configs', nargs='*', metavar='CONFIG',
                  help='a set the tool ships with; both by default')
  ap.add_argument('--semantics', action='append', default=[],
                  metavar='CONFIG',
                  help='the central file of the semantics of an input')
  ap.add_argument('--smt-semantics', action='append', default=[],
                  metavar='CONFIG',
                  help='the central file of an SMT-LIB semantics, i.e. of a '
                       'set that is the target of the compilation')
  ap.add_argument('--out-dir', default=None,
                  help='write the generated files here instead')
  ap.add_argument('--check', action='store_true',
                  help='say whether the generated files are current rather '
                       'than writing them')
  a = ap.parse_args()
  # Which shape a set compiles to is said by the role a run gives it, and the
  # option that names a set is what gives it one; a set named on its own has
  # none to be given, so only the shipped ones, whose roles are fixed, may be.
  sets = []
  for p in a.configs:
    role = role_of(p)
    if role is None:
      die('%s is not a set the tool ships with, so which shape it compiles to '
          'has to be said: name it with --semantics or --smt-semantics' % p)
    sets.append((p, role))
  sets += [(p, False) for p in a.semantics]
  sets += [(p, True) for p in a.smt_semantics]
  sets = sets or list(SHIPPED)
  # What the sets are named by in a line of the log: the directory they share
  # where they share one, so that a line names the file rather than the way to
  # it, see report.rel.
  home = os.path.dirname(os.path.commonprefix(
      [os.path.dirname(os.path.abspath(p)) + os.sep for p, _ in sets]))
  named_sets = [report.rel(p, home) for p, _ in sets]
  width = max(len(n) for n in named_sets)
  if a.check:
    report.step('Checking the generated signatures against %s'
                % report.rel(home))
    bad, done = 0, []
    for config, blocks in compile_all(sets):
      bad += check_order(blocks, report.rel(config.target),
                         config.decls.helper_prefixes()
                         + config.decls.constructor_prefixes())
      for text, target, what in written(blocks, config):
        state, wrong = check_current(text, target)
        done.append((report.rel(target), state, None if wrong else what))
        bad += wrong
    entries, text, eo_text = natives()
    for what, target in ((text, NATIVE_DEFS_TARGET), (eo_text, EO_DEFS_TARGET)):
      state, wrong = check_current(what, target)
      done.append((report.rel(target), state,
                   None if wrong else '%d natives' % len(entries)))
      bad += wrong
    for layer in LAYERS:
      ncfg = compile_native(layer)
      state, wrong = check_current(render_native(layer, ncfg), layer.target)
      done.append((report.rel(layer.target), state,
                   None if wrong else '%d natives' % len(ncfg.natives)))
      bad += wrong
    at = max(len(n) for n, _, _ in done)
    for name, state, what in done:
      report.state(name, state, what, width=at)
      if what is None:
        report.error('%s is %s; run %s to write it'
                     % (name, state, report.rel(__file__)))
    sys.exit(1 if bad else 0)
  report.step('Compiling semantics under %s' % report.rel(home))
  entries, text, eo_text = natives()
  for what, target, src in ((text, NATIVE_DEFS_TARGET, NATIVES_CONFIG),
                            (eo_text, EO_DEFS_TARGET, EO_CONFIG)):
    ntarget = (os.path.join(a.out_dir, os.path.basename(target))
               if a.out_dir is not None else target)
    changed = write_if_changed(what, ntarget)
    report.item(named(src), report.rel(ntarget),
                '%d natives%s' % (len(entries),
                                  '' if changed else ', unchanged'),
                width=width)
  for layer in LAYERS:
    ncfg = compile_native(layer)
    ntarget = (os.path.join(a.out_dir, os.path.basename(layer.target))
               if a.out_dir is not None else layer.target)
    nchanged = write_if_changed(render_native(layer, ncfg), ntarget)
    report.item(report.rel(layer.path), report.rel(ntarget),
                '%d natives%s' % (len(ncfg.natives),
                                  '' if nchanged else ', unchanged'),
                width=width)
  for (config, blocks), name in zip(compile_all(sets), named_sets):
    for text, target, what in written(blocks, config):
      if a.out_dir is not None:
        target = os.path.join(a.out_dir, os.path.basename(target))
      changed = write_if_changed(text, target)
      report.item(name, report.rel(target),
                  what if changed else '%s, unchanged' % what, width=width)
    report.step(summary(config), 2)


if __name__ == '__main__':
  main()
