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

  usage: sem_compile.py [--out-dir DIR] [--check] [--signature CONFIG]
                        [--semantics CONFIG] [CONFIG...]

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
# The file each set stands in. A set is one file: it holds its theories in the
# order their blocks are emitted, one to a section.
CONFIGS = (os.path.join(SEM, 'smt.eos'), os.path.join(SEM, 'development-cpc.eos'))

# The sets the tool ships with, each with its role: whether it is the SMT-LIB
# signature, which is the target of the compilation, rather than the signature
# of an input. The two compile to different things, so a run has to know which
# a set is before it reads a line, and the role is what says so: for these two
# it is fixed here, and for any other set it is said by the option that names
# it, --semantics for a target and --signature for an input -- never by what a
# file is called.
SHIPPED = ((CONFIGS[0], True), (CONFIGS[1], False))

# The native layer of the Lean backend: what the generated Lean is written over
# and no compiler writes. It is one set, and a fixed one -- there is one such
# layer, not one per input -- so it is compiled beside the two above rather
# than named by an option. It stands in the plugin that reads what it compiles
# to, since it is of that backend and of nothing else.
NATIVE_CONFIG = os.path.join(ROOT, 'plugins', 'lean_meta', 'lean.eos')
NATIVE_TARGET = os.path.join(OUT, 'lean_native.lean')

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
-- writes instead. See LeanMetaReduce::placeNativeDefs.
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
    # generated Lean is to be told, and how much of each thing it holds.
    self.clauses = []
    self.counts = {}

  @property
  def name(self):
    return name_of(self.path)

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
  config.counts = counts(blocks)
  return out


def check_distinct(configs):
  """No two sets of one run may write one file.

  Two sets of one role standing in one directory would, since a set outside
  the tool compiles beside itself, see Config._beside; what is written first
  would be read as what was written last, so the run refuses instead.
  """
  seen = {}
  for config in configs:
    t = os.path.realpath(config.target)
    if t in seen:
      die('%s and %s both compile to %s; a set compiles beside itself, so '
          'two of one role cannot stand in one directory'
          % (seen[t], config.name, config.target))
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
  vocab, macros = read_vocabulary(VOCAB_FILES), read_macros(MACRO_FILES)
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


NATIVE_GENERATED = """\
-- GENERATED FILE -- do not edit.
--
-- Compiled from %s by tools/eoc/sem_compile.py, which is where a
-- definition of the layer is to be changed or added.
--
-- The layer is what the generated Lean is allowed to call that the compiler
-- does not write itself. A block runs from `-- $native <name> ...` to the
-- next marker and is the unit the lean-meta stage keeps or drops; the names
-- are what it defines and what a signature may reach, and whatever else its
-- text defines has no name here and so is private to it. A
-- `-- $native-needs <scope>` line opens the section of blocks that need that
-- much of the embedding in scope. See LeanMetaReduce::placeNativeDefs.
"""


def render_native(config):
  """The native layer as the file the lean-meta stage reads.

  A block is what one entry says under :lean-impl, under the names it
  declares; the sections are what :needs says, opened where the scope changes,
  which is the order the set gives them.
  """
  out = [NATIVE_GENERATED % named(config.path)]
  scope = None
  for e in config.natives:
    if e.needs != scope:
      scope = e.needs
      out.append('-- $native-needs %s' % scope)
    doc = '\n'.join(('-- ' + d).rstrip() for d in e.doc)
    out.append('%s-- $native %s\n%s'
               % (doc + '\n' if doc else '', ' '.join(e.names), e.text))
  return '\n\n'.join(out) + '\n'


class Native:
  """One entry of the native layer: what it defines, what it needs in scope,
  and the Lean it is."""

  def __init__(self, names, needs, text, doc):
    self.names = names
    self.needs = needs
    self.text = text
    self.doc = doc


def compile_native(path=NATIVE_CONFIG):
  """Read the native layer, which compiles to Lean and to nothing else."""
  config = Config(path, sem_target.NATIVE_SET, [path],
                  list(itertools.takewhile(lambda l: l.startswith(';'),
                                           read_text(path).split('\n'))),
                  False)
  config.natives = []
  for b in read_config([path], config.decls):
    for e in b.entries():
      if not e.has('lean-impl'):
        die('%s: a native says what it is under :lean-impl' % e.name)
      config.natives.append(Native(
          [e.name],
          e.get('needs').val if e.has('needs') else 'SmtEval',
          e.get('lean-impl').val,
          [d[1:].strip() for d in e.doc]))
  return config


def compile_to_files(sets=SHIPPED, out_dir=None):
  """Compile each set and write what it compiles to, where it changed.

  This is what tools/eoc/driver.py calls before the model-smt stage. `sets` is
  (path, is_target) pairs, see compile_all. It gives back what each set
  compiled to -- its signature in the deep embedding and its termination
  clauses, in that order -- so the caller need not know the layout.
  """
  out = {}
  # The native layer is one set and a fixed one, so it is compiled whatever a
  # run names, see NATIVE_CONFIG.
  native_target = NATIVE_TARGET
  if out_dir is not None:
    native_target = os.path.join(out_dir, os.path.basename(native_target))
  write_if_changed(render_native(compile_native()), native_target)
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
  ap.add_argument('--signature', action='append', default=[],
                  metavar='CONFIG',
                  help='the central file of the signature of an input')
  ap.add_argument('--semantics', action='append', default=[],
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
          'has to be said: name it with --signature or --semantics' % p)
    sets.append((p, role))
  sets += [(p, False) for p in a.signature]
  sets += [(p, True) for p in a.semantics]
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
    ncfg = compile_native()
    state, wrong = check_current(render_native(ncfg), NATIVE_TARGET)
    done.append((report.rel(NATIVE_TARGET), state,
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
  ncfg = compile_native()
  ntarget = (os.path.join(a.out_dir, os.path.basename(NATIVE_TARGET))
             if a.out_dir is not None else NATIVE_TARGET)
  nchanged = write_if_changed(render_native(ncfg), ntarget)
  report.item(report.rel(NATIVE_CONFIG), report.rel(ntarget),
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
