"""How the tools of the pipeline say what they are doing.

One house style, so that a run reads the same whether a line came from the
compiler, from the driver or from a script that calls them, see eoc_step in
tools/eoc/cpc/common.sh for the same thing in shell:

  -- Compiling semantics under tools/eoc/semantics
  --   smt.eos -> tools/eoc/out/smt_defs.eo (219 blocks)

A step of a run is a line under `-- `, and what a step is made of is indented
two spaces further under it. A path is written from the root of the repository,
since a log is usually read somewhere other than the tree that wrote it, and
one that lies outside the tree -- the signature of a calculus that lives beside
it -- is written as it stands.

What went wrong is not a step. It goes to stderr as `error: ...`, which is
where the CI of a caller looks for it, see the checks that run this compiler
from logos and from cvc5.
"""

import os
import sys

# What every line of a step begins with, and what one step of another is
# indented by.
PREFIX = '-- '
INDENT = '  '

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def rel(path, start=None):
  """A path as a log names one.

  From the root of the repository, or from `start` where one is given, and as
  it stands where it lies outside: what is written has to be the same on every
  machine that runs the tool, and a path of another tree cannot be.
  """
  full = os.path.abspath(str(path))
  base = os.path.abspath(str(start)) if start is not None else ROOT
  if full == base:
    return os.path.basename(full) or full
  if os.path.commonpath([full, base]) != base:
    return str(path)
  return os.path.relpath(full, base).replace(os.sep, '/')


def step(text, level=0):
  """One step of a run, or a part of one where level says how deep."""
  print('%s%s%s' % (PREFIX, INDENT * level, text))


def item(source, target, note=None, width=0, level=1):
  """One thing a step did to a file: what it read, what it wrote, and what
  there was of it."""
  arrow = '%-*s -> %s' % (width, source, target) if target else '%s' % source
  step(arrow + (' (%s)' % note if note else ''), level)


def stage(n, total, name, path, gives=True, width=9):
  """One stage of a run: which of how many it is, what it does, and the file it
  leaves behind -- or the file it read, where it leaves none."""
  step('[%d/%d] %-*s %s%s'
       % (n, total, width, name, '-> ' if gives else '   ', rel(path)), 1)


def error(text):
  """What went wrong, where a caller's CI can find it.

  The steps of a run are flushed first, so that the two streams read in the
  order they happened where a caller has piped them into one, as CI does.
  """
  sys.stdout.flush()
  print('error: %s' % text, file=sys.stderr)
  sys.stderr.flush()


def warning(text):
  sys.stdout.flush()
  print('warning: %s' % text, file=sys.stderr)
  sys.stderr.flush()


def state(name, said, note=None, width=0, level=1):
  """What a file was found to be, and what there was of it."""
  step('%-*s %s%s' % (width, name, said, ' (%s)' % note if note else ''),
       level)
