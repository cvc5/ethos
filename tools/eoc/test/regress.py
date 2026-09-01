#!/usr/bin/env python3
"""Says whether the pipeline still writes what it wrote.

A run compiles one signature that stands in this tree and takes the digest of
every file it leaves behind, stage files and published artifacts alike, and
compares that with what is checked in. What it guards is the one property a
refactor of the compiler has to have and nothing else here checks: that the
bytes did not move. `sem_compile.py --check` says the configuration is
compiled; the smoke tests of CI say a run finishes; this says it finished the
same way.

  python3 tools/eoc/test/regress.py            say whether the bytes moved
  python3 tools/eoc/test/regress.py --update   take what this run wrote as what
                                               is to be written from now on

A digest says the bytes did not move; it does not say they are well formed.
For the two runs that write a file for a solver, cvc5 reads back what they
wrote -- `--parse-only`, and `--lang=sygus` for the synthesis query -- which is
what catches a verification condition that names a symbol it never declares,
and the only check there is on one. A run uses whatever cvc5 is on PATH and
goes without if there is none, so that a checkout without one still says
whether the bytes moved; --require-cvc5 says a run without it is not a run,
which is what CI passes.

What is checked in is the digest of each file rather than the file, since the
tree checks in no generated artifact at all -- see the `tools/eoc/out/` line of
.gitignore, and `88097405`, which took the artifacts out. A digest says the
same thing in twenty lines, and a run that changed something says which files
it changed; what they now hold is a `--final-out-dir` away.

The digests are of what the pipeline wrote *for this signature under these
semantics*, so a change to `semantics/smt.eos` or to `development-cpc.eos`
moves them, and rightly: a run that means to change the model is a run that
means to change these. Say so with --update, and what the diff of expected.txt
then shows is how much of the output that change reached.

The signature is `tests/Booleans-rules.eo`, compiled for one rule. The
whole-signature path is not covered: no signature in this tree is one the
semantics the tool ships with covers entirely, see `lean --all`, which stops
at the first symbol the semantics says nothing about.
"""

import argparse
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import report  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
DRIVER = os.path.join(ROOT, 'tools', 'eoc', 'driver.py')
EXPECTED = os.path.join(HERE, 'expected.txt')

# The signature a run compiles, the semantics it is compiled under, and the
# rule it is compiled for. One rule of one signature is what the trimming
# leaves the stages the most to do with the least to check in.
INPUT = os.path.join(ROOT, 'tests', 'Booleans-rules.eo')
SEMANTICS = os.path.join(ROOT, 'tools', 'eoc', 'semantics',
                         'development-cpc.eos')
TARGET = 'and_intro'

# What a run does: the subcommand, the arguments it takes after the ones they
# share, and whether it is compiled for one rule or for the whole signature.
RUNS = (('vc', (), True),
        ('sygus', ('--sygus',), True),
        ('lean', (), True),
        ('eo', ('--natives=eo',), False))


# What the driver calls each of them, where that is not the name above: the
# eo-meta backend is the desugar stage answering the natives another way, and
# sygus is the same verification condition asked as a synthesis query.
SUBCOMMAND = {'sygus': 'vc', 'eo': 'desugar'}

# The runs that write a file for a solver, which is what there is for cvc5 to
# read: the other two write Eunoia and Lean, which it has nothing to say about.
SOLVER_RUNS = frozenset(('vc', 'sygus'))


def run(what, extra, target, build_dir, out_dir, cvc5):
  """Compile the signature one way, saying nothing unless it fails.

  `cvc5` is the one to read back what a run wrote, or None to go without. It
  is named rather than left to the driver to find so that a run says which it
  used, and it is passed only to the runs that write something for it.
  """
  read_back = (['--cvc5', cvc5] if cvc5 is not None and what in SOLVER_RUNS
               else ['--skip-cvc5'])
  cmd = [sys.executable, DRIVER, SUBCOMMAND.get(what, what),
         '--build-dir', build_dir, '--final-out-dir', out_dir,
         '--no-build', *read_back, '--semantics', SEMANTICS,
         *extra, INPUT, *( [TARGET] if target else [] )]
  done = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
  if done.returncode != 0:
    sys.stdout.write(done.stdout)
    sys.stderr.write(done.stderr)
    report.error('%s failed; the digests say nothing about a run that did not '
                 'finish' % what)
    sys.exit(1)


def digests(out_dir):
  """What every file the run left behind holds, keyed by its path under the
  output tree and named the way a log names one, i.e. with the one separator
  whatever the machine underneath spells one with."""
  out = {}
  for path, _dirs, files in os.walk(out_dir):
    for f in files:
      full = os.path.join(path, f)
      with open(full, 'rb') as fh:
        out[os.path.relpath(full, out_dir).replace(os.sep, '/')] = \
            hashlib.sha256(fh.read()).hexdigest()
  return out


def read_expected():
  """What is checked in, written the way sha256sum writes one so that a line
  can be checked by hand."""
  out = {}
  if not os.path.exists(EXPECTED):
    return out
  with open(EXPECTED, encoding='utf-8') as fh:
    for line in fh:
      line = line.strip()
      if not line or line.startswith('#'):
        continue
      digest, _, path = line.partition('  ')
      out[path] = digest
  return out


def write_expected(found):
  with open(EXPECTED, 'w', encoding='utf-8') as fh:
    fh.write('# The digest of every file the pipeline writes for the run in\n'
             '# regress.py, which is what says the bytes have not moved. Run\n'
             '# that file with --update to write this one.\n')
    for path in sorted(found):
      fh.write('%s  %s\n' % (found[path], path))


def compare(found, want):
  """What moved, as three lists: what the run no longer writes, what it writes
  that it did not, and what it writes differently."""
  gone = sorted(p for p in want if p not in found)
  new = sorted(p for p in found if p not in want)
  changed = sorted(p for p in found if p in want and found[p] != want[p])
  return gone, new, changed


def main():
  ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
  ap.add_argument('--build-dir', default=os.path.join(ROOT, 'build-eoc'),
                  help='the build directory ethos-eoc stands in')
  ap.add_argument('--out-dir', default=None,
                  help='write the run here instead of in a temporary tree, '
                       'to look at what it wrote')
  ap.add_argument('--update', action='store_true',
                  help='take what this run wrote as what is to be written')
  ap.add_argument('--require-cvc5', action='store_true',
                  help='a run without cvc5 is not a run, rather than one that '
                       'checks the solver files by their digest alone')
  a = ap.parse_args()
  build_dir = os.path.abspath(a.build_dir)
  if not os.path.isfile(os.path.join(build_dir, 'ethos-eoc')):
    report.error('ethos-eoc is not in %s; build it, or name the directory it '
                 'is in with --build-dir' % report.rel(build_dir))
    return 1
  cvc5 = shutil.which('cvc5')
  if cvc5 is None and a.require_cvc5:
    report.error('cvc5 is not on PATH, and --require-cvc5 says a run without '
                 'it is not a run: put one there, or drop the option')
    return 1
  keep = a.out_dir is not None
  out_dir = os.path.abspath(a.out_dir) if keep else tempfile.mkdtemp()
  try:
    report.step('Compiling %s for %s' % (report.rel(INPUT), TARGET))
    if cvc5 is None:
      report.step('no cvc5 on PATH; the solver files are checked by their '
                  'digest alone', 1)
    else:
      report.step('cvc5 reads back what the solver runs write: %s' % cvc5, 1)
    for what, extra, target in RUNS:
      run(what, extra, target, build_dir, out_dir, cvc5)
    found = digests(out_dir)
  finally:
    if not keep:
      subprocess.run(['rm', '-rf', out_dir], check=False)
  if a.update:
    write_expected(found)
    report.item(report.rel(EXPECTED), None, '%d files' % len(found))
    return 0
  want = read_expected()
  if not want:
    report.error('%s holds nothing; run with --update to write it'
                 % report.rel(EXPECTED))
    return 1
  gone, new, changed = compare(found, want)
  for paths, said in ((changed, 'differs'), (new, 'is new'),
                      (gone, 'was not written')):
    for path in paths:
      report.state(path, said, width=max(len(p) for p in want))
  if gone or new or changed:
    report.error('the pipeline no longer writes what it wrote: %d file(s) '
                 'differ, %d new, %d missing; run with --update if that is '
                 'the change you meant to make'
                 % (len(changed), len(new), len(gone)))
    return 1
  report.step('%d files, all as checked in' % len(found), 1)
  return 0


if __name__ == '__main__':
  raise SystemExit(main())
