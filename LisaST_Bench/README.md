# LisaST benchmarks

Everything needed to reproduce the paper's tables. Design in [`../CPPpaper/content.md`](../CPPpaper/content.md),
build notes in [`../CPPpaper/benchmark-implementation.md`](../CPPpaper/benchmark-implementation.md).

Runs on Linux under bash; on Windows use WSL, since StarExec is Ubuntu and so is most of the audience.

## Setup

Needs a JDK 21, sbt 2.0.0, and a TPTP v9.3.1 installation. `env.sh` puts a JDK and sbt from `$HOME/tools` on
`PATH` without root, and finds TPTP:

```sh
. ./env.sh          # sets JAVA_HOME, PATH and TPTP
```

`$TPTP` must point at the directory holding `Problems/`. It is needed for every experiment, including the CASC
half: a CASC problem's `include('Axioms/…')` resolves against the library even when the problem itself is run
from somewhere else.

## Running an experiment

```sh
./run.sh e1b                        # every configuration in experiments/e1b.conf
./run.sh e1b limit=3 timeout=20000  # a dry run over three problems
./run.sh e1b dataset=tptp400        # the same experiment over the other half of the benchmark
```

Any `key=value` after the experiment name goes to the harness and overrides the configuration file.

One CSV per configuration (`results/<experiment>-<config>.csv`), one combined (`results/<experiment>.csv`), and
`results/<experiment>.provenance` recording the revision, host, TPTP root and toolchain that produced them.

A configuration whose CSV already exists is skipped, so an interrupted run resumes by being started again;
`FORCE=1` re-runs everything. A configuration that fails does not stop the rest — the failures are listed at
the end and the exit status is non-zero.

`run.sh` calls sbt once to build an assembly jar, then runs each configuration as a plain JVM against it. Not
`sbt runMain` per configuration: sbt 2 is client/server, and a second invocation in the same shell attaches to
the server the first one started, which leaks the environment between configurations and can hang outright.
Running the jar also drops eight sbt startups from the wall clock and exercises the artifact StarExec is given.

| variable | |
|---|---|
| `TPTP` | the TPTP installation. Required |
| `JAR` | a prebuilt assembly jar, to skip the build |
| `HEAP` | maximum heap per configuration, default `10G` |
| `FORCE` | `1` to re-run configurations that already have a CSV |
| `SBT` | the sbt launcher, if not `sbt` on `PATH` |

## Experiments

| file | question |
|---|---|
| `e1a` | how many problems the eight-strategy portfolio solves, uncertified |
| `e1b` | the same certified: what the proof term and the kernel check cost |
| `e2` | clausification variants (prenex, distribution) against each other, clausify-only |
| `e3-time` | what each redundancy mechanism is worth, bounded by wall clock |
| `e3-given` | the same nine, bounded by given-clause count: the inference saving alone |
| `e4` | the ortholattice normaliser, on and off |
| `e5` | SInE axiom selection, on and off |

`e1a` and `e1b` are portfolios: their `.conf` carries a `portfolio` marker, and on StarExec the packager turns
each into ONE configuration that starts its eight strategies together, one pinned to each of the eight cores a
job pair is granted. No worker is killed when another succeeds, so every strategy is measured over the whole
budget, and the portfolio result is the per-problem minimum over eight rows that really did share a wall clock.

`run.sh` ignores the marker and runs the eight one after another: the same per-strategy measurement on a
machine with one core's worth of attention to give, but not a portfolio result, and it does not claim to be.

`e2` and `e3-given` are deterministic and run locally; the timed ones belong on the cluster.

## Datasets

| name | contents |
|---|---|
| `casc-j13-fof` | the 400 problems of the CASC-J13 FOF division: FEQ (300) + FNE (100) |
| `tptp400` | 400 drawn from TPTP v9.3.1, seed 42, disjoint from the CASC 400 |
| `small` | a handful, for dry runs |

`tptp400.csv` carries each problem's form, status, SPC and domain, so the analysis can split the results
without needing `$TPTP`.

Rebuild the manifests with

```sh
cd .. && sbt "lisa-sets/runMain lisa.automation.superposition.bench.BuildDatasets"
```

which redraws `tptp400`, checks every CASC path still resolves, and mirrors both manifests into the classpath
resources the harness loads them from. The outputs are committed, so this is only needed to reproduce the draw
itself.

Problem files are not committed: TPTP is 10 GB and the CASC categories 104 MB.

**The CASC problems are scrambled** — implications reversed, conjuncts permuted — in 365 of the 400, which
changes clause order and so the search. Reproducing the competition means running the copies from the CASC
`Problems.tgz`, not the library's, which is what `root=` is for:

```sh
./run.sh e1b root=/path/to/casc-j13/Problems
```

## Layout

```
env.sh            JDK, sbt and TPTP on PATH
run.sh            runs one experiment
experiments/      one file per experiment, one line per configuration
datasets/         the problem manifests
results/          CSVs and provenance, committed
```

The harness itself is Scala, in `lisa-sets/src/main/scala/lisa/automation/superposition/bench/`.
