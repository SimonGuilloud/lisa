#!/usr/bin/env bash
#
# Run one experiment: one CSV per configuration, one combined CSV, and a record of what produced them.
#
#   ./run.sh <experiment> [key=value]…
#
# Any key=value goes to the harness and overrides the configuration file, so a dry run is
#
#   ./run.sh e1b limit=3 timeout=20000
#
# and the same experiment over the other half of the benchmark is
#
#   ./run.sh e1b dataset=tptp400
#
# A configuration whose CSV already exists is skipped, so an interrupted run resumes by being started again;
# FORCE=1 re-runs everything. A configuration that fails does not stop the others: the failures are listed at
# the end and the exit status is non-zero.
#
# Environment:
#   TPTP   a TPTP installation, the directory containing Problems/. Required, including for the CASC half,
#          whose problems `include('Axioms/…')` from the library even when run from their own root.
#   SBT    the sbt launcher, if not `sbt` on PATH.
#   JAR    a prebuilt assembly jar, to skip the build.
#   HEAP   maximum heap per configuration (default 10G, matching `javaOptions` in build.sbt).
#   FORCE  1 to re-run configurations that already have a CSV.

set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$here/.." && pwd)"
results="$here/results"
SBT="${SBT:-sbt}"
HEAP="${HEAP:-10G}"

# The entry point is one of the dataset objects. Which one only picks a default problem list, and every
# experiment passes its own with `files`.
main="lisa.automation.superposition.bench.FofEvaluation"

experiment="${1:-}"
[ -n "$experiment" ] || { echo "usage: $(basename "$0") <experiment> [key=value]…" >&2; exit 2; }
shift
passthrough=("$@")

[ -n "${TPTP:-}" ] || { echo "run.sh: set TPTP to a TPTP installation" >&2; exit 2; }
[ -d "$TPTP/Problems" ] || { echo "run.sh: no Problems/ under TPTP=$TPTP" >&2; exit 2; }

conf="$here/experiments/$experiment.conf"
[ -f "$conf" ] || { echo "run.sh: no such experiment: $conf" >&2; exit 2; }

# ── the prover, built once, then run as a plain JVM per configuration ─────────────────────────────
#
# Not `sbt runMain` per configuration. sbt 2 is client/server, and a second invocation in the same shell
# attaches to the server the first one started: the environment leaks between them, and a `runMain` after a
# `runMain` can simply hang — 55 minutes with no forked JVM, observed. One `sbt` call up front and plain
# `java` after it makes each configuration an independent process, drops eight sbt startups from the wall
# clock, and runs the very artifact StarExec is given.
if [ -n "${JAR:-}" ]; then
  jar="$JAR"
else
  echo "=== building the assembly jar"
  jar="$( cd "$repo" && "$SBT" -batch "lisa-sets/assembly" | sed -n 's/^\[info\] Built: //p' | tail -1 )"
fi
[ -f "$jar" ] || { echo "run.sh: no assembly jar (got '$jar')" >&2; exit 2; }

# `defaults <key=value>…` in a configuration file applies to every configuration in it, so that switching the
# dataset or the timeout for a whole experiment is one edit rather than eight. Precedence, lowest first:
# defaults, the configuration's own line, then the command line.
defaults="$(sed -n 's/^defaults[[:space:]]\+//p' "$conf" | tr '\n' ' ')"

# `dataset=` on the command line has to be honoured here too, not just passed on, since the driver is what
# turns a dataset name into the list of problems.
override_dataset="$(sed -n 's/.*\bdataset=\([^ ]*\).*/\1/p' <<<"${passthrough[*]:-}")"

mkdir -p "$results"
# The dataset is part of every output name, because the same experiment is run over both halves of the
# benchmark and the two must not overwrite each other — nor, worse, have the second silently skipped by the
# resume check because the first left a file where it looks.
conf_dataset="$(sed -n 's/.*\bdataset=\([^ ]*\).*/\1/p' <<<"$defaults")"
tag="$experiment-${override_dataset:-${conf_dataset:-mixed}}" # `mixed` when the file names a dataset per line
combined="$results/$tag.csv"
: > "$combined"
failed=()

# ── what produced these numbers ───────────────────────────────────────────────────────────────────
#
# A results CSV that cannot be tied to a revision of the prover is not evidence, and by the time a reviewer
# asks, the working tree has moved on. Written before the run, so it survives an interrupted one.
{
  echo "experiment: $experiment"
  echo "date:       $(date -Iseconds)"
  echo "host:       $(uname -sr) $(hostname)"
  echo "git:        $(git -C "$repo" rev-parse HEAD 2>/dev/null || echo unknown)$(git -C "$repo" diff --quiet 2>/dev/null || echo ' (dirty)')"
  echo "tptp:       $TPTP"
  echo "java:       $(java -version 2>&1 | head -1)"
  echo "jar:        $jar"
  echo "heap:       $HEAP"
  echo "command:    $(basename "$0") $experiment ${passthrough[*]:-}"
  [ -n "$defaults" ] && echo "defaults:   $defaults"
  echo "--"
  grep -v '^[[:space:]]*\(#\|$\)' "$conf"
} > "$results/$tag.provenance"

# ── one configuration per non-comment line: a name, then the harness arguments for it ─────────────
while IFS= read -r line; do
  case "$line" in '' | \#* | defaults\ *) continue ;; esac
  name="${line%% *}"
  args="$defaults ${line#* }"

  dataset="${override_dataset:-$(sed -n 's/.*\bdataset=\([^ ]*\).*/\1/p' <<<"$args")}"
  [ -n "$dataset" ] || { echo "run.sh: configuration '$name' names no dataset" >&2; exit 2; }
  # Absolute: the harness forks a JVM per problem, and a relative path would be read against whatever
  # directory that child happens to inherit.
  list="$here/datasets/$dataset.txt"
  [ -f "$list" ] || { echo "run.sh: no such dataset: $list" >&2; exit 2; }
  out="$results/$tag-$name.csv"

  if [ -s "$out" ] && [ "${FORCE:-0}" != "1" ]; then
    echo "=== $experiment / $name — already done, skipping ($(($(wc -l < "$out") - 1)) rows; FORCE=1 to redo)"
  else
    echo "=== $experiment / $name"
    # Recording the failure rather than letting `set -e` abort: one configuration crashing should not throw
    # away the seven that would have run after it, on a matrix that takes hours.
    if ! java "-Xmx$HEAP" -cp "$jar" "$main" \
        files "$list" $args "dataset=$dataset" "config=$name" "out=$out" ${passthrough[*]:+"${passthrough[@]}"}; then
      echo "!!! $experiment / $name failed" >&2
      failed+=("$name")
      continue
    fi
  fi

  # The first configuration contributes the header, the rest only their rows.
  if [ -s "$combined" ]; then tail -n +2 "$out" >> "$combined"; else cat "$out" >> "$combined"; fi
done < "$conf"

echo
# The header only exists if some configuration contributed one, so do not subtract it from an empty file.
rows=$(wc -l < "$combined"); [ "$rows" -gt 0 ] && rows=$((rows - 1))
echo "combined: $combined ($rows rows)"
echo "recorded: $results/$tag.provenance"
if [ ${#failed[@]} -gt 0 ]; then
  echo "failed configurations: ${failed[*]}" >&2
  exit 1
fi
