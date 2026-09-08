#!/usr/bin/env bash
#
# Build the StarExec solver package: LisaST_Bench/starexec/lisaST.tgz
#
#   ./build.sh            build it
#   SLIM=1 ./build.sh     leave out the three giant axiom files (see "axioms" below)
#   HEAP_MB=122880 ./build.sh  the memory to assume when StarExec does not say (default 122880)
#   CONFIGS="e2_rewrite e1b" ./build.sh   ship only these configurations, for a dry run
#
# HEAP_MB is a protocol choice, not a safety net; it is used only when a job sets no memory limit. It decides
# results rather than only speed: the clausifier's safety valve trips at 90% of max heap, so a larger heap
# genuinely solves problems a smaller one cannot. The default is the CASC-J13 limit -- its rules cap a solver
# at 128 GiB -- and the job's own `mem` should normally supply the real figure instead.
#
# ── what a job pair is given, and what the scripts do with it ─────────────────────────────────────
#
# runsolver invokes each pair as `--cores 0-7 -C <cpu> -W <wall> -M <mem_mb>`, so a pair has EIGHT cores and
# one memory allowance covering the whole process tree. That is the hardware CASC ran on, and it decides the
# shape of the package:
#
#   * The E1 portfolio is one configuration that starts its eight strategies together, each pinned to a core
#     of its own with `taskset`, each with an eighth of the memory allowance (capped at the 12 GiB a CASC
#     worker had). Give such a job `mem=128` so that the eight heaps fit.
#
#   * Every other configuration is single-threaded and pins itself to ONE core, so that its CPU time equals
#     its wall clock and 180 s of wall clock is 180 s of CPU on one core -- exactly one portfolio worker's
#     allowance, which is what makes the two comparable. Without the pin a JVM's GC and JIT threads accrue
#     CPU on the other seven cores, and a CPU limit set to the wall clock kills the run early. Give such a
#     job `mem=16`, which leaves the 12 GiB heap after the JVM's non-heap reservation.
#
# ── the archive StarExec expects ──────────────────────────────────────────────────────────────────
#
#   bin/starexec_run_<config>   one per experiment configuration; $1 = problem, $2 = preserved output dir
#   bin/starexec_common.sh      the limit arithmetic and node reporting they share
#   bin/lisa.jar                the assembly, all of Lisa
#   bin/Axioms/                 the axiom files the problems `include`
#
# Needs $TPTP (for the axioms) and a JDK/sbt on PATH; ../env.sh provides both.

set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
bench="$(cd "$here/.." && pwd)"
repo="$(cd "$bench/.." && pwd)"
main="lisa.automation.superposition.bench.FofEvaluation"
heap_mb="${HEAP_MB:-122880}"  # only a fallback: what to assume when the job sets no memory limit

if [ -z "${TPTP:-}" ]; then
  # shellcheck source=/dev/null
  . "$bench/env.sh" >/dev/null
fi
[ -d "${TPTP:-}/Axioms" ] || { echo "set TPTP to a TPTP installation (needs Axioms/)" >&2; exit 1; }

stage="$(mktemp -d)"
trap 'rm -rf "$stage"' EXIT
mkdir -p "$stage/bin"

# ── the solver ────────────────────────────────────────────────────────────────────────────────────
echo "=== building the assembly jar"
jar="$( cd "$repo" && "${SBT:-sbt}" -batch "lisa-sets/assembly" | sed -n 's/^\[info\] Built: //p' | tail -1 )"
[ -f "$jar" ] || { echo "no assembly jar (got '$jar')" >&2; exit 1; }
cp "$jar" "$stage/bin/lisa.jar"

# ── the axioms ────────────────────────────────────────────────────────────────────────────────────
#
# A StarExec node has no TPTP installation, and the competition problems `include('Axioms/…')`. Rather than
# depend on benchmark dependencies (which need a community leader) or pre-expand every problem with `tptp4X`
# (which duplicates shared axioms across problems), the axioms the problems actually reach travel inside the
# package and the run scripts point $TPTP at it. Only what is referenced: 1231 files, not the library's 10 GB.
#
# Three of them are most of the weight — CSR002+4 (71 MB), NLP001+0 (67 MB), BIO001+0 (26 MB) — and the
# problems using them are the ones that are unsolvable or unparseable anyway, so SLIM=1 drops them and takes
# the package from ~243 MB to ~79 MB.
echo "=== collecting axioms"
# `grep` exits non-zero on a problem with no `include`, which under `set -e` would end the scan silently, so
# every step here tolerates finding nothing. Both manifests are scanned: the two halves of the benchmark draw
# on different axiom files.
: > "$stage/axioms.list"
for manifest in "$bench"/datasets/casc-j13-fof.txt "$bench"/datasets/tptp400.txt; do
  [ -f "$manifest" ] || continue
  while read -r rel; do
    f="$TPTP/$rel"
    [ -f "$f" ] || continue
    grep -ohE "include\([^)]*\)" "$f" 2>/dev/null | sed "s/include(.//;s/.).*//" >> "$stage/axioms.list" || true
  done < "$manifest"
done
sort -u -o "$stage/axioms.list" "$stage/axioms.list"

slim_out=0
mkdir -p "$stage/bin/Axioms"
while read -r a; do
  src="$TPTP/$a"
  [ -f "$src" ] || continue
  if [ "${SLIM:-0}" = "1" ] && [ "$(stat -c%s "$src")" -gt 10000000 ]; then slim_out=$((slim_out + 1)); continue; fi
  mkdir -p "$stage/bin/$(dirname "$a")"
  cp "$src" "$stage/bin/$a"
done < "$stage/axioms.list"
kept=$(find "$stage/bin/Axioms" -type f | wc -l)
echo "    $kept of $(wc -l < "$stage/axioms.list") referenced axiom files, $(du -sh "$stage/bin/Axioms" | cut -f1); $slim_out omitted as over 10 MB"

# ── the prelude every run script shares ───────────────────────────────────────────────────────────
#
# Written literally (a quoted heredoc), with the one build-time constant substituted afterwards, so that the
# variables below are read on the node and not here.
cat > "$stage/bin/starexec_common.sh" <<'COMMON_EOF'
# Sourced by every starexec_run_* script. Expects $here (the package's bin/), $problem ($1) and $out ($2).
# Sets $mem_mb, $node_mb, $budget (ms), $core_list, $ncores and the `pin` helper, and writes the node dumps.

mkdir -p "$out"

# StarExec's limits, defended against absence *and* against zero. `${VAR:-default}` substitutes only when a
# variable is unset or empty, so a `STAREXEC_MAX_MEM` of literally 0 — which is what a job with no memory
# limit reports — fell through it and produced `-Xmx-512m`, which the JVM rejects before running anything at
# all. It is in MEGABYTES, not bytes: a job created with mem=12 reports 12288. Reading it as bytes asked for a
# 125 GB heap inside a 12 GB limit, and the JVM refused to start.
mem_mb=${STAREXEC_MAX_MEM:-0}
[ "$mem_mb" -lt 1024 ] && mem_mb=@HEAP_MB@
# Never assume more than the machine has: an allowance the node cannot back gets the JVM OOM-killed part way
# through a run, which looks like a solver failure rather than a misconfiguration.
node_mb=$(( $(awk '/^MemTotal:/ {print $2}' /proc/meminfo 2>/dev/null || echo 0) / 1024 ))
[ "$node_mb" -gt 4096 ] && [ "$mem_mb" -gt $(( node_mb - 4096 )) ] && mem_mb=$(( node_mb - 4096 ))

secs=${STAREXEC_WALLCLOCK_LIMIT:-0}
[ "$secs" -lt 10 ] && secs=300            # unset, zero or implausible
# The budget bounds the *search*, and three things still have to happen inside the wall clock after it runs
# out, so the margin covers all three rather than just the last:
#
#   1. The search notices only between given-clause iterations, and one iteration can be seconds long. A
#      worker asked for 175 s reported 175.7 s of search, and one reported over 180 s.
#   2. On the certified path the proof is then reconstructed and kernel-checked, which is not in the budget.
#   3. The harness's own hard cap fires at budget + 5 s, and the portfolio's parent then has to collect eight
#      workers' rows and print a status.
#
# At a 5 s margin the hard cap landed exactly on the wall clock: 4 of 10 dry-run pairs were killed by
# StarExec, and two lost a worker's row. 12 s puts the hard cap at 7 s before the kill.
budget=$(( secs * 1000 - 14000 ))
[ "$budget" -lt 5000 ] && budget=5000

# The cores this pair may use. `nproc` reports the machine and the affinity mask reports the allowance, and
# the two differ: the nodes are 32-core, and runsolver hands each pair `--cores 0-7`. Pinning against this
# list is what makes eight parallel workers a portfolio rather than eightfold oversubscription of one core.
core_list=""
for part in $(taskset -cp $$ 2>/dev/null | sed 's/.*: *//' | tr ',' ' '); do
  case "$part" in
    *-*) i=${part%-*}; while [ "$i" -le "${part#*-}" ]; do core_list="$core_list $i"; i=$((i + 1)); done ;;
    *[0-9]*) core_list="$core_list $part" ;;
  esac
done
core_list="${core_list# }"
ncores=$(printf '%s\n' $core_list | grep -c . || true)
if [ "${ncores:-0}" -lt 1 ]; then core_list=0; ncores=1; fi

# `taskset` is not on every image, and a pin that silently failed would turn the portfolio into eight
# processes fighting over one scheduler without saying so. Resolve it once, into a helper.
if taskset -c "${core_list%% *}" true >/dev/null 2>&1; then pin_ok=yes; else pin_ok=no; fi
pin() { core="$1"; shift; if [ "$pin_ok" = yes ]; then exec taskset -c "$core" "$@"; else exec "$@"; fi; }

# Printed into every pair's log so the paper can state the machines that produced the numbers from the runs
# themselves rather than from documentation. The leading percent keeps each line a TSTP comment.
cpu="$(awk -F: '/^model name/ {print $2; exit}' /proc/cpuinfo 2>/dev/null | sed 's/^ *//')"
echo "% LisaST node: ${cpu:-unknown}, $(nproc 2>/dev/null || echo ?) cores, java $(java -version 2>&1 | head -1)"
echo "% LisaST pair: cores [$core_list] (pinning $pin_ok), ${mem_mb}m of ${node_mb}m, budget ${budget}ms"

# StarExec renames every benchmark to `theBenchmark.p` and passes no variable naming it, and the competition
# copies are header-stripped, so nothing inside the sandbox knows which problem this is. The analysis recovers
# it from the output path instead. Keep a dump of the environment beside the result: if some installation does
# provide the name, this is what will say so.
env | grep -i starexec | sort > "$out/starexec-env.txt" 2>/dev/null || true
{
  echo "host=$(hostname 2>/dev/null)"   # names the machine, which runsolver's fixed `--cores 0-7` otherwise hides
  echo "nproc=$(nproc 2>/dev/null)"
  echo "affinity=$(taskset -cp $$ 2>&1)"
  echo "cores=$core_list"
  echo "pinning=$pin_ok"
  echo "cpuset_v2=$(cat /sys/fs/cgroup/cpuset.cpus.effective 2>/dev/null)"
  echo "cpu_max_v2=$(cat /sys/fs/cgroup/cpu.max 2>/dev/null)"
  echo "mem_max_v2=$(cat /sys/fs/cgroup/memory.max 2>/dev/null)"
  echo "MemTotal=$(awk '/^MemTotal:/ {print $2}' /proc/meminfo 2>/dev/null) kB"
  echo "ulimit_v=$(ulimit -v 2>/dev/null)"
} > "$out/starexec-node.txt" 2>/dev/null || true
COMMON_EOF
sed -i "s/@HEAP_MB@/$heap_mb/" "$stage/bin/starexec_common.sh"

# ── the run scripts ───────────────────────────────────────────────────────────────────────────────
#
# A configuration file carrying a `portfolio` line becomes ONE script that runs all of its lines in parallel;
# every other file becomes one single-threaded script per line. StarExec supplies the budget and the memory
# rather than the configuration file, so `timeout=` and `dataset=` are stripped from the file's own arguments.
# CONFIGS restricts the package to named configurations, for a dry run: `createjob` from the command line runs
# every configuration of every solver in a space, so the only way to run a subset is to ship a subset.
want="${CONFIGS:-}"
count=0

# `-Xmx` is not the whole story: the memory limit is an *address space* rlimit (ulimit -v), and a JVM reserves
# well beyond its heap — a 1 GB compressed class space by default, plus metaspace, code cache, thread stacks
# and GC structures. At 2 GB of margin a 14336m heap under a 16384 MB limit died with "Could not allocate
# compressed class space", so each JVM is given 4 GB of headroom and the class space is capped explicitly.
jvm='-XX:CompressedClassSpaceSize=256m'
skip='^[[:space:]]*($|#|defaults[[:space:]]|portfolio([[:space:]]|$))'

for conf in "$bench"/experiments/*.conf; do
  experiment="$(basename "$conf" .conf)"
  defaults="$(sed -n 's/^defaults[[:space:]]\+//p' "$conf" | tr '\n' ' ')"
  defaults="$(sed -E 's/(^| )(timeout|dataset)=[^ ]*/ /g' <<<"$defaults")"

  if grep -qE '^portfolio([[:space:]]|$)' "$conf"; then
    # ── one script, one pinned worker per line ────────────────────────────────────────────────────
    [ -n "$want" ] && ! grep -qw "$experiment" <<<"$want" && continue
    workers="$(grep -cvE "$skip" "$conf")"
    script="$stage/bin/starexec_run_${experiment}"
    cat > "$script" <<EOF
#!/usr/bin/env bash
# $experiment — parallel portfolio, generated by LisaST_Bench/starexec/build.sh
set -uo pipefail
here="\$(cd "\$(dirname "\$0")" && pwd)"
export TPTP="\$here"
problem="\$1"; out="\$2"
. "\$here/starexec_common.sh"

workers=$workers

# One core and an equal share of the memory each. The pair's whole allowance is what CASC caps a solver at --
# the queue grants about 128 GiB however much the job asks for -- so splitting it eight ways is what the
# competition's own limit implies per worker, and comes to just under 12 GiB. The cap keeps a queue that
# granted more from handing out a heap no competition worker would have had.
heap=\$(( mem_mb / workers - 4096 ))
[ "\$heap" -gt 12288 ] && heap=12288
[ "\$heap" -lt 512 ] && heap=512
# Only when the split leaves a worker with substantially less than that: a job created with too small a \`mem\`
# is a misconfiguration worth shouting about, a queue's own 128 GiB ceiling is not.
[ "\$heap" -lt 8192 ] &&
  echo "% LisaST WARNING: only \${heap}m per worker from \${mem_mb}m — raise the job's mem= (160 asks the maximum)"
[ "\$ncores" -lt "\$workers" ] &&
  echo "% LisaST WARNING: \$ncores cores for \$workers workers — they share cores, so these are not portfolio timings"

# No worker is killed when another succeeds: every strategy runs to the end of the budget, so its row says
# what that strategy did in the time it was actually given. The cores would be idle either way, so this costs
# nothing and buys E1 its per-strategy columns.
i=0
pids=""
launch() {
  name="\$1"; shift
  d="\$out/\$name"
  core="\$(printf '%s\\n' \$core_list | sed -n "\$(( i % ncores + 1 ))p")"
  mkdir -p "\$d"
  pin "\$core" java "-Xmx\${heap}m" $jvm -cp "\$here/lisa.jar" $main one "\$problem" "\$d" \\
    $defaults "\$@" dataset=starexec config=$experiment "problem=\$(basename "\$problem")" "timeout=\$budget" \\
    > "\$d/stdout.txt" 2>&1 &
  echo "% LisaST worker \$name on core \$core, pid \$!"
  pids="\$pids \$!"
  i=\$(( i + 1 ))
}

EOF
    grep -vE "$skip" "$conf" | while IFS= read -r line; do
      printf 'launch %s %s\n' "${line%% *}" "${line#* }"
    done >> "$script"
    cat >> "$script" <<'PORTFOLIO_EOF'

# One status for the pair: the best any worker reached. The workers already map their own verdict onto the
# SZS ontology — a refuted conjecture is a Theorem, a refuted axiom set merely Unsatisfiable — so this ranks
# their answers rather than repeating that reasoning.
rank() {
  case "$1" in
    Theorem | Unsatisfiable | ContradictoryAxioms) echo 4 ;;
    CounterSatisfiable | Satisfiable) echo 3 ;;
    Timeout) echo 2 ;;
    *) echo 1 ;;
  esac
}

# Collected on the way out as well as at the end. The workers stop 5 s before the hard kill, but eight of them
# finishing at once — an e1b worker reconstructs and checks a proof after its search budget expires — can put
# the summary past the deadline, and a pair killed here would report no status at all. On SIGTERM the summary
# still runs, over whatever has arrived; the per-worker CSVs are written by the workers themselves and survive
# either way, so the worst case costs the summary and not the data.
summarise() {
  best=GaveUp
  for s in $(grep -h '^% SZS status' "$out"/*/stdout.txt 2>/dev/null | awk '{print $4}'); do
    [ "$(rank "$s")" -gt "$(rank "$best")" ] && best="$s"
  done
  # One CSV for the pair, one row per worker, so the analysis reads a portfolio pair exactly as it reads a
  # single-threaded one — the `strategy` column is what separates the workers.
  first=yes
  for csv in "$out"/*/result.csv; do
    [ -f "$csv" ] || continue
    if [ "$first" = yes ]; then head -1 "$csv" > "$out/result.csv"; first=no; fi
    tail -n +2 "$csv" >> "$out/result.csv"
  done
  echo "% SZS status $best for $(basename "$problem")"
}
trap 'summarise; exit 0' TERM INT

# Wait for the workers, but not past a deadline of our own. A worker can miss every cooperative stop it is
# given -- its search deadline, the harness's hard cap, and the interrupt after that -- if it is somewhere
# that polls none of them or is thrashing its collector. One such worker used to hold the whole pair until
# StarExec killed the process tree, which cost the run: the other seven had finished and had rows to report.
#
# So: wait until shortly before the wall clock, then stop asking. A straggler gets a SIGTERM, which its
# shutdown hook turns into a `KILLED` row if it is healthy enough to run one, and the summary goes ahead
# either way. The pair then completes with seven good rows and one bad one, instead of being killed outright.
# `SECONDS` counts from when this shell started, which is when the pair started -- the deadline has to be
# measured from there and not from when the wait begins, since by then the eight JVMs are already launched.
while [ "$SECONDS" -lt $(( secs - 5 )) ]; do
  running=no
  for p in $pids; do if kill -0 "$p" 2>/dev/null; then running=yes; break; fi; done
  [ "$running" = no ] && break
  sleep 1
done
for p in $pids; do kill -0 "$p" 2>/dev/null && echo "% LisaST straggler pid $p did not stop; terminating" && kill -TERM "$p" 2>/dev/null; done
sleep 1

trap - TERM INT
summarise

# SIGKILL last, and only after the summary is written. runsolver waits for the whole process tree, not for
# this script, so a worker that ignored the SIGTERM above would keep the pair alive until the wall clock
# killed it -- which is exactly what happened when only the TERM was sent: the summary was complete at 177 s
# and the pair was still recorded as a wall-clock timeout at 183 s. SIGKILL cannot be ignored, so the tree
# ends here and the pair completes with whatever rows the workers managed.
for p in $pids; do kill -0 "$p" 2>/dev/null && kill -KILL "$p" 2>/dev/null; done
exit 0
PORTFOLIO_EOF
    chmod +x "$script"
    count=$((count + 1))
  else
    # ── one single-threaded script per line ───────────────────────────────────────────────────────
    while IFS= read -r line; do
      case "$line" in '' | \#* | defaults\ * | portfolio | portfolio\ *) continue ;; esac
      name="${line%% *}"
      args="$defaults ${line#* }"
      [ -n "$want" ] && ! grep -qw "${experiment}_${name}" <<<"$want" && continue
      script="$stage/bin/starexec_run_${experiment}_${name}"
      cat > "$script" <<EOF
#!/usr/bin/env bash
# $experiment / $name — generated by LisaST_Bench/starexec/build.sh
set -uo pipefail
here="\$(cd "\$(dirname "\$0")" && pwd)"
export TPTP="\$here"
problem="\$1"; out="\$2"
. "\$here/starexec_common.sh"

heap=\$(( mem_mb - 4096 ))
[ "\$heap" -lt 512 ] && heap=512

# Pinned to a single core, like a portfolio worker. The pair is granted eight, but this configuration is
# single-threaded and the point of the bound is comparability: on one core the JVM's own GC and JIT threads
# timeshare with the search instead of running beside it, so the CPU time a run accrues is its wall clock and
# a 180 s budget is the 180 s of CPU one portfolio worker had. Unpinned, the same run charges its collector to
# the other seven cores, and a CPU limit equal to the wall clock kills it early — 180 s of CPU arrived at
# 167 s of wall clock.
pin "\${core_list%% *}" java "-Xmx\${heap}m" $jvm -cp "\$here/lisa.jar" $main one "\$problem" "\$out" \\
  $args "dataset=starexec" "config=${experiment}_${name}" "problem=\$(basename "\$problem")" "timeout=\$budget"
EOF
      chmod +x "$script"
      count=$((count + 1))
    done < "$conf"
  fi
done
echo "=== $count run scripts"

# ── the archive ───────────────────────────────────────────────────────────────────────────────────
out="$here/${OUT:-lisaST}.tgz"
rm -f "$out"
( cd "$stage" && rm -f axioms.list && tar czf "$out" bin )
echo "=== wrote $out ($(du -h "$out" | cut -f1))"
