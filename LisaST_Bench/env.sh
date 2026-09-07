# Source this before run.sh to put a JDK and sbt on PATH and point TPTP at the problem library.
#
#   source LisaST_Bench/env.sh && ./LisaST_Bench/run.sh e1b limit=3
#
# On a normal Ubuntu box `apt install openjdk-21-jdk-headless sbt` makes most of this unnecessary; this file
# exists because the toolchain here lives in $HOME, installed without root.

_tools="${LISAST_TOOLS:-$HOME/tools}"

# A JDK: the one in $_tools if present, else whatever is already configured.
if [ -z "${JAVA_HOME:-}" ]; then
  for _jdk in "$_tools"/jdk-*; do
    [ -x "$_jdk/bin/java" ] && { export JAVA_HOME="$_jdk"; break; }
  done
fi
[ -n "${JAVA_HOME:-}" ] && export PATH="$JAVA_HOME/bin:$PATH"

# sbt, likewise.
[ -x "$_tools/sbt/bin/sbt" ] && export PATH="$_tools/sbt/bin:$PATH"

# The TPTP library. Under WSL the Windows installation is reachable through /mnt/c.
if [ -z "${TPTP:-}" ]; then
  for _t in "$HOME/TPTP-v9.3.1" /mnt/c/Users/Simon/Work/TPTP-v9.3.1; do
    [ -d "$_t/Problems" ] && { export TPTP="$_t"; break; }
  done
fi

unset _tools _jdk _t
echo "JAVA_HOME=${JAVA_HOME:-<unset>}"
echo "TPTP=${TPTP:-<unset>}"
echo "sbt=$(command -v sbt || echo '<not on PATH>')"
