#!/usr/bin/env bash
#
# Download the problem corpora. Neither is committed: TPTP is 10 GB unpacked, and the competition problems are
# redistributed rather than authored here.
#
#   ./fetch.sh            both
#   ./fetch.sh tptp       the TPTP library only
#   ./fetch.sh casc       the CASC-J13 competition problems only
#
# Environment:
#   DEST   where to install (default $HOME). `env.sh` looks in $HOME and in this machine's Windows checkout.

set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
dest="${DEST:-$HOME}"
what="${1:-both}"

# Bare `tptp.org`, not `www.tptp.org`: the latter serves the library fine but 404s on /CASC/.
tptp_url="https://tptp.org/TPTP/Distribution/TPTP-v9.3.1.tgz"
casc_url="https://tptp.org/CASC/J13/Problems.tgz"

get() { curl -fSL --retry 3 --retry-delay 5 -o "$1" "$2"; }

# ── the TPTP library ──────────────────────────────────────────────────────────────────────────────
if [ "$what" = both ] || [ "$what" = tptp ]; then
  if [ -d "${TPTP:-}/Problems" ]; then
    echo "TPTP: already installed at $TPTP"
  elif [ -d "$dest/TPTP-v9.3.1/Problems" ]; then
    echo "TPTP: already installed at $dest/TPTP-v9.3.1"
  else
    echo "TPTP: downloading v9.3.1 (~890 MB)"
    get "$dest/TPTP-v9.3.1.tgz" "$tptp_url"
    tar xzf "$dest/TPTP-v9.3.1.tgz" -C "$dest"
    echo "TPTP: installed at $dest/TPTP-v9.3.1 — export TPTP=$dest/TPTP-v9.3.1"
  fi
fi

# ── the CASC-J13 competition problems ─────────────────────────────────────────────────────────────
#
# These are the problems as the competition issued them, which is what E1 must run: 365 of the 400 are
# scrambled relative to the library (implications reversed, conjuncts permuted), and that changes clause order
# and so the search. They still `include('Axioms/…')` from the library, so $TPTP is needed to run them.
#
# The archive is flat per division (`FEQ/AGT007+2.p`), while the manifests hold library-shaped paths
# (`Problems/AGT/AGT007+2.p`). Rather than carry a second manifest for the same 400 problems, the files are
# laid out here in the library's shape, so one manifest serves both and `root=` alone chooses between them:
#
#   ./run.sh e1b root=$dest/casc-j13
#
if [ "$what" = both ] || [ "$what" = casc ]; then
  casc="$dest/casc-j13"
  mkdir -p "$casc"
  if [ ! -f "$casc/Problems.tgz" ]; then
    echo "CASC: downloading J13 Problems.tgz (~33 MB)"
    get "$casc/Problems.tgz" "$casc_url"
  else
    echo "CASC: Problems.tgz already downloaded"
  fi

  # Only the FOF division: FEQ (300, with equality) + FNE (100, without) are the 400 the paper reports. The
  # archive also carries FNN, FNQ, TEQ, TNE and UEQ, which are other divisions and not used here.
  tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
  tar xzf "$casc/Problems.tgz" -C "$tmp" FEQ FNE
  rm -rf "$casc/Problems"
  # A TPTP problem's domain is the first three characters of its name, which is how the library is organised.
  find "$tmp/FEQ" "$tmp/FNE" -name '*.p' | while read -r p; do
    b="$(basename "$p")"
    d="$casc/Problems/${b:0:3}"
    mkdir -p "$d" && cp "$p" "$d/"
  done
  echo "CASC: laid out $(find "$casc/Problems" -name '*.p' | wc -l) problems under $casc/Problems"

  # The point of the layout is that the shipped manifest resolves against it; check that it does, or the
  # experiments would quietly run fewer problems than they report.
  missing=0
  while read -r rel; do
    [ -f "$casc/$rel" ] || { echo "  missing: $rel" >&2; missing=$((missing + 1)); }
  done < "$here/datasets/casc-j13-fof.txt"
  [ "$missing" -eq 0 ] || { echo "CASC: $missing of the manifest's problems are absent" >&2; exit 1; }
  echo "CASC: all $(wc -l < "$here/datasets/casc-j13-fof.txt") manifest problems resolve under $casc"
  echo "CASC: run the competition copies with  ./run.sh <experiment> root=$casc"
fi
