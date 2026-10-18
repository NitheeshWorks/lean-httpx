#!/usr/bin/env bash
# Native checks of HTTPTransport against a hostile in-process server, then
# the time and memory benchmark, each body in its own process. The bounds
# are in tests/Native.lean (`benchBounds`).
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
lake build native >/dev/null || exit 1
fail=0
./.lake/build/bin/native || fail=1
for c in /big-body /big-chunked; do
  out=$(./.lake/build/bin/native bench "$c"); status=$?
  grep -E '^(RESULT|  FAIL)' <<<"$out"
  if (( status != 0 )); then fail=1; fi
done
exit $fail
