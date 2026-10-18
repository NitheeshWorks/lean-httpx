#!/usr/bin/env bash
# Native checks of HTTPTransport against a hostile in-process server, then
# the time and memory benchmark, each body in its own process. The bounds
# are in tests/Native.lean and tests/NativeH2.lean (`benchBounds`).
# HTTP/2 (tests/NativeH2.lean) runs the same way against a hostile h2 server.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
lake build native native2 >/dev/null || exit 1
fail=0
./.lake/build/bin/native || fail=1
for c in /big-body /big-chunked; do
  out=$(./.lake/build/bin/native bench "$c"); status=$?
  grep -E '^(RESULT|  FAIL)' <<<"$out"
  if (( status != 0 )); then fail=1; fi
done
./.lake/build/bin/native2 || fail=1
out=$(./.lake/build/bin/native2 bench); status=$?
grep -E '^(RESULT|  FAIL)' <<<"$out"
if (( status != 0 )); then fail=1; fi
exit $fail
