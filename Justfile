set shell := ["bash", "-euo", "pipefail", "-c"]

profile_input := "benchmarks/satlib/sat/aim-100-1_6-yes1-1.cnf"
profile_output := "profiles/aim-100-1_6-yes1-1.perf"

# Record a SAT profile in perf-script format, which Speedscope imports directly.
profile duration="120" input=profile_input output=profile_output:
    #!/usr/bin/env bash
    set -euo pipefail
    duration="{{ duration }}"
    input="{{ input }}"
    output="{{ output }}"
    dune build --profile benchmark --build-dir _build_profile app/solve.exe
    mkdir -p "$(dirname "$output")"
    raw="$output.data"
    set +e
    perf record -e cpu-clock:u -F 99 --call-graph dwarf,16384 \
      --output "$raw" -- \
      timeout --signal=TERM --kill-after=5s "${duration}s" \
        bash -c 'while "$@"; do :; done' profile-loop \
          _build_profile/default/app/solve.exe bench sat "$input"
    status=$?
    set -e
    if [[ $status -ne 0 && $status -ne 124 ]]; then
      exit "$status"
    fi
    perf script --input "$raw" > "$output"
    echo "Speedscope profile: $output"
