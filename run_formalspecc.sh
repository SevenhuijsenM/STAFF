#!/usr/bin/env bash
set -euo pipefail

if [ $# -lt 1 ]; then
  echo "Usage: ./run_formalspecc.sh <dataset-folder> [model] [temperature] [max_verify_iters] [run_label]"
  echo "Optional env vars: ENABLE_DIFFERENTIAL_TESTING=1, ENABLE_MUTATION_TESTING=1, SKIP_ROUNDTRIP=1, PRETRANSLATED_HARNESS_DIR, DAFNY_EXECUTABLE, DAFNY_BACKEND, C_COMPILER, DTEST_COMMAND_TEMPLATE, DAFNY_BUILD_COMMAND_TEMPLATE, DAFNY_GENERATED_TESTS_COMMAND_TEMPLATE, MUTATION_COMMAND_TEMPLATE, MUTATION_TIMEOUT, MUTATION_REPORT_NAME"
  exit 1
fi

DATASET="$1"
MODEL="${2:-gpt-5.2}"
TEMP="${3:-0.2}"
MAX_VERIFY_ITERS="${4:-3}"
RUN_LABEL="${5:-}"
ENABLE_DIFFERENTIAL_TESTING="${ENABLE_DIFFERENTIAL_TESTING:-1}"
ENABLE_MUTATION_TESTING="${ENABLE_MUTATION_TESTING:-1}"
PRETRANSLATED_HARNESS_DIR="${PRETRANSLATED_HARNESS_DIR:-}"
DAFNY_EXECUTABLE="${DAFNY_EXECUTABLE:-dafny}"
DAFNY_BACKEND="${DAFNY_BACKEND:-cpp}"
DAFNY_GENERATE_TESTS_MODE="${DAFNY_GENERATE_TESTS_MODE:-InlinedBlock}"
DAFNY_TEST_BACKEND="${DAFNY_TEST_BACKEND:-py}"
C_COMPILER="${C_COMPILER:-gcc}"
DTEST_COMMAND_TEMPLATE="${DTEST_COMMAND_TEMPLATE:-}"
DAFNY_BUILD_COMMAND_TEMPLATE="${DAFNY_BUILD_COMMAND_TEMPLATE:-}"
DAFNY_GENERATED_TESTS_COMMAND_TEMPLATE="${DAFNY_GENERATED_TESTS_COMMAND_TEMPLATE:-}"
MUTATION_COMMAND_TEMPLATE="${MUTATION_COMMAND_TEMPLATE:-acsl-mutation-tester --input {translated_c_path} --report {report_file}}"
MUTATION_TIMEOUT="${MUTATION_TIMEOUT:-600}"
MUTATION_REPORT_NAME="${MUTATION_REPORT_NAME:-mutation_report.json}"

if [ -z "${OPENAI_API_KEY:-}" ]; then
  echo "Error: OPENAI_API_KEY is not set"
  exit 2
fi

KEY_LOWER="$(printf '%s' "$OPENAI_API_KEY" | tr '[:upper:]' '[:lower:]')"
for marker in "your_key" "your-api-key" "your_api_key" "replace_with" "sk-..." "<your"; do
  if [[ "$KEY_LOWER" == *"$marker"* ]]; then
    echo "Error: OPENAI_API_KEY appears to be a placeholder value. Set a real API key and retry."
    exit 2
  fi
done

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

if [ -z "$RUN_LABEL" ]; then
  MODEL_SLUG="$(printf '%s' "$MODEL" | tr '/.' '--')"
  RUN_LABEL="${DATASET}-${MODEL_SLUG}-$(date +%Y%m%d-%H%M%S)"
fi

RUN_ARGS=(
  python3 formalspecc_skill.py run
  --dataset "$DATASET"
  --output-root runs
  --output-folder "$RUN_LABEL"
  --model "$MODEL"
  --temperature "$TEMP"
  --max-verify-iters "$MAX_VERIFY_ITERS"
  --checkpoint-every 10
  --dafny-executable "$DAFNY_EXECUTABLE"
  --dafny-backend "$DAFNY_BACKEND"
  --dafny-generate-tests-mode "$DAFNY_GENERATE_TESTS_MODE"
  --dafny-test-backend "$DAFNY_TEST_BACKEND"
  --c-compiler "$C_COMPILER"
)

if [ "$ENABLE_DIFFERENTIAL_TESTING" = "1" ]; then
  RUN_ARGS+=(--enable-differential-testing)
fi
if [ "${SKIP_ROUNDTRIP:-0}" = "1" ]; then
  RUN_ARGS+=(--skip-roundtrip)
fi
if [ "$ENABLE_MUTATION_TESTING" = "1" ]; then
  RUN_ARGS+=(--enable-mutation-testing)
fi
if [ -n "$DTEST_COMMAND_TEMPLATE" ]; then
  RUN_ARGS+=(--dtest-command-template "$DTEST_COMMAND_TEMPLATE")
fi
if [ -n "$DAFNY_BUILD_COMMAND_TEMPLATE" ]; then
  RUN_ARGS+=(--dafny-build-command-template "$DAFNY_BUILD_COMMAND_TEMPLATE")
fi
if [ -n "$DAFNY_GENERATED_TESTS_COMMAND_TEMPLATE" ]; then
  RUN_ARGS+=(--dafny-generated-tests-command-template "$DAFNY_GENERATED_TESTS_COMMAND_TEMPLATE")
fi
if [ -n "$PRETRANSLATED_HARNESS_DIR" ]; then
  RUN_ARGS+=(--translated-harness-dir "$PRETRANSLATED_HARNESS_DIR")
fi
RUN_ARGS+=(--mutation-command-template "$MUTATION_COMMAND_TEMPLATE")
if [ -n "$MUTATION_TIMEOUT" ]; then
  RUN_ARGS+=(--mutation-timeout "$MUTATION_TIMEOUT")
fi
if [ -n "$MUTATION_REPORT_NAME" ]; then
  RUN_ARGS+=(--mutation-report-name "$MUTATION_REPORT_NAME")
fi

"${RUN_ARGS[@]}"

RUN_DIR="runs/$RUN_LABEL"
python3 formalspecc_skill.py all \
  --dataset "$RUN_LABEL" \
  --run-dir "$RUN_DIR" \
  --out-dir "$RUN_DIR/analysis"

echo
echo "Done. Review:"
echo "  $SCRIPT_DIR/$RUN_DIR/analysis/summary/summary.md"
echo "  $SCRIPT_DIR/$RUN_DIR/analysis/figures/status_counts.svg"
echo "  $SCRIPT_DIR/$RUN_DIR/analysis/figures/proof_gap_profile.svg"
