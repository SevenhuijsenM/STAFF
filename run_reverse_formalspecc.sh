#!/usr/bin/env bash
set -euo pipefail

if [ $# -lt 1 ]; then
  echo "Usage: ./run_reverse_formalspecc.sh <dataset-folder> [model] [temperature] [max_verify_iters] [run_label]"
  exit 1
fi

DATASET="$1"
MODEL="${2:-gpt-5.5}"
TEMP="${3:-1.0}"
MAX_VERIFY_ITERS="${4:-1}"
RUN_LABEL="${5:-}"
DAFNY_EXECUTABLE="${DAFNY_EXECUTABLE:-dafny}"

if [ -z "${OPENAI_API_KEY:-}" ]; then
  echo "Error: OPENAI_API_KEY is not set"
  exit 2
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

if [ -z "$RUN_LABEL" ]; then
  MODEL_SLUG="$(printf '%s' "$MODEL" | tr '/.' '--')"
  RUN_LABEL="${DATASET}-${MODEL_SLUG}-reverse-$(date +%Y%m%d-%H%M%S)"
fi

python3 formalspecc_skill.py run \
  --dataset "$DATASET" \
  --output-root runs-reverse \
  --output-folder "$RUN_LABEL" \
  --model "$MODEL" \
  --temperature "$TEMP" \
  --max-verify-iters "$MAX_VERIFY_ITERS" \
  --checkpoint-every 10 \
  --source-lang acsl \
  --target-lang dafny \
  --dafny-executable "$DAFNY_EXECUTABLE"

RUN_DIR="runs-reverse/$RUN_LABEL"
python3 formalspecc_skill.py all \
  --dataset "$RUN_LABEL" \
  --run-dir "$RUN_DIR" \
  --out-dir "$RUN_DIR/analysis"

echo
echo "Done. Review:"
echo "  $SCRIPT_DIR/$RUN_DIR/analysis/summary/summary.md"
