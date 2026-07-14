#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"
mkdir -p runs/MBPP-153-tests-harness-translate

venv/bin/python translate_test_cases.py \
  --input-folder MBPP-153-tests \
  --input-dir input \
  --output-dir translated-harnesses \
  --provider openai \
  --model gpt-5.4-mini \
  --signature-map "${SIGNATURE_MAP:-output/MBPP-DFY-153-fixed/signature_map.json}" \
  --test-harness \
  --resume \
  --checkpoint-every 10 \
  > runs/MBPP-153-tests-harness-translate/run.log 2>&1
