#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"
mkdir -p runs/MBPP-153-tests-harness-translate

venv/bin/python translate_test_cases.py \
  --input-folder MBPP-153-tests \
  --input-dir input \
  --output-dir translated-harnesses \
  --provider openai \
  --model gpt-5.4-mini \
  --signature-map output/MBPP-DFY-153-fixed-gpt-5.2-temp0.2-2026-06-23/signature_map.json \
  --test-harness \
  --resume \
  --checkpoint-every 10 \
  > runs/MBPP-153-tests-harness-translate/run.log 2>&1
