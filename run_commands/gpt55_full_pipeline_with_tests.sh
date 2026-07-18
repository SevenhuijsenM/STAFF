#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

export OPENAI_API_KEY="$(python3 -c 'import json, pathlib; p = pathlib.Path("config.json"); print(json.load(p.open())["openai_api_key"])')"
export MODEL="gpt-5.5"
export TEMP="1.0"
export RUN_LABEL="MBPP-DFY-153-fixed-gpt55-full"
export ENABLE_DIFFERENTIAL_TESTING="1"
export ENABLE_MUTATION_TESTING="1"

./run_full_pipeline_with_tests.sh MBPP-DFY-153-fixed MBPP-153-tests
