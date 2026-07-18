# STAFF: ACSL Specification Generation

STAFF is a verifier-guided pipeline for translating Dafny benchmarks into ACSL-annotated C and checking the result with complementary validation steps.

## Quick Usage

```bash
python main.py --input-folder FOLDER --model gpt-5.4-nano --fallback-model gpt-5.2 --temperature 0.2 --checkpoint-every 10 --openai-key YOUR_KEY
```

## What It Does

`formalspecc` translates Dafny specifications into ACSL-annotated C, then runs
verification and validation checks so you can judge translation quality from
multiple angles.

Default checks:

| Check | When it runs | What it tells you |
|------|--------------|-------------------|
| Compilation | Always | Whether the generated C is syntactically valid |
| Frama-C WP/RTE | Always, if Frama-C is available | Whether the translated ACSL discharges as a proof obligation set |
| Behavioral validation | Always attempted | Whether translated test cases agree with the generated C |
| Translated harness validation | When `PRETRANSLATED_HARNESS_DIR` is set | Whether pretranslated C test harnesses still match the translated C outputs |
| Round-trip back-translation | Always attempted | Whether the translated artifact can be translated back to Dafny and compared against the source |
| Mutation testing | Always attempted | Whether the translated ACSL survives an external mutation pass |

## Full Pipeline Setup

To run the whole pipeline locally:

1. Install the Python dependencies with `setup.sh` on WSL/Linux or `setup.bat` on Windows.
2. Install the external verification tools:
   - Dafny, available on `PATH` for source-side checks.
   - GCC or another C compiler used by generated harnesses.
   - Frama-C with WP/RTE for target-side verification.
   - If Frama-C is already installed in an OPAM switch, make sure the switch's `bin` directory is on `PATH` before running the pipeline.
3. Set `OPENAI_API_KEY`.
4. Place the dataset folder under `tools/formalspecc/input/`.
5. If you already translated Dafny test cases to C harnesses, set `PRETRANSLATED_HARNESS_DIR` to that folder.
6. Run the wrapper script for your platform.
7. Review the run folder and the generated analysis files.

The wrappers run the post-translation validation stages by default:

- translated test-case validation is enabled unless you pass `--skip-differential-testing` or set the corresponding wrapper override,
- translated harness validation runs automatically when `PRETRANSLATED_HARNESS_DIR` is set,
- round-trip back-translation is enabled unless you pass `--skip-roundtrip`,
- ACSL mutation testing is enabled unless you pass `--skip-mutation-testing` or set the corresponding wrapper override.

Example WSL/Linux run:

```bash
cd tools/formalspecc
source venv/bin/activate
export OPENAI_API_KEY="YOUR_KEY"
export ENABLE_DIFFERENTIAL_TESTING=1
export ENABLE_MUTATION_TESTING=1
export PRETRANSLATED_HARNESS_DIR="translated-harnesses/MBPP-153-tests"
export DAFNY_EXECUTABLE="/usr/bin/dafny"
export MUTATION_COMMAND_TEMPLATE='acsl-mutation-tester --input {translated_c_path} --report {report_file}'
./run_formalspecc.sh MBPP-DFY-153-fixed gpt-5.5 1.0 3
```

If Frama-C is unavailable, the pipeline still translates files, but the verification gate is skipped and the run is no longer a full end-to-end validation.

## Local Skill Workflow

For a reproducible run + summarize + figures workflow, use:

- `FORMALSPECC_SKILL.md` (step-by-step usage)
- `formalspecc_skill.py` (CLI)
- `translate_test_cases.py` (plain-C Dafny test-case translator)
- `validate_translated_harnesses.py` (post-process translated test-case harnesses against translated C outputs)
- `ACSL-Mutation-Tester` (optional post-translation specification mutation testing hook)
- `run_formalspecc.sh` / `run_formalspecc.ps1` (one-command wrappers)
- `run_reverse_formalspecc.sh` / `run_reverse_formalspecc.ps1` (ACSL-annotated C to Dafny wrappers)

Example:

```bash
python translate_test_cases.py --input-folder MBPP-DFY-153-fixed --model gpt-5.4-mini --output-dir translated-c
```

If you want to run the test-case translation step with OpenRouter instead of the
default OpenAI endpoint, pass the provider and key explicitly:

```bash
python translate_test_cases.py \
  --input-folder MBPP-DFY-153-fixed \
  --provider openrouter \
  --openrouter-key YOUR_OPENROUTER_KEY \
  --model ~openai/gpt-latest \
  --signature-map translated-c/signature_map.json \
  --output-dir translated-c
```

The optional signature map helps the harness generator preserve lengths,
wrappers, and multiple-return conventions when the translated solution changes
its C surface form.

### Options

| Flag | Description | Default |
|------|-------------|---------|
| `--input-folder` | Input folder name | - |
| `--output-folder` | Output folder name | same as input |
| `--provider` | Model provider (`openai` or `openrouter`) | openai |
| `--model` | OpenAI model | gpt-5.2 |
| `--fallback-model` | Retry untranslated files with this model | none |
| `--fallback-temperature` | Temperature for fallback model | same as `--temperature` |
| `--checkpoint-every` | Save intermediate progress every N files | 0 (disabled) |
| `--resume` | Skip files already translated in output folder | false |
| `--temperature` | LLM temperature | 0.7 |
| `--openrouter-key` | OpenRouter API key | none |
| `--openrouter-referer` | Optional `HTTP-Referer` header for OpenRouter attribution | none |
| `--openrouter-title` | Optional `X-OpenRouter-Title` header for OpenRouter attribution | none |
| `--source-lang` | Source language | dafny |
| `--target-lang` | Target language | ACSL |
| `--skip-verification` | Skip Frama-C | false |
| `--no-debug` | Disable debug output | false |
| `--enable-differential-testing` | Run Dafny-to-C behavioral checks | true |
| `--skip-differential-testing` | Disable Dafny-to-C behavioral checks | false |
| `--dafny-executable` | Dafny CLI executable/path | dafny |
| `--dafny-backend` | Dafny backend for validation builds | cpp |
| `--dafny-generate-tests-mode` | Mode for `dafny generate-tests` | InlinedBlock |
| `--dafny-test-backend` | Backend for `dafny test` execution | py |
| `--c-compiler` | C compiler for generated harnesses | gcc |
| `--dtest-command-template` | Command template that emits test vectors JSON | none |
| `--translated-harness-dir` | Directory with pretranslated C test harnesses for end-to-end validation | none |
| `--enable-mutation-testing` | Run ACSL mutation testing after translation | true |
| `--skip-mutation-testing` | Disable ACSL mutation testing after translation | false |
| `--mutation-command-template` | Command template for the mutation-testing tool | none |
| `--mutation-timeout` | Timeout for the mutation-testing command | 600 |
| `--mutation-report-name` | Mutation report filename written by the hook | mutation_report.json |

## Project Structure

```text
FormalSpecC/
|-- src/
|   |-- pipeline.py      # Core pipeline (LLMClient + ACSLPipeline)
|   |-- config.py        # Configuration
|   |-- metrics.py       # Metrics calculator
|   `-- report.py        # HTML reports
|-- prompts.py           # LLM prompts
|-- input/               # Input .dfy files
|-- output/              # Generated .c files
`-- main.py              # Entry point
```

## Output Organization

```text
output/folder/
|-- *.c                   # Verified files (V)
|-- behavioral_validation/ # Optional Dafny/C cross-check artifacts
|-- translated_harness_validation/ # Optional validation against pretranslated C harnesses
|-- roundtrip/            # Optional Dafny back-translation comparison artifacts
|-- mutation_testing/      # Optional ACSL mutation-testing artifacts
|-- non_verifying/         # Compiles but does not verify (~)
`-- non_compiling/         # Does not compile (X)

Each file also gets a `traces/<task>.trace.json` record with structured
entries for `structural_fidelity`, `behavioral_validation`, `roundtrip`, and
`mutation_testing`, plus folder-level translated harness validation when
configured, so downstream scripts can consume the same evidence without
scraping log text.
```

## Optional Behavioral Validation

The pipeline can perform an additional behavioral cross-check between the Dafny
source and the translated C artifact.

The validation stage is adapter-based because Dafny and DTest setups vary
across machines.

What it can do:

1. Verify the Dafny source with the Dafny CLI.
2. Load test vectors from a sidecar file named `<program>.tests.json`, or run a
   user-supplied DTest-style command template to generate that JSON file.
3. Try Dafny's built-in `generate-tests` command and save its output when no custom
   generated-tests command template is supplied.
4. Build the Dafny source to a configured backend, defaulting to `cpp`.
5. Run a generated C harness against the translated C file using those vectors.

Example:

```bash
python main.py \
  --input-folder MBPP-DFY-153-smoke \
  --enable-differential-testing \
  --dafny-executable "C:/path/to/Dafny.exe" \
  --dtest-command-template "my-dtest-adapter --input {dafny_file} --output {vectors_file}" \
  --dafny-build-command-template "dafny build --target:{backend} {dafny_file}"
```

Test vector schema:

- See `examples/differential-tests.schema.json`.
- The current generated C harness supports scalar returns and simple scalar or
  `int*` array parameters.
- For more complex translated C signatures, keep using the adapter mechanism to
  generate a simpler callable surface or extend the harness generator.

---

## Optional Specification Mutation Testing

The pipeline can also invoke an external ACSL mutation-testing pass after a
translated C artifact is produced. This hook wraps the standalone tool in this
repository:

- [ACSL-Mutation-Tester](https://github.com/SevenhuijsenM/ACSL-Mutation-Tester)

The mutation stage receives the translated C file, the original source file, the
resolved work directory, and a report-path placeholder. It is intentionally
post-processing only: translation and Frama-C verification still run first, and
mutation testing acts as an additional robustness signal when available.
The same command template is reused for every translated file; you do not need
to define a separate template per benchmark item.

Example:

```bash
python main.py \
  --input-folder MBPP-DFY-153-smoke \
  --enable-mutation-testing \
  --mutation-command-template "acsl-mutation-tester --input {translated_c_path} --report {report_file}"
```

The command template may use these placeholders:

- `{translated_c_path}`
- `{translated_c_code}`
- `{translated_c_filename}`
- `{source_file}`
- `{source_code}`
- `{work_dir}`
- `{report_file}`

---

## Detailed Setup

1. Run the setup script to create a virtual environment:

### Linux/Mac
```bash
bash setup.sh
```

### Windows
```cmd
setup.bat
```

2. Activate the virtual environment:

### Linux/Mac
```bash
source venv/bin/activate
```

### Windows
```cmd
venv\Scripts\activate
```

3. Install Frama-C for verification if it is not already present:

```bash
# On Ubuntu/Debian
sudo apt-get install frama-c
```

4. Set your OpenAI API key (see Configuration below).

## Configuration

### Option 1: Environment Variable (Recommended)

```bash
export OPENAI_API_KEY=your_api_key_here
```

### Option 2: Command Line

```bash
python3 main.py --openai-key your_api_key_here
```

### Option 3: Config File

Create a `config.json` file (gitignored):

```json
{
  "openai_api_key": "your_api_key_here",
  "default_model": "gpt-5.2",
  "input_dir": "input",
  "output_dir": "output"
}
```

## Usage

Make sure the virtual environment is activated, then run:

### Process a specific folder

Place your source files (`.dfy`, `.java`, etc.) in `input/your_folder/`:

```bash
python main.py --input-folder your_folder --openai-key YOUR_KEY
```

This will:

1. Read files from `input/your_folder/`
2. Translate each file to ACSL
3. Save results to `output/your_folder/`
4. Only save the final version, not intermediate attempts

### Process multiple folders

```bash
python main.py --folders folder1 folder2 folder3
```

### Process all folders in input/

```bash
python main.py --openai-key YOUR_KEY
```

## Reverse Pipeline

The same pipeline can also be run in reverse, using ACSL-annotated C input files and
producing Dafny output files verified with the Dafny CLI.

Example:

```bash
python main.py \
  --input-folder reverse-smoke \
  --input-dir input \
  --output-dir output-reverse \
  --output-folder reverse-smoke-out \
  --model gpt-5.5 \
  --temperature 1.0 \
  --source-lang acsl \
  --target-lang dafny \
  --dafny-executable "C:/path/to/Dafny.exe"
```
