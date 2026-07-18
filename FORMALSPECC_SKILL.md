# formalspecc Local Skill (Project Workflow)

This is a project-local "skill" for running formalspecc and turning run outputs into paper-ready summaries and figures.

## Scope

- Run translation + verification for any dataset folder under `tools/formalspecc/input/`.
- Process run outputs into compact summary files.
- Generate simple SVG figures from run metrics.
- Provide a reusable path to extract numbers for `main.tex` tables.

Important:
- Dataset names are inputs to commands; nothing is hardcoded to D1/D2/D3.
- Do not assume any dataset is final until you run it and confirm outputs.

## Files in this skill

- `tools/formalspecc/formalspecc_skill.py` (main CLI)
- `tools/formalspecc/run_formalspecc.sh` (WSL/Linux wrapper)
- `tools/formalspecc/run_formalspecc.ps1` (PowerShell wrapper)

## Prerequisites

1. Create and activate a virtual environment.
2. Install dependencies from `requirements.txt`.
3. Ensure `frama-c` and `gcc` are installed and available on PATH.
4. Set `OPENAI_API_KEY` in your shell.

## Run the tool

### WSL/Linux

```bash
cd tools/formalspecc
source venv/bin/activate
export OPENAI_API_KEY="YOUR_KEY"
./run_formalspecc.sh <dataset-folder> gpt-5.2 0.2
```

### PowerShell

```powershell
cd tools/formalspecc
.\venv\Scripts\Activate.ps1
$env:OPENAI_API_KEY="YOUR_KEY"
.\run_formalspecc.ps1 -Dataset <dataset-folder> -Model gpt-5.2 -Temperature 0.2
```

### Direct CLI (advanced)

```bash
python formalspecc_skill.py run --dataset <dataset-folder> --output-root runs --model gpt-5.2 --temperature 0.2 --checkpoint-every 10
```

## Process output and make summaries

After a run, summarize results:

```bash
python formalspecc_skill.py summarize --dataset <dataset-folder> --run-dir runs/<dataset-folder> --out-dir analysis/<dataset-folder>/summary
```

Generated summary files:

- `analysis/<dataset>/summary/summary.json`
- `analysis/<dataset>/summary/summary.md`

`summary.md` includes:
- strict successful translation count/rate (verified files),
- compilation rate,
- proof-obligation discharge,
- failure profile for compiled non-verified files,
- round-trip back-translation counts,
- token usage and API cost,
- a short paper-snippet line.

## Create figures from output

Generate SVG charts:

```bash
python formalspecc_skill.py figures --summary-json analysis/<dataset>/summary/summary.json --out-dir analysis/<dataset>/figures
```

Generated figures:

- `analysis/<dataset>/figures/status_counts.svg`
- `analysis/<dataset>/figures/proof_gap_profile.svg`

Or run summarize + figures together:

```bash
python formalspecc_skill.py all --dataset <dataset-folder> --run-dir runs/<dataset-folder> --out-dir analysis/<dataset-folder>
```

## Output paths to track

- Run artifacts: `runs/<dataset-folder>/`
- Per-file traces: `runs/<dataset-folder>/traces/*.trace.json`
- Round-trip traces: `runs/<dataset-folder>/roundtrip/**`
- Analysis artifacts: `analysis/<dataset-folder>/`

## Using in the paper

- Treat `verified_files / total_files` as strict successful translations.
- Use `summary.md` numbers for `main.tex` result tables.
- Keep unresolved cells explicitly marked using `\todo{...}` with specific missing actions.
