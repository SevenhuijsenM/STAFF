# Public gpt-5.5 Results

This folder contains a sanitized snapshot of the `MBPP-DFY-153-fixed-gpt55-full` run of STAFF.
It is meant to make the main results and the generated artifacts easy to inspect and cite without exposing local workspace details.

## What is included

- `generated/` with the 130 final generated C outputs
- `non_verifying/` with the 31 generated C files that did not verify
- `analysis/summary/summary.md`
- `analysis/summary/summary.json`
- `analysis/figures/status_counts.svg`
- `analysis/figures/proof_gap_profile.svg`
- `translation_report.md`
- `metrics.json`
- `signature_map.json`
- `untranslated_files.txt`

## What was excluded

- raw traces
- raw pipeline dumps
- behavioral validation intermediates
- mutation-testing intermediates
- any files with absolute machine-specific paths

## Tool versions

The published snapshot was produced with the following toolchain:

- LLM: `gpt-5.5`
- Dafny: `4.11.0`
- Frama-C: `32.0 (Germanium)`
- GCC: `13.3.0`
- Python: `3.12.3`
- DexTool: `DextoolVersion(unknown build)`

## How to read the snapshot

- `generated/` contains the translated ACSL-annotated C artifacts that survived the pipeline.
- `non_verifying/` contains the translated ACSL-annotated C artifacts that were produced but did not pass verification.
- `analysis/summary/` gives a compact run summary.
- `analysis/figures/` contains the figures used in the paper for the main outcome counts and proof-goal profile.
- `signature_map.json` records the translated call signatures used by the harness-validation stage.
- `translation_report.md` provides a more verbose per-file narrative of the run.

## Reproducibility notes

This snapshot is intentionally sanitized. Local absolute paths, transient working directories, and raw intermediate traces are omitted.
The goal is to preserve the run outcome and the generated artifacts while keeping the bundle portable and public.

If you want to recreate the run, use the same benchmark folder, the same model (`gpt-5.5`), and the same tool versions listed above.
