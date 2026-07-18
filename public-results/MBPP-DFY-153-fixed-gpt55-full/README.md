# Public gpt-5.5 results

This folder contains a sanitized snapshot of the `MBPP-DFY-153-fixed-gpt55-full` run.

Included:
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

Excluded on purpose:
- raw traces
- raw pipeline dumps
- behavioral validation intermediates
- mutation-testing intermediates
- any files with absolute machine-specific paths

The intent is to make the main results and the generated artifacts easy to view and cite without exposing local workspace details.
