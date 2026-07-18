# STAFF

STAFF is a verifier-guided translation pipeline for converting Dafny benchmarks into ACSL-annotated C code and checking the results with multiple complementary validation steps. This repository contains the public-facing scripts, legacy material kept for provenance, and a sanitized results bundle for the `gpt-5.5` full run.

## What is public here

- The translation and validation scripts used for the pipeline.
- A sanitized result snapshot at `public-results/MBPP-DFY-153-fixed-gpt55-full`.
- The public dataset and helper scripts are organized under the `STAFF-Dataset` and `STAFF-Scripts` folders.

## Public results

The `public-results/MBPP-DFY-153-fixed-gpt55-full` folder contains a cleaned summary of the full `gpt-5.5` run, including:

- a short human-readable summary,
- a sanitized JSON summary,
- the main result figures,
- and a short note explaining what was intentionally left out.

## Running the pipeline

The repository still includes the existing helper scripts for reproducing the workflow locally. The main entry points are:

- `run_commands/gpt55_full_pipeline_with_tests.sh`
- `run_harness_translation.sh`
- `STAFF-Scripts/run_tests.py`

These scripts expect a local Python environment and the required verification tooling to be installed.

## Repository layout

- `STAFF-Dataset` contains the published dataset snapshot.
- `STAFF-Scripts` contains helper scripts used in the original workflow and kept for reproducibility.
