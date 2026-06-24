# LeanNumBench arXiv Release Artifact

This package contains the public reproducibility artifact for the arXiv
preprint "LeanNumBench: Diagnosing LLM Proof Completion in Lean-Checked
Numerical Analysis".

## Current Main Results

- Frozen LeanNumBench v1 benchmark: 160 records and 405 task specifications.
- Final proof-completion panel: 5 endpoint aliases x 160 records = 800
  model-record attempts.
- Best one-shot result in the final five-endpoint panel: 147/160.
- Final hard subset: 11 rows failed by at least three of five endpoints.
- Final hard-subset pass@3: 165 API rows, three samples per endpoint-record
  pair; best endpoint solves 9/11; four rows remain unsolved by at least two
  endpoints.

## Directory Layout

- `records/`: benchmark metadata for the frozen LeanNumBench v1 release.
- `schemas/`: JSON schemas used by benchmark records and model-pilot manifests.
- `companion_lean/`: Lean 4 source, `lean-toolchain`, and Lake configuration
  for the theorem declarations used by proof candidates.
- `experiments/model_pilot_160_proof/`: frozen 160-record prompt pack,
  targets, candidate template, manifest, and prompt audit.
- `experiments/hard_subset_frontier_160/`: final 11-row hard-subset prompt
  pack and prompt audit.
- `experiments/controlled_pair_v4_selected_8/`: matched proof-surface pilot
  prompt pack and prompt audit.
- `results/`: paper-facing tables, JSON summaries, and no-usage raw model
  outputs for the 160-record panel and final pass@3 probe.
- `reproduction_scripts/`: artifact smoke-check, prompt-audit,
  materialization, candidate-checking, and no-LLM tactic-baseline scripts.

## Public-Release Sanitization

Local filesystem paths and API-key patterns have been removed or replaced.
Raw per-call token-usage metadata and raw per-call cost fields have been
removed. Aggregate model-variant token and cost summaries are retained only in
`results/model_variant_cost_audit.*`.

## License

Benchmark records, schemas, prompt packs, generated table data, and metadata
are released under CC-BY-4.0. Companion Lean source, evaluation scripts, and
release tooling are released under Apache-2.0.

## Reproduction Notes

Quick no-API artifact check:

```bash
python reproduction_scripts/artifact_smoke_check.py
```

Standalone schema validation:

```bash
python reproduction_scripts/validate_record_schemas.py
```

Full local Lean replay of the 160-record proof panel:

```bash
cd companion_lean
lake exe cache get
lake build LeanNumerics
cd ..
RS=reproduction_scripts
OUT=_repro/leannumbench160_candidates
python $RS/materialize_model_pilot_candidates.py \
  results/raw_outputs/frontier_160_no_usage.jsonl \
  --targets experiments/model_pilot_160_proof/targets.jsonl \
  --output-dir $OUT
python $RS/check_lean_candidates_divide.py \
  --candidate-file $OUT/proof_candidates.jsonl \
  --lean-project companion_lean --repair-simple \
  --output _repro/leannumbench160_check.json
```

These commands do not call model APIs. The cache-get step only accelerates
Mathlib setup; if unavailable, Lake can build from source. The companion Lean
project uses `leanprover/lean4:v4.29.1`, pins Mathlib at `v4.29.1`, and ships
with `lake-manifest.json` SHA256
`2ed57a7e536783afef8fbb708429ea371e2524c941d8e7152f7a9bd3eca4b63b`.
