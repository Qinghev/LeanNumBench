# LeanNumBench

LeanNumBench is a Lean 4 diagnostic benchmark for numerical-analysis
proof-body completion. It evaluates whether language-model endpoints can
complete local Lean proof bodies under frozen theorem statements and local
declaration context, with all reported proof completions checked locally by
Lean and with `sorry` disallowed.

The public benchmark and arXiv release name is `LeanNumBench`.

## v1 Release

LeanNumBench v1 contains:

| Asset | Count |
|---|---:|
| Frozen theorem records | 160 |
| Task specifications | 405 |
| Proof-completion tasks | 160 |
| Statement-translation tasks | 160 |
| Theorem-retrieval tasks | 85 |
| Main proof-completion panel | 5 endpoint aliases x 160 rows |
| Hard subset | 11 rows failed by at least 3 of 5 endpoints |

The release focuses on proof-body completion for finite differences, FEM/P0
projection, spectral identities, ODE and Runge--Kutta identities,
linear-algebra stability, interpolation, quadrature, and related local
numerical-analysis proof patterns.

## Paper

The public preprint package is in [`paper/arxiv2026`](paper/arxiv2026).
The public GitHub release is
[`v1.0-arxiv`](https://github.com/Qinghev/LeanNumBench/releases/tag/v1.0-arxiv).

Important files:

- [`paper/arxiv2026/main.tex`](paper/arxiv2026/main.tex): arXiv top-level TeX.
- [`paper/arxiv2026/appendix.tex`](paper/arxiv2026/appendix.tex): appendix body
  loaded by `main.tex`.
- [`paper/arxiv2026/LeanNumBench_arxiv2026_source.zip`](paper/arxiv2026/LeanNumBench_arxiv2026_source.zip):
  arXiv source bundle.
- [`paper/arxiv2026/LeanNumBench_arxiv2026_release_artifact.zip`](paper/arxiv2026/LeanNumBench_arxiv2026_release_artifact.zip):
  standalone reproducibility artifact.
- [`paper/arxiv2026/anc/leannumbench-v1-artifact.zip`](paper/arxiv2026/anc/leannumbench-v1-artifact.zip):
  arXiv ancillary artifact included in the source bundle.

Build the paper locally:

```bash
cd paper/arxiv2026
latexmk -pdf main.tex
```

No model API calls are required to build the paper or audit the released
artifact.

## Reproducibility

Run the fast no-API artifact smoke check:

```bash
cd paper/arxiv2026/release_artifact
python reproduction_scripts/artifact_smoke_check.py
```

Expected summary:

```json
{
  "passed": true,
  "records": 160,
  "tasks": 405,
  "frontier_model_record_pairs": 800,
  "hard_subset_records": 11,
  "pass3_api_rows": 165
}
```

The artifact contains frozen records, prompt packs, usage-stripped model
outputs, materialized-candidate scripts, row-level summaries, checker logs,
generated table data, hashes, and offline replay scripts.

To rerun local Lean checking, use the companion Lean project shipped inside
`paper/arxiv2026/release_artifact/companion_lean`:

```bash
cd paper/arxiv2026/release_artifact/companion_lean
lake exe cache get
lake build LeanNumerics
```

The companion Lean project uses `leanprover/lean4:v4.29.1` and pins Mathlib at
`v4.29.1`.

## Main Results Snapshot

The May-2026 five-endpoint proof-completion panel over all 160 records:

| Endpoint alias | Passed | Accuracy |
|---|---:|---:|
| Gemini 3.1 Pro Preview | 147/160 | 91.9% |
| GPT-5.5 Pro | 145/160 | 90.6% |
| Claude Opus 4.8 | 141/160 | 88.1% |
| Qwen3.6 Max Preview | 139/160 | 86.9% |
| DeepSeek v4 Pro | 126/160 | 78.8% |

These are dated endpoint-protocol results, not a timeless model ranking. The
benchmark contribution is the prompt pack, local checker, released candidates,
row-level diagnostics, hard-subset analysis, declaration-context ablation,
repair audit, and failure taxonomy.

## Repository Layout

```text
paper/arxiv2026/                       Public preprint and release package
paper/arxiv2026/release_artifact/      Path-sanitized reproducibility artifact
paper/arxiv2026/anc/                   arXiv ancillary artifact
docs/release/                          Public release notes
.github/workflows/ci.yml               No-API artifact and Lean smoke checks
```

For the public v1 artifact, use the frozen files under
`paper/arxiv2026/release_artifact/`.

## Licenses

Benchmark records, schemas, prompt packs, generated table data, and benchmark
metadata are released under CC-BY-4.0; see
[`LICENSE-METADATA.md`](LICENSE-METADATA.md).

Companion Lean source, evaluation scripts, and release tooling are released
under Apache-2.0; see [`LICENSE`](LICENSE).

## Citation

Use [`CITATION.cff`](CITATION.cff) or cite the arXiv preprint once an arXiv ID
is available.
