# LeanNumBench arXiv Release Notes

Release status: public preprint release package.

- Benchmark name: `LeanNumBench`.
- Author line: Qinghe Wang, Independent Researcher.
- Primary benchmark: 160 proof-completion records and 405 task specifications.
- Main evaluation: dated May-2026 five-endpoint proof-completion panel.
- Reproducibility: no paid API calls are required for PDF compilation or
  artifact smoke checks; model outputs are usage-stripped.
- License: CC-BY-4.0 for benchmark metadata; Apache-2.0 for companion Lean
  source, evaluation scripts, and release tooling.

Known limitations are stated in the paper and appendix: the release does not
yet include an independent taxonomy annotation study, Lean-feedback agent
baseline, full-160 pass@k panel, retrieval-augmented baseline,
shuffled/irrelevant-context control, or direct CAM-Bench numerical-subset rerun.

## Current Build Hashes

- Release artifact zip: `LeanNumBench_arxiv2026_release_artifact.zip`.
- arXiv ancillary artifact path: `anc/leannumbench-v1-artifact.zip`.
- Release artifact SHA256: `e7e649f5ba0efd59de165ae36c31fca40bebf6a6e336f4b683b388198604bb22`.
- Frozen 160-row proof prompt pack SHA256: `a02df6374ec92828389b3f1f59f56d2133e00378ade8eef4763b66e42c2adb78`.
- Companion Lean `lake-manifest.json` SHA256: `b5199815f98f54813f7ff29fffebd34f0f421d16fd0eeacacd198f20cd7d73c1`.
- Public GitHub release:
  `https://github.com/Qinghev/LeanNumBench/releases/tag/v1.0-arxiv`.

