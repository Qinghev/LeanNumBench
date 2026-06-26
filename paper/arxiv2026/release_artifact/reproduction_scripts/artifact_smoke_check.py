"""Offline smoke checks for the LeanNumBench arXiv artifact.

This script checks metadata consistency, usage-stripping, local path
sanitization, and package integrity. It does not call model APIs and does not
require Lean.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

from validate_record_schemas import validate_records


ROOT = Path(__file__).resolve().parents[1]

LOCAL_PATH_PATTERNS = [
    re.compile(pattern, re.IGNORECASE)
    for pattern in [
        r"C:\\Users\\[A-Za-z0-9_.-]+",
        r"C:/Users/[A-Za-z0-9_.-]+",
        r"Documents\\research",
        r"Documents/research",
        r"sk-or-[A-Za-z0-9_-]{16,}",
        r"sk-[A-Za-z0-9_-]{16,}",
        r"AIza[A-Za-z0-9_-]{16,}",
        "OPENROUTER_" + "API_KEY",
    ]
]

USAGE_KEYS = {
    "usage",
    "usage_metadata",
    "cost",
    "cost_details",
    "upstream_inference_cost",
    "upstream_inference_prompt_cost",
    "upstream_inference_completions_cost",
}


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def walk_keys(value: Any, prefix: str = "") -> list[str]:
    if isinstance(value, dict):
        findings = []
        for key, item in value.items():
            path = f"{prefix}.{key}" if prefix else str(key)
            if key in USAGE_KEYS:
                findings.append(path)
            findings.extend(walk_keys(item, path))
        return findings
    if isinstance(value, list):
        findings = []
        for index, item in enumerate(value):
            findings.extend(walk_keys(item, f"{prefix}[{index}]"))
        return findings
    return []


def check(condition: bool, issues: list[str], message: str) -> None:
    if not condition:
        issues.append(message)


def main() -> int:
    issues: list[str] = []
    manifest_path = ROOT / "artifact_manifest.json"
    index_path = ROOT / "records" / "index.json"
    frontier_path = ROOT / "results" / "frontier_proof_160_summary.json"
    pass3_path = ROOT / "results" / "final160_hard_subset_pass3_summary.json"

    check(manifest_path.is_file(), issues, "missing artifact_manifest.json")
    check(index_path.is_file(), issues, "missing records/index.json")
    check(frontier_path.is_file(), issues, "missing frontier summary")
    check(pass3_path.is_file(), issues, "missing pass@3 summary")

    if issues:
        print(json.dumps({"passed": False, "issues": issues}, indent=2))
        return 1

    manifest = load_json(manifest_path)
    index = load_json(index_path)
    frontier = load_json(frontier_path)
    pass3 = load_json(pass3_path)
    schema_payload = validate_records(ROOT)
    if not schema_payload.get("passed", False):
        issues.extend(f"schema validation: {issue}" for issue in schema_payload.get("issues", [])[:20])

    records = index.get("records", [])
    task_count = 0
    for item in records:
        record = load_json(ROOT / "records" / "theorems" / item["path"])
        task_count += len(record.get("tasks", []))

    check(len(records) == 160, issues, f"expected 160 records, found {len(records)}")
    check(task_count == 405, issues, f"expected 405 tasks, found {task_count}")
    check(frontier.get("model_record_pairs") == 800, issues, "frontier pair count is not 800")
    check(frontier.get("hard_subset_records") == 11, issues, "hard subset count is not 11")
    check(pass3.get("api_rows") == 165, issues, "pass@3 API row count is not 165")
    check(manifest.get("double_blind") is False, issues, "artifact manifest should be public")

    for path in [
        ROOT / "results" / "raw_outputs" / "frontier_160_no_usage.jsonl",
        ROOT / "results" / "raw_outputs" / "final160_hard_subset_pass3_no_usage.jsonl",
        ROOT / "results" / "raw_outputs" / "model_variant_audit_no_usage.jsonl",
        ROOT / "results" / "raw_outputs" / "controlled_pair_v4_selected_8_no_usage.jsonl",
    ]:
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if not line.strip():
                continue
            bad_keys = walk_keys(json.loads(line))
            if bad_keys:
                issues.append(f"{path.relative_to(ROOT)}:{line_number}: raw usage keys {bad_keys[:3]}")
                break

    for path in sorted(ROOT.rglob("*")):
        if not path.is_file():
            continue
        if path == Path(__file__).resolve():
            continue
        if path.suffix.lower() not in {".bib", ".csv", ".json", ".jsonl", ".lean", ".md", ".py", ".tex", ".txt", ".toml"}:
            continue
        text = path.read_text(encoding="utf-8", errors="ignore")
        for pattern in LOCAL_PATH_PATTERNS:
            if pattern.search(text):
                issues.append(f"{path.relative_to(ROOT).as_posix()}: local/secret pattern {pattern.pattern}")

    checksum_manifest = ROOT / "sha256_manifest.txt"
    if checksum_manifest.is_file():
        for line in checksum_manifest.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            expected, rel = line.split("  ", 1)
            path = ROOT / rel
            check(path.is_file(), issues, f"missing checksum target {rel}")
            if path.is_file() and sha256_file(path) != expected:
                issues.append(f"checksum mismatch: {rel}")

    payload = {
        "passed": not issues,
        "records": len(records),
        "tasks": task_count,
        "frontier_model_record_pairs": frontier.get("model_record_pairs"),
        "hard_subset_records": frontier.get("hard_subset_records"),
        "pass3_api_rows": pass3.get("api_rows"),
        "schema_errors": schema_payload.get("schema_errors"),
        "issues": issues,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if not issues else 1


if __name__ == "__main__":
    raise SystemExit(main())
