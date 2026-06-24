"""Audit a prepared LeanNumBench model-pilot prompt pack.

This script is intentionally local and model-free. It checks that prompt,
target, and candidate-template JSONL files are aligned, that proof hints are
not copied verbatim into prompts, that candidate templates are empty, and that
public artifact archives do not contain configured leak patterns.
"""

from __future__ import annotations

import argparse
import json
import statistics
import sys
import zipfile
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


def resolve_layout(root: Path) -> tuple[Path, Path, Path | None]:
    repo_theorem_root = root / "records" / "theorems"
    repo_index = repo_theorem_root / "index.json"
    release_zip = root / "paper" / "arxiv2026" / "LeanNumBench_arxiv2026_release_artifact.zip"
    if repo_index.is_file():
        return repo_theorem_root, repo_index, release_zip if release_zip.is_file() else None

    artifact_theorem_root = root / "records" / "theorems"
    artifact_index = root / "records" / "index.json"
    if artifact_index.is_file() and artifact_theorem_root.is_dir():
        return artifact_theorem_root, artifact_index, None

    return repo_theorem_root, repo_index, None


THEOREM_ROOT, INDEX_PATH, DEFAULT_SUPPLEMENT_ZIP = resolve_layout(ROOT)
TEXT_SUFFIXES = {
    ".bib",
    ".csv",
    ".json",
    ".jsonl",
    ".lean",
    ".md",
    ".py",
    ".tex",
    ".toml",
    ".txt",
    ".yaml",
    ".yml",
}

PILOT_SENSITIVE_PATTERNS = [
    "git@github.com:",
    "public repository owner",
    "C:" + "\\Users\\",
    "C:" + "/Users/",
    "sk-or-",
    "sk-",
    "AIza",
]

SUPPLEMENT_SENSITIVE_PATTERNS = [
    *PILOT_SENSITIVE_PATTERNS,
    "Qinghe Wang",
    "qinghe",
    "LeanNumerics",
]


def load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return data


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows = []
    with path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            stripped = line.strip()
            if not stripped:
                continue
            data = json.loads(stripped)
            if not isinstance(data, dict):
                raise ValueError(f"{path}:{line_number}: expected a JSON object")
            rows.append(data)
    return rows


def load_records_by_id() -> dict[str, dict[str, Any]]:
    index = load_json(INDEX_PATH)
    records: dict[str, dict[str, Any]] = {}
    for item in index["records"]:
        record = load_json(THEOREM_ROOT / item["path"])
        records[record["id"]] = record
    return records


def theorem_name(record: dict[str, Any]) -> str:
    theorem_declarations = [
        declaration["name"]
        for declaration in record["formal"]["declarations"]
        if declaration["kind"] == "theorem"
    ]
    if not theorem_declarations:
        raise ValueError(f"{record['id']}: no theorem declaration")
    return theorem_declarations[-1]


def theorem_statement(record: dict[str, Any]) -> str:
    theorem_declarations = [
        declaration["statement"]
        for declaration in record["formal"]["declarations"]
        if declaration["kind"] == "theorem"
    ]
    if not theorem_declarations:
        raise ValueError(f"{record['id']}: no theorem declaration")
    return theorem_declarations[-1]


def prompt_source_context(prompt: str) -> str:
    start_marker = "Relevant local declaration names already available through the Lean imports:\n\n"
    end_marker = "\n\nTheorem statement to prove:\n\n"
    if start_marker not in prompt or end_marker not in prompt:
        return ""
    return prompt.split(start_marker, 1)[1].split(end_marker, 1)[0]


def add_issue(issues: list[dict[str, str]], kind: str, location: str, message: str) -> None:
    issues.append({"kind": kind, "location": location, "message": message})


def scan_text_for_patterns(
    text: str,
    patterns: list[str],
    location: str,
    issues: list[dict[str, str]],
) -> None:
    for pattern in patterns:
        if pattern in text:
            add_issue(issues, "sensitive_pattern", location, f"found pattern {pattern!r}")


def display_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def audit_rows(pilot_dir: Path) -> dict[str, Any]:
    prompt_path = pilot_dir / "prompts.jsonl"
    target_path = pilot_dir / "targets.jsonl"
    candidate_path = pilot_dir / "candidate_template.jsonl"
    manifest_path = pilot_dir / "manifest.json"
    summary_path = pilot_dir / "summary.json"

    for path in [prompt_path, target_path, candidate_path, manifest_path, summary_path]:
        if not path.is_file():
            raise ValueError(f"missing required pilot artifact: {path}")

    prompts = load_jsonl(prompt_path)
    targets = load_jsonl(target_path)
    candidates = load_jsonl(candidate_path)
    manifest = load_json(manifest_path)
    summary = load_json(summary_path)
    records_by_id = load_records_by_id()
    issues: list[dict[str, str]] = []

    if not (len(prompts) == len(targets) == len(candidates)):
        add_issue(
            issues,
            "row_count_mismatch",
            str(pilot_dir),
            f"prompts={len(prompts)}, targets={len(targets)}, candidates={len(candidates)}",
        )

    prompt_ids = [row.get("prompt_id") for row in prompts]
    target_ids = [row.get("prompt_id") for row in targets]
    candidate_ids = [row.get("prompt_id") for row in candidates]
    if prompt_ids != target_ids or prompt_ids != candidate_ids:
        add_issue(issues, "prompt_id_alignment", str(pilot_dir), "JSONL prompt_id order differs")
    if len(set(prompt_ids)) != len(prompt_ids):
        add_issue(issues, "duplicate_prompt_id", str(pilot_dir), "duplicate prompt_id values")

    rows_by_target_id = {row.get("prompt_id"): row for row in targets}
    rows_by_candidate_id = {row.get("prompt_id"): row for row in candidates}
    prompt_lengths = []
    categories = Counter()
    difficulties = Counter()
    tasks = Counter()

    for prompt_row in prompts:
        prompt_id = str(prompt_row.get("prompt_id", ""))
        record_id = str(prompt_row.get("record_id", ""))
        prompt = str(prompt_row.get("prompt", ""))
        prompt_lengths.append(len(prompt))
        categories[str(prompt_row.get("category", ""))] += 1
        difficulties[str(prompt_row.get("difficulty", ""))] += 1
        tasks[str(prompt_row.get("task", ""))] += 1

        scan_text_for_patterns(prompt, PILOT_SENSITIVE_PATTERNS, prompt_id, issues)

        if record_id not in records_by_id:
            add_issue(issues, "unknown_record_id", prompt_id, f"record_id {record_id!r} not in index")
            continue

        record = records_by_id[record_id]
        source_context = prompt_source_context(prompt)
        target_name = theorem_name(record)
        target_statement = theorem_statement(record)
        if source_context:
            if target_statement in source_context:
                add_issue(
                    issues,
                    "target_statement_in_source_context",
                    prompt_id,
                    "source declaration context contains the target theorem statement",
                )
            context_lines = [line.strip() for line in source_context.splitlines()]
            if any(line.startswith(f"- theorem {target_name}") for line in context_lines):
                add_issue(
                    issues,
                    "target_name_in_source_context",
                    prompt_id,
                    "source declaration context contains the target theorem name",
                )

        target_row = rows_by_target_id.get(prompt_id, {})
        target_text = str(target_row.get("target", "")).strip()
        if len(target_text) >= 12 and target_text.lower() in prompt.lower():
            add_issue(
                issues,
                "target_hint_verbatim_in_prompt",
                prompt_id,
                "target proof hint appears verbatim in the model prompt",
            )

        candidate_row = rows_by_candidate_id.get(prompt_id, {})
        prediction = candidate_row.get("prediction")
        if prediction not in ("", None):
            add_issue(
                issues,
                "nonempty_candidate_template",
                prompt_id,
                "candidate_template prediction must be empty before a model run",
            )

    prompt_stats = {
        "min": min(prompt_lengths) if prompt_lengths else 0,
        "max": max(prompt_lengths) if prompt_lengths else 0,
        "mean": round(statistics.mean(prompt_lengths), 1) if prompt_lengths else 0,
        "median": round(statistics.median(prompt_lengths), 1) if prompt_lengths else 0,
    }

    return {
        "pilot_dir": display_path(pilot_dir),
        "pilot_id": manifest.get("pilot_id") or summary.get("pilot_id"),
        "prompt_rows": len(prompts),
        "target_rows": len(targets),
        "candidate_rows": len(candidates),
        "prompt_chars": prompt_stats,
        "by_category": dict(sorted(categories.items())),
        "by_difficulty": dict(sorted(difficulties.items())),
        "by_task": dict(sorted(tasks.items())),
        "issues": issues,
    }


def scan_supplement_zip(zip_path: Path) -> dict[str, Any]:
    issues: list[dict[str, str]] = []
    scanned_files = 0
    if not zip_path.is_file():
        add_issue(issues, "missing_supplement_zip", display_path(zip_path), "supplement zip does not exist")
        return {"path": display_path(zip_path), "scanned_files": scanned_files, "issues": issues}

    with zipfile.ZipFile(zip_path) as archive:
        for member in archive.infolist():
            member_path = Path(member.filename)
            if member.is_dir() or member_path.suffix.lower() not in TEXT_SUFFIXES:
                continue
            scanned_files += 1
            data = archive.read(member)
            text = data.decode("utf-8", errors="ignore")
            scan_text_for_patterns(text, SUPPLEMENT_SENSITIVE_PATTERNS, member.filename, issues)

    return {"path": display_path(zip_path), "scanned_files": scanned_files, "issues": issues}


def write_report(report: dict[str, Any], output_path: Path | None) -> None:
    rendered = json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True)
    if output_path is None:
        print(rendered)
        return
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(rendered + "\n", encoding="utf-8")
    print(f"Wrote prompt audit report to {output_path}")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pilot_dir", type=Path, help="Prepared model pilot directory.")
    parser.add_argument(
        "--supplement-zip",
        type=Path,
        default=DEFAULT_SUPPLEMENT_ZIP,
        help="Optional public artifact zip to scan.",
    )
    parser.add_argument("--output", type=Path, help="Write JSON report to this path.")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    pilot_report = audit_rows(args.pilot_dir)
    supplement_report = scan_supplement_zip(args.supplement_zip) if args.supplement_zip else None
    issues = list(pilot_report["issues"])
    if supplement_report is not None:
        issues.extend(supplement_report["issues"])
    report = {
        "report_kind": "model_pilot_prompt_audit",
        "schema_version": "0.1.0",
        "passed": not issues,
        "pilot": pilot_report,
        "supplement": supplement_report,
        "issues_count": len(issues),
        "issues": issues,
    }
    write_report(report, args.output)
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
