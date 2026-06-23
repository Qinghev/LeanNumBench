"""Compile-check LeanNumBench Lean statement/proof candidates.

This script is a local harness, not a full LLM runner. It uses a checked
LeanNumBench record to build a temporary Lean file, imports the referenced
LeanNumerics module, renames the candidate theorem to avoid declaration-name
collisions, and calls `lake env lean`.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


def resolve_layout(root: Path) -> tuple[Path, Path, Path]:
    repo_theorem_root = root / "nabench" / "theorems"
    repo_index = repo_theorem_root / "index.json"
    if repo_index.is_file():
        return repo_theorem_root, repo_index, (root / ".." / "LeanNumerics").resolve()

    artifact_theorem_root = root / "records" / "theorems"
    artifact_index = root / "records" / "index.json"
    artifact_lean = root / "companion_lean"
    if artifact_index.is_file() and artifact_theorem_root.is_dir():
        return artifact_theorem_root, artifact_index, artifact_lean.resolve()

    return repo_theorem_root, repo_index, (root / ".." / "LeanNumerics").resolve()


THEOREM_ROOT, INDEX_PATH, DEFAULT_LEAN_PROJECT = resolve_layout(ROOT)
THEOREM_PATTERN = re.compile(r"\btheorem\s+([A-Za-z_][A-Za-z0-9_'.]*)")
NO_PROGRESS_PATTERN = re.compile(r"`([^`]+)` made no progress")
NO_GOALS_PATTERN = re.compile(r"Candidate\.lean:(\d+):\d+: error: No goals to be solved")
SIMPLE_NO_GOALS_TACTICS = {"norm_num", "ring", "ring_nf", "simp"}


def load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return data


def load_records() -> list[dict[str, Any]]:
    index = load_json(INDEX_PATH)
    return [load_json(THEOREM_ROOT / item["path"]) for item in index["records"]]


def record_by_id(record_id: str) -> dict[str, Any]:
    for record in load_records():
        if record["id"] == record_id:
            return record
    raise ValueError(f"unknown record id {record_id!r}")


def module_from_file(file_name: str) -> str:
    path = Path(file_name)
    without_suffix = path.with_suffix("")
    return ".".join(without_suffix.parts)


def namespace_lines(record: dict[str, Any]) -> tuple[list[str], list[str]]:
    namespaces = record["formal"].get("namespace", [])
    opens = [f"namespace {name}" for name in namespaces]
    closes = [f"end {name}" for name in reversed(namespaces)]
    return opens, closes


def statement_translation_target(record: dict[str, Any]) -> str:
    for task in record["tasks"]:
        if task["task"] == "statement_translation":
            return task["target"]
    raise ValueError(f"{record['id']}: no statement_translation task")


def read_text_argument(value: str | None, fallback: str) -> str:
    if value is None:
        return fallback
    path = Path(value)
    if path.is_file():
        return path.read_text(encoding="utf-8")
    return value


def load_candidate_items(path: Path) -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8").strip()
    if not text:
        return []
    if path.suffix == ".jsonl":
        items = [json.loads(line) for line in text.splitlines() if line.strip()]
    else:
        data = json.loads(text)
        if isinstance(data, dict):
            items = data.get("candidates", [])
        else:
            items = data
    if not isinstance(items, list):
        raise ValueError(f"{path}: expected a JSON array or JSONL candidate list")
    for index, item in enumerate(items):
        if not isinstance(item, dict):
            raise ValueError(f"{path}: candidate {index} must be an object")
        if not isinstance(item.get("record_id"), str) or not item["record_id"]:
            raise ValueError(f"{path}: candidate {index} missing record_id")
        if not isinstance(item.get("proof"), str) or not item["proof"].strip():
            raise ValueError(f"{path}: candidate {index} missing proof")
        if "statement" in item and not isinstance(item["statement"], str):
            raise ValueError(f"{path}: candidate {index} statement must be a string")
    return items


def candidate_name(record_id: str) -> str:
    return "nabench_candidate_" + re.sub(r"[^A-Za-z0-9_]", "_", record_id)


def proof_candidate_name(item: dict[str, Any], index: int) -> str:
    suffix_source = item.get("candidate_id") or f"candidate_{index}"
    suffix = re.sub(r"[^A-Za-z0-9_]", "_", suffix_source)
    return f"{candidate_name(item['record_id'])}__{suffix}"


def rename_theorem(statement: str, name: str = "nabench_candidate") -> str:
    statement = statement.strip()
    if not statement.startswith("theorem "):
        raise ValueError("candidate statement must start with `theorem `")
    renamed, count = THEOREM_PATTERN.subn(f"theorem {name}", statement, count=1)
    if count != 1:
        raise ValueError("could not find theorem declaration name")
    return renamed


def build_candidate_source(record: dict[str, Any], statement: str, proof: str, name: str = "nabench_candidate") -> str:
    module_name = module_from_file(record["formal"]["file"])
    opens, closes = namespace_lines(record)
    body = [
        f"import {module_name}",
        "",
        "set_option autoImplicit false",
        "open scoped BigOperators",
        "",
        *opens,
        "",
        f"{rename_theorem(statement, name)} := by",
        *[f"  {line}" if line else "" for line in proof.strip().splitlines()],
        "",
        *closes,
        "",
    ]
    return "\n".join(body)


def run_lean(source: str, lean_project: Path, timeout: int) -> dict[str, Any]:
    lean_project = lean_project.resolve()
    if not lean_project.is_dir():
        raise ValueError(f"Lean project not found: {lean_project}")
    scratch_root = lean_project / ".nabench_tmp"
    scratch_root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="run_", dir=scratch_root) as tmp_dir:
        candidate_path = Path(tmp_dir) / "Candidate.lean"
        candidate_path.write_text(source, encoding="utf-8")
        completed = subprocess.run(
            ["lake", "env", "lean", str(candidate_path)],
            cwd=lean_project,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    combined_output = completed.stdout + completed.stderr
    return {
        "passed": completed.returncode == 0,
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
        "contains_sorry": "declaration uses `sorry`" in combined_output or "sorry" in source,
    }


def build_all_statements_source(records: list[dict[str, Any]]) -> str:
    imports = sorted({module_from_file(record["formal"]["file"]) for record in records})
    body = [*(f"import {module_name}" for module_name in imports), "", "set_option autoImplicit false", "open scoped BigOperators", ""]
    for record in records:
        opens, closes = namespace_lines(record)
        body.extend(
            [
                f"-- {record['id']}",
                *opens,
                "",
                f"{rename_theorem(statement_translation_target(record), candidate_name(record['id']))} := by",
                "  sorry",
                "",
                *closes,
                "",
            ]
        )
    return "\n".join(body)


def build_proof_candidates_source(items: list[dict[str, Any]]) -> tuple[str, list[dict[str, Any]]]:
    records = [record_by_id(item["record_id"]) for item in items]
    imports = sorted({module_from_file(record["formal"]["file"]) for record in records})
    body = [*(f"import {module_name}" for module_name in imports), "", "set_option autoImplicit false", "open scoped BigOperators", ""]
    result_templates = []

    for index, (item, record) in enumerate(zip(items, records)):
        statement = item.get("statement", statement_translation_target(record))
        name = proof_candidate_name(item, index)
        opens, closes = namespace_lines(record)
        body.extend(
            [
                f"-- {item.get('candidate_id') or index}: {record['id']}",
                *opens,
                "",
                f"{rename_theorem(statement, name)} := by",
                *[f"  {line}" if line else "" for line in item["proof"].strip().splitlines()],
                "",
                *closes,
                "",
            ]
        )
        result_templates.append(
            {
                "record_id": record["id"],
                "formal_file": record["formal"]["file"],
                "mode": "proof_body_candidate",
                "candidate_id": item.get("candidate_id"),
                "contains_sorry": "sorry" in item["proof"],
            }
        )

    return "\n".join(body), result_templates


def check_record_statement(record: dict[str, Any], lean_project: Path, timeout: int) -> dict[str, Any]:
    statement = statement_translation_target(record)
    source = build_candidate_source(record, statement, "sorry", candidate_name(record["id"]))
    result = run_lean(source, lean_project, timeout)
    return {
        "record_id": record["id"],
        "formal_file": record["formal"]["file"],
        "mode": "statement_with_sorry",
        **result,
    }


def check_proof_candidates_batch(
    items: list[dict[str, Any]], lean_project: Path, timeout: int
) -> list[dict[str, Any]] | None:
    source, result_templates = build_proof_candidates_source(items)
    result = run_lean(source, lean_project, timeout)
    if not result["passed"]:
        return None
    return [
        {
            **template,
            "passed": True,
            "returncode": result["returncode"],
            "stdout": "",
            "stderr": "",
            "batch_compiled": True,
        }
        for template in result_templates
    ]


def no_progress_tactic(output: str) -> str | None:
    match = NO_PROGRESS_PATTERN.search(output)
    if not match:
        return None
    return match.group(1).strip()


def drop_first_tactic_line(proof: str, tactic: str) -> tuple[str, bool]:
    lines = proof.splitlines()
    repaired = []
    removed = False
    for line in lines:
        stripped = line.strip()
        if not removed and (stripped == tactic or stripped.startswith(f"{tactic} ")):
            removed = True
            continue
        repaired.append(line)
    return "\n".join(repaired).strip(), removed


def should_try_ring_nf(output: str) -> bool:
    return "The `ring` tactic failed" in output and "ring_nf" in output


def replace_first_tactic_line(proof: str, source: str, target: str) -> tuple[str, bool]:
    lines = proof.splitlines()
    replaced = False
    for index, line in enumerate(lines):
        if replaced or line.strip() != source:
            continue
        indent = line[: len(line) - len(line.lstrip())]
        lines[index] = f"{indent}{target}"
        replaced = True
    return "\n".join(lines).strip(), replaced


def proof_start_line(record: dict[str, Any]) -> int:
    opens, _closes = namespace_lines(record)
    return 8 + len(opens)


def no_goals_proof_line(output: str, record: dict[str, Any]) -> int | None:
    match = NO_GOALS_PATTERN.search(output)
    if not match:
        return None
    source_line = int(match.group(1))
    index = source_line - proof_start_line(record)
    return index if index >= 0 else None


def drop_simple_no_goals_line(proof: str, line_index: int | None) -> tuple[str, bool, str | None]:
    if line_index is None:
        return proof, False, None
    lines = proof.splitlines()
    if line_index >= len(lines):
        return proof, False, None
    tactic = lines[line_index].strip()
    if tactic not in SIMPLE_NO_GOALS_TACTICS:
        return proof, False, None
    repaired = [line for index, line in enumerate(lines) if index != line_index]
    return "\n".join(repaired).strip(), True, tactic


def check_proof_candidate(
    item: dict[str, Any],
    lean_project: Path,
    timeout: int,
    repair_simple: bool = False,
) -> dict[str, Any]:
    record = record_by_id(item["record_id"])
    statement = item.get("statement", statement_translation_target(record))
    proof = item["proof"]
    source = build_candidate_source(record, statement, proof, proof_candidate_name(item, 0))
    result = run_lean(source, lean_project, timeout)
    original_result = result
    repair_steps = []
    if repair_simple:
        for _attempt in range(5):
            if result["passed"]:
                break
            output = result["stdout"] + result["stderr"]
            tactic = no_progress_tactic(output)
            if tactic is not None:
                repaired_proof, removed = drop_first_tactic_line(proof, tactic)
                if not removed or not repaired_proof:
                    break
                proof = repaired_proof
                repair_steps.append({"kind": "drop_no_progress_tactic", "tactic": tactic})
                source = build_candidate_source(record, statement, proof, proof_candidate_name(item, 0))
                result = run_lean(source, lean_project, timeout)
                continue
            if should_try_ring_nf(output):
                repaired_proof, replaced = replace_first_tactic_line(proof, "ring", "ring_nf")
                if not replaced or not repaired_proof:
                    break
                proof = repaired_proof
                repair_steps.append({"kind": "replace_tactic", "from": "ring", "to": "ring_nf"})
                source = build_candidate_source(record, statement, proof, proof_candidate_name(item, 0))
                result = run_lean(source, lean_project, timeout)
                continue
            repaired_proof, removed, dropped_tactic = drop_simple_no_goals_line(
                proof,
                no_goals_proof_line(output, record),
            )
            if removed and repaired_proof:
                proof = repaired_proof
                repair_steps.append({"kind": "drop_no_goals_tactic", "tactic": dropped_tactic})
                source = build_candidate_source(record, statement, proof, proof_candidate_name(item, 0))
                result = run_lean(source, lean_project, timeout)
                continue
            break
    contains_sorry = "sorry" in item["proof"] or result["contains_sorry"]
    if repair_steps:
        contains_sorry = contains_sorry or "sorry" in proof
    return {
        "record_id": record["id"],
        "formal_file": record["formal"]["file"],
        "mode": "proof_body_candidate",
        "candidate_id": item.get("candidate_id"),
        "contains_sorry": contains_sorry,
        "batch_compiled": False,
        "repaired": bool(repair_steps) and result["passed"],
        "repair_steps": repair_steps,
        "proof_after_repair": proof if repair_steps else None,
        "original_stdout": original_result["stdout"] if repair_steps else None,
        "original_stderr": original_result["stderr"] if repair_steps else None,
        **{key: value for key, value in result.items() if key != "contains_sorry"},
    }


def summarize_results(results: list[dict[str, Any]]) -> dict[str, Any]:
    passed = [result for result in results if result["passed"]]
    failed = [result for result in results if not result["passed"]]
    sorry = [result for result in results if result.get("contains_sorry")]
    return {
        "total": len(results),
        "passed": len(passed),
        "failed": len(failed),
        "contains_sorry": len(sorry),
        "passed_without_sorry": len([result for result in passed if not result.get("contains_sorry")]),
    }


def print_text_result(result: dict[str, Any]) -> None:
    status = "PASS" if result["passed"] else "FAIL"
    print(f"{status} {result['record_id']} ({result['mode']})")
    if result["stdout"]:
        print(result["stdout"], end="")
    if result["stderr"]:
        print(result["stderr"], end="", file=sys.stderr)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record-id", help="record id to check")
    parser.add_argument("--all-statements", action="store_true", help="check every statement_translation target")
    parser.add_argument(
        "--candidate-file",
        type=Path,
        help="JSON or JSONL proof-body candidates with record_id, proof, and optional statement/candidate_id",
    )
    parser.add_argument("--disallow-sorry", action="store_true", help="fail if any proof candidate uses sorry")
    parser.add_argument(
        "--repair-simple",
        action="store_true",
        help="apply simple local proof repairs such as no-progress tactic drops and ring-to-ring_nf replacements",
    )
    parser.add_argument("--candidate", help="candidate theorem statement text or path; defaults to record target")
    parser.add_argument("--proof", help="candidate proof body text or path; defaults to `sorry`")
    parser.add_argument("--lean-project", type=Path, default=DEFAULT_LEAN_PROJECT)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument("--output", type=Path, help="optional report output path")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if not args.all_statements and not args.record_id and not args.candidate_file:
        raise SystemExit("error: pass --record-id, --all-statements, or --candidate-file")

    try:
        if args.candidate_file:
            candidate_items = load_candidate_items(args.candidate_file)
            try:
                results = check_proof_candidates_batch(candidate_items, args.lean_project, args.timeout)
            except subprocess.TimeoutExpired:
                results = None
            if results is None:
                results = []
                for item in candidate_items:
                    try:
                        results.append(check_proof_candidate(item, args.lean_project, args.timeout, args.repair_simple))
                    except (subprocess.TimeoutExpired, ValueError) as exc:
                        results.append(
                            {
                                "record_id": item.get("record_id", "__unknown__"),
                                "formal_file": "__unknown__",
                                "mode": "proof_body_candidate",
                                "candidate_id": item.get("candidate_id"),
                                "passed": False,
                                "returncode": None,
                                "stdout": "",
                                "stderr": str(exc),
                                "contains_sorry": "sorry" in item.get("proof", ""),
                                "batch_compiled": False,
                            }
                        )
        elif args.all_statements:
            records = load_records()
            source = build_all_statements_source(records)
            result = run_lean(source, args.lean_project, args.timeout)
            results = [
                {
                    "record_id": "__all_statement_targets__",
                    "record_count": len(records),
                    "formal_file": "__multiple__",
                    "mode": "all_statements_with_sorry",
                    **result,
                }
            ]
        else:
            record = record_by_id(args.record_id)
            statement = read_text_argument(args.candidate, statement_translation_target(record))
            proof = read_text_argument(args.proof, "sorry")
            source = build_candidate_source(record, statement, proof, candidate_name(record["id"]))
            result = run_lean(source, args.lean_project, args.timeout)
            results = [
                {
                    "record_id": record["id"],
                    "formal_file": record["formal"]["file"],
                    "mode": "candidate",
                    **result,
                }
            ]
    except (subprocess.TimeoutExpired, ValueError) as exc:
        if args.json:
            print(json.dumps({"passed": False, "error": str(exc)}, indent=2, sort_keys=True))
        else:
            print(f"error: {exc}", file=sys.stderr)
        return 1

    payload = {
        "schema_version": "0.1.0",
        "report_kind": "lean_candidate_check",
        "lean_project": str(args.lean_project),
        "results": results,
        "passed": all(result["passed"] for result in results),
        "summary": summarize_results(results),
    }
    if args.disallow_sorry and any(result.get("contains_sorry") for result in results):
        payload["passed"] = False
        payload["error"] = "one or more proof candidates use sorry"
    if args.json:
        output = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    else:
        from io import StringIO
        import contextlib

        buffer = StringIO()
        with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(buffer):
            for result in results:
                print_text_result(result)
        output = buffer.getvalue()

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output, encoding="utf-8")
    else:
        print(output, end="")

    return 0 if payload["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
