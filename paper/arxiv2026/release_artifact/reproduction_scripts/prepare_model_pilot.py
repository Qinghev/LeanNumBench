"""Prepare local prompt packs for a LeanNumBench model pilot manifest.

This script does not call model APIs. It turns a tracked pilot manifest into
ignored local JSONL files that can be handed to a model runner and later scored
with the existing Lean candidate checker.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


def resolve_layout(root: Path) -> tuple[Path, Path, Path, Path]:
    repo_theorem_root = root / "records" / "theorems"
    repo_index = repo_theorem_root / "index.json"
    if repo_index.is_file():
        return (
            repo_theorem_root,
            repo_index,
            (root / ".." / "LeanNumerics").resolve(),
            root / "data" / "model_pilots",
        )

    artifact_theorem_root = root / "records" / "theorems"
    artifact_index = root / "records" / "index.json"
    if artifact_index.is_file() and artifact_theorem_root.is_dir():
        return (
            artifact_theorem_root,
            artifact_index,
            (root / "companion_lean").resolve(),
            root / "_repro" / "model_pilots",
        )

    return (
        repo_theorem_root,
        repo_index,
        (root / ".." / "LeanNumerics").resolve(),
        root / "data" / "model_pilots",
    )


THEOREM_ROOT, INDEX_PATH, DEFAULT_LEAN_PROJECT, DEFAULT_OUTPUT_ROOT = resolve_layout(ROOT)
TASK_OUTPUT_KIND = {
    "statement_translation": "lean_theorem_statement",
    "proof_completion": "lean_proof_body",
    "theorem_retrieval": "lean_declaration_names",
}
SOURCE_DECLARATION_CONTEXT_MODES = {"full", "none"}
IDENTIFIER_PATTERN = re.compile(r"\b[A-Za-z_][A-Za-z0-9_'.]*\b")
DECLARATION_PATTERN = re.compile(r"^\s*(?:noncomputable\s+)?(?:def|theorem)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b")
COMMON_WORDS = {
    "A",
    "Burgers",
    "Heat",
    "KdV",
    "Given",
    "Lean",
    "ODE",
    "PDE",
    "The",
    "a",
    "against",
    "and",
    "as",
    "by",
    "complete",
    "definition",
    "definitions",
    "equation",
    "for",
    "from",
    "generic",
    "lemma",
    "lemmas",
    "of",
    "proof",
    "referenced",
    "scaffold",
    "statement",
    "the",
    "theorem",
    "to",
    "using",
    "with",
}


def load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return data


def require_string(data: dict[str, Any], key: str, context: str) -> str:
    value = data.get(key)
    if not isinstance(value, str) or not value:
        raise ValueError(f"{context}: missing string field {key!r}")
    return value


def load_records_by_id() -> dict[str, dict[str, Any]]:
    index = load_json(INDEX_PATH)
    records: dict[str, dict[str, Any]] = {}
    for item in index["records"]:
        record = load_json(THEOREM_ROOT / item["path"])
        records[record["id"]] = record
    return records


def task_map(record: dict[str, Any]) -> dict[str, dict[str, str]]:
    tasks: dict[str, dict[str, str]] = {}
    for task in record["tasks"]:
        tasks[task["task"]] = task
    return tasks


def theorem_statement(record: dict[str, Any]) -> str:
    theorem_declarations = [
        declaration["statement"]
        for declaration in record["formal"]["declarations"]
        if declaration["kind"] == "theorem"
    ]
    if not theorem_declarations:
        raise ValueError(f"{record['id']}: no theorem declaration")
    return theorem_declarations[-1]


def theorem_name(record: dict[str, Any]) -> str:
    theorem_declarations = [
        declaration["name"]
        for declaration in record["formal"]["declarations"]
        if declaration["kind"] == "theorem"
    ]
    if not theorem_declarations:
        raise ValueError(f"{record['id']}: no theorem declaration")
    return theorem_declarations[-1]


def definition_context(record: dict[str, Any]) -> str:
    definitions = [
        declaration["statement"]
        for declaration in record["formal"]["declarations"]
        if declaration["kind"] == "definition"
    ]
    if not definitions:
        return "No local definitions are listed in this record."
    return "\n".join(definitions)


def declaration_name_list(record: dict[str, Any]) -> str:
    declarations = [
        f"- {declaration['name']} ({declaration['kind']})"
        for declaration in record["formal"]["declarations"]
    ]
    return "\n".join(declarations)


def declaration_headers_from_file(source_path: Path, stop_name: str | None = None) -> list[tuple[str, str]]:
    declarations = []
    lines = source_path.read_text(encoding="utf-8").splitlines()
    index = 0
    while index < len(lines):
        line = lines[index]
        match = DECLARATION_PATTERN.match(line)
        if not match:
            index += 1
            continue
        name = match.group(1)
        if name == stop_name:
            break
        header_lines = [line.rstrip()]
        index += 1
        while index < len(lines) and ":=" not in header_lines[-1]:
            if DECLARATION_PATTERN.match(lines[index]):
                break
            header_lines.append(lines[index].rstrip())
            index += 1
        header = "\n".join(header_lines)
        if ":=" in header:
            header = header.split(":=", 1)[0].rstrip()
        declarations.append((name, header))
    return declarations


def nearby_source_declarations(record: dict[str, Any], lean_project: Path = DEFAULT_LEAN_PROJECT) -> list[tuple[str, str]]:
    source_path = lean_project / record["formal"]["file"]
    if not source_path.is_file():
        return []
    target_name = theorem_name(record)
    declarations = declaration_headers_from_file(source_path, stop_name=target_name)
    return declarations[-20:]


def local_import_source_path(module_name: str, lean_project: Path = DEFAULT_LEAN_PROJECT) -> Path | None:
    if not module_name.startswith("LeanNumerics."):
        return None
    return lean_project / Path(*module_name.split(".")).with_suffix(".lean")


def imported_source_declarations(
    record: dict[str, Any],
    lean_project: Path = DEFAULT_LEAN_PROJECT,
) -> list[tuple[str, list[tuple[str, str]]]]:
    target_name = theorem_name(record)
    groups = []
    for module_name in record["formal"].get("imports", []):
        source_path = local_import_source_path(module_name, lean_project)
        if source_path is None or not source_path.is_file():
            continue
        declarations = [
            (name, header)
            for name, header in declaration_headers_from_file(source_path)
            if name != target_name
        ]
        if declarations:
            groups.append((module_name, declarations[-20:]))
    return groups


def declaration_header_list(declarations: list[tuple[str, str]]) -> str:
    if not declarations:
        return "- None"
    rows = []
    for _name, header in declarations:
        header_lines = [line.strip() for line in header.splitlines() if line.strip()]
        if not header_lines:
            continue
        rows.append("- " + header_lines[0])
        rows.extend("  " + line for line in header_lines[1:])
    return "\n".join(rows) if rows else "- None"


def source_declaration_context(record: dict[str, Any]) -> str:
    sections = []
    nearby_declarations = nearby_source_declarations(record)
    if nearby_declarations:
        sections.append(
            "Same Lean source file before the target theorem:\n" + declaration_header_list(nearby_declarations)
        )
    for module_name, declarations in imported_source_declarations(record):
        sections.append(f"Imported local module {module_name}:\n" + declaration_header_list(declarations))
    if not sections:
        return "No local source declaration list is available."
    return "\n\n".join(sections)


def referenced_identifiers(text: str) -> list[str]:
    identifiers = []
    seen = set()
    for identifier in IDENTIFIER_PATTERN.findall(text):
        if identifier in COMMON_WORDS:
            continue
        if "_" not in identifier and not any(char.isupper() for char in identifier[1:]):
            continue
        if identifier not in seen:
            identifiers.append(identifier)
            seen.add(identifier)
    return identifiers


def proof_guidance(record: dict[str, Any], task: dict[str, str]) -> str:
    tags = set(record["tags"])
    category = record["category"]
    guidance = [
        "Lean 4 proof-body rules:",
        "- Return only tactic/proof lines that follow `:= by`.",
        "- Do not include `theorem`, `namespace`, `end`, Markdown fences, prose, or comments only.",
        "- Do not use Lean 3 tactic commas; write one Lean 4 tactic line at a time.",
        "- The theorem parameters and named hypotheses in the statement are already in scope.",
        "- Do not `intro` theorem-header binders that are already named in the statement.",
        "- Use exact declaration names from the prompt; do not invent snake_case aliases.",
    ]
    references = referenced_identifiers(task["input"])
    if references:
        guidance.extend(
            [
                "",
                "Referenced names from the task input:",
                bullet_list(references),
                "If a referenced theorem almost matches the goal, prefer `simpa [localDefinition] using referencedTheorem ...`.",
            ]
        )
    guidance.extend(
        [
            "",
            "Definition-unfolding rules:",
            "- For theorem names ending in `_eq` or direct definition-unfolding goals, try `rfl` or `unfold exactName1 exactName2` followed by `rfl`.",
            "- For algebraic constant-state goals, prefer one `unfold ...` line listing all exact definitions, then `ring` or `ring_nf`.",
            "- When a wrapper definition calls imported base definitions, unfold both the wrapper and those base definitions before algebraic tactics.",
            "- When using a theorem from the context, match the displayed binder order and do not pass variables absent from that theorem signature.",
            "- Avoid inserting `simp` between definition unfolding and `ring` unless it is clearly needed.",
            "- For conjunction goals, split the goal with `constructor`; for nested conjunctions, use a nested `constructor` block or `constructor <;> linarith` when both subgoals are linear arithmetic.",
        ]
    )
    if "kdv" in tags:
        guidance.extend(
            [
                "",
                "KdV naming rules:",
                "- Use camelCase names such as `kdvConservativeFlux`, `kdvConservativeUpdate`, `kdvCanonicalFlux`, and `kdvCanonicalUpdate`.",
                "- Do not invent names such as `kdv_flux`, `kdvUpdate`, `kdvFluxDiff`, or `Grid`.",
                "- For `fluxDifference (kdvConservativeFlux ... (fun _ => c)) i = 0`, prefer `unfold fluxDifference kdvConservativeFlux secondForwardDifference` followed by `ring`; do not try to use `fluxDifference_const_zero` through `simpa` unless the flux has already been rewritten to a syntactic constant function.",
                "- For `kdvCanonicalUpdate_eq`, use the full wrapper chain: `unfold kdvCanonicalUpdate kdvConservativeUpdate conservativeUpdate fluxDifference kdvCanonicalFlux` followed by `rfl`.",
                "- For canonical KdV constant-state wrapper goals, prefer `unfold kdvCanonicalUpdate` then `exact kdvConservativeUpdate_const_state scale 3 1 c i` with the displayed binder names.",
                "- For KdV total-preservation wrapper theorems, keep the proof short: unfold `kdvConservativeUpdate` and apply `totalOn_conservativeUpdate_of_boundary_eq` or `totalOn_conservativeUpdate_of_periodicBoundary` with the displayed binders.",
            ]
        )
    if "heat_equation" in tags:
        guidance.extend(
            [
                "",
                "Heat-equation proof rules:",
                "- Prefer exact names beginning with `heat...` from the theorem statement and task input.",
                "- Do not use Lean 3 comma chaining such as `rw [...],`.",
                "- For heat grid total-balance goals, prefer a multiline `calc` proof over one large `simp_rw` list.",
                "- For finite-sum balance proofs, use `apply Finset.sum_congr` for pointwise grid rewrites, then separate `rw` steps for `Finset.sum_add_distrib`, `Finset.mul_sum`, and boundary/telescoping lemmas.",
                "- For `heatWeights_nonneg`, after unfolding the three weight definitions, split the nested conjunction and solve the linear subgoals with `exact hr0` or `linarith`.",
                "- For `heatSecondDifference_sum_range`, in the successor case use `rw [Finset.sum_range_succ, ih]`, then `unfold heatSecondDifference heatBoundaryTerm`, then `ring`; do not put these definitions in the `rw` list.",
                "- For `heatStep_abs_le`, first split `(left + center) + right` with `abs_add_le (heatLeftWeight r * uLeft + heatCenterWeight r * u) (heatRightWeight r * uRight)`, then split the left-center pair with `abs_add_le (heatLeftWeight r * uLeft) (heatCenterWeight r * u)`.",
                "- In the second `heatStep_abs_le` calc inequality, do not use `add_le_add_right`; instead introduce `have hTri : |heatLeftWeight r * uLeft + heatCenterWeight r * u| <= |heatLeftWeight r * uLeft| + |heatCenterWeight r * u| := by exact abs_add_le ...`, then close that calc step with `linarith`.",
                "- In that heat stability proof, rewrite with `abs_mul` and `abs_of_nonneg`, use `mul_le_mul_of_nonneg_left` for the three bounded inputs, and finish with the heat weight sum by unfolding weights and `ring`.",
                "- Do not put a binder-taking theorem such as `heatStepGrid_eq_center_plus_heatSecondDifference` in the same rewrite list as `Finset.sum_add_distrib`.",
            ]
        )
    if "burgers" in tags:
        guidance.extend(
            [
                "",
                "Burgers proof rules:",
                "- Use exact names such as `burgersFlux`, `burgersConservativeUpdate`, and the referenced `totalOn_burgers...` lemmas.",
                "- Do not invent generic predicates such as `totalPreserved`.",
            ]
        )
    if tags & {"conservation", "total_balance", "total_preservation", "boundary_flux", "periodic_boundary", "discrete_mass"}:
        guidance.extend(
            [
                "",
                "Conservation/telescoping proof rules:",
                "- Prefer the existing total/boundary lemma named in the task input.",
                "- Use `simpa [wrapperDefinition] using ...` when the theorem is a wrapper around an imported lemma.",
                "- Avoid expanding finite sums from scratch unless the task explicitly asks for it.",
                "- Keep wrapper proofs under a few tactic lines; do not re-prove generic telescoping sums when an imported theorem is listed.",
            ]
        )
    if tags & {"constant_state", "convex_combination", "ring", "field_simp"}:
        guidance.extend(
            [
                "",
                "Algebraic proof rules:",
                "- For direct algebraic goals, prefer `unfold ...` followed by `ring` or `ring_nf`.",
                "- If `ring` leaves a normalized arithmetic goal, try `ring_nf`.",
            ]
        )
    if tags & {"convex_combination", "linf_stability", "nonnegative_weights"}:
        guidance.extend(
            [
                "",
                "Stability and convex-combination proof rules:",
                "- Use the theorem name `abs_add_le`, not `abs_add`.",
                "- For two-term L-infinity stability, use `abs_add_le`, rewrite products with `abs_mul` and `abs_of_nonneg`, bound both products using `mul_le_mul_of_nonneg_left`, then finish with the weight-sum algebra.",
                "- For nonnegative weight pairs such as Lax-Friedrichs, after unfolding definitions use `constructor <;> linarith` rather than nested bullet scripts with extra subgoals.",
            ]
        )
    if "general_n" in tags:
        guidance.extend(
            [
                "",
                "General-N finite-index proof rules:",
                "- Unfold all local LeanNumerics definitions needed by the goal, including definitions nested inside other definitions, before using algebraic tactics.",
                "- For finite-sum algebra, prefer library lemmas over manual induction: `Finset.sum_sub_distrib`, `Finset.sum_const`, `Finset.sum_mul`, `Finset.sum_congr`, `Finset.sum_le_sum`, and `Finset.abs_sum_le_sum_abs`.",
                "- Use namespaced Mathlib lemma names such as `Finset.abs_sum_le_sum_abs`; do not use unqualified or invented names.",
                "- Avoid `Finset.induction_on` unless the theorem statement provides all required typeclass assumptions such as `DecidableEq`.",
                "- For finite means or weighted averages, clear denominators only after the target is unfolded and normalized; use `field_simp [hcard]` or `field_simp [hmass]` when those hypotheses appear, then `ring`.",
                "- For row-stochastic absolute-value inequalities, use `Finset.abs_sum_le_sum_abs` followed by `Finset.sum_le_sum`; do not try `apply Finset.sum`.",
            ]
        )
        if category == "spectral_dft":
            guidance.extend(
                [
                    "- For centered-signal/DC finite-sum goals, unfold the wrapper and nested mean/DC definitions together, for example `unfold centeredSignal finiteMean finiteDC`.",
                    "- For sums of centered values, the useful normalization lemmas are usually `Finset.sum_sub_distrib`, `Finset.sum_const`, `nsmul_eq_mul`, `field_simp`, and `ring`.",
                ]
            )
        if category == "fem_projection":
            guidance.extend(
                [
                    "- For weighted P0 residual orthogonality, factor the constant out of the finite sum with `Finset.sum_mul`, then reuse the available residual-mass-zero theorem.",
                ]
            )
        if category == "linear_algebra_stability":
            guidance.extend(
                [
                    "- For finite row-application bounds, unfold the row-apply definition, use `Finset.abs_sum_le_sum_abs`, rewrite `|a i * x i|` with `abs_mul` and `abs_of_nonneg`, then bound terms with `mul_le_mul_of_nonneg_left`.",
                ]
            )
    if category == "interpolation_linear":
        guidance.extend(
            [
                "",
                "Interpolation proof rules:",
                "- For affine interpolation, unfold `affineInterp` and use `ring` unless the goal is an absolute-value stability bound.",
                "- For linear interpolation endpoint/constant facts, unfold `linearInterp`, clear the nonzero denominator with `field_simp [h]`, then use `ring`.",
                "- For interpolation stability bounds, use `abs_add_le`, rewrite products with `abs_mul` and `abs_of_nonneg`, then bound each weighted endpoint with `mul_le_mul_of_nonneg_left`.",
            ]
        )
    if category == "quadrature_rules":
        guidance.extend(
            [
                "",
                "Quadrature proof rules:",
                "- For midpoint and trapezoid linearity/exactness, unfold the quadrature definition and use `ring`.",
                "- For quadrature nonnegativity, unfold the rule and use `mul_nonneg`, `add_nonneg`, and `nlinarith`.",
            ]
        )
    return "\n".join(guidance)


def statement_guidance(record: dict[str, Any]) -> str:
    tags = set(record["tags"])
    guidance = [
        "Lean 4 theorem-statement rules:",
        "- Return exactly one Lean theorem declaration starting with `theorem`.",
        "- Do not include `:=`, `:= by`, proof text, Markdown fences, prose, comments, or a trailing colon.",
        "- Use exact camelCase identifiers from the available declaration signatures; do not invent snake_case aliases.",
        "- The candidate checker will rename the theorem, so the theorem name is less important than the binders and proposition.",
        "- Prefer named local definitions such as `totalOn`, `discreteMass`, `heatInteriorTotal`, and `heatStepGridTotal` over expanding finite sums from scratch.",
        "- If a finite sum is unavoidable, use Lean syntax `Finset.sum (Finset.range n) (fun i => ...)`.",
    ]
    if "kdv" in tags:
        guidance.extend(
            [
                "",
                "KdV statement rules:",
                "- Use `kdvConservativeFlux`, `kdvConservativeUpdate`, `kdvCanonicalFlux`, and `kdvCanonicalUpdate` exactly.",
                "- Do not invent names such as `kdvUpdate`, `kdvFlux`, `kdv_flux`, or `kdv_conservative_update`.",
            ]
        )
    if "burgers" in tags:
        guidance.extend(
            [
                "",
                "Burgers statement rules:",
                "- Use `burgersFlux` and `burgersConservativeUpdate` exactly.",
                "- Do not expand Burgers totals with raw sum notation if a `totalOn` theorem is being requested.",
            ]
        )
    if "heat_equation" in tags:
        guidance.extend(
            [
                "",
                "Heat-equation statement rules:",
                "- Use exact names such as `heatStep`, `heatStepGrid`, `heatSecondDifference`, `heatInteriorTotal`, and `heatStepGridTotal`.",
                "- Keep CFL and boundary hypotheses as named Lean binders when they appear in the informal assumptions.",
            ]
        )
    if tags & {"conservation", "total_balance", "total_preservation", "boundary_flux", "periodic_boundary", "discrete_mass"}:
        guidance.extend(
            [
                "",
                "Conservation statement rules:",
                "- Use `totalOn u n` and `periodicBoundary flux n` exactly when those concepts appear.",
                "- For boundary-equality assumptions, write a named hypothesis such as `(hflux : flux n = flux 0)`.",
            ]
        )
    return "\n".join(guidance)


def bullet_list(items: list[str]) -> str:
    if not items:
        return "- None"
    return "\n".join(f"- {item}" for item in items)


def common_header(record: dict[str, Any]) -> str:
    formal = record["formal"]
    return "\n".join(
        [
            f"Record id: {record['id']}",
            f"Title: {record['title']}",
            f"Category: {record['category']}",
            f"Difficulty: {record['difficulty']}",
            f"Lean imports: {', '.join(formal['imports'])}",
            f"Namespace: {' / '.join(formal.get('namespace', []))}",
            "",
            "Local definitions available to use:",
            definition_context(record),
        ]
    )


def prompt_options(manifest: dict[str, Any]) -> dict[str, Any]:
    options = manifest.get("prompt_options", {})
    if not isinstance(options, dict):
        raise ValueError("manifest: prompt_options must be an object when present")
    return {
        "source_declaration_context": options.get("source_declaration_context", "full"),
    }


def source_declaration_context_sections(
    record: dict[str, Any],
    options: dict[str, Any],
    heading: str,
) -> list[str]:
    if options.get("source_declaration_context", "full") == "none":
        return []
    return [heading, source_declaration_context(record)]


def build_prompt(record: dict[str, Any], task: dict[str, str], options: dict[str, Any]) -> str:
    task_name = task["task"]
    informal = record["informal"]
    if task_name == "statement_translation":
        return "\n\n".join(
            [
                "You are formalizing a numerical-analysis theorem in Lean 4. Return only one Lean theorem statement.",
                common_header(record),
                *source_declaration_context_sections(
                    record,
                    options,
                    "Relevant local declaration signatures already available through the Lean imports:",
                ),
                "Informal theorem:",
                informal["statement"],
                "LaTeX:",
                informal["latex"],
                "Assumptions:",
                bullet_list(informal["assumptions"]),
                "Expected conclusion:",
                informal["expected_conclusion"],
                "Task input:",
                task["input"],
                "Statement guidance:",
                statement_guidance(record),
            ]
        )
    if task_name == "proof_completion":
        return "\n\n".join(
            [
                "You are completing a Lean 4 proof for a numerical-analysis theorem. Return only the proof body that follows `:= by`.",
                common_header(record),
                "Formal declarations listed in this benchmark record:",
                declaration_name_list(record),
                *source_declaration_context_sections(
                    record,
                    options,
                    "Relevant local declaration names already available through the Lean imports:",
                ),
                "Theorem statement to prove:",
                theorem_statement(record),
                "Task input:",
                task["input"],
                "Proof guidance:",
                proof_guidance(record, task),
            ]
        )
    if task_name == "theorem_retrieval":
        return "\n\n".join(
            [
                "You are retrieving useful Lean declaration names for a numerical-analysis formalization task.",
                common_header(record),
                "Task input:",
                task["input"],
                "Output rules: return only a comma-separated list of Lean declaration names; do not include explanations.",
            ]
        )
    raise ValueError(f"unsupported task {task_name!r}")


def safe_id(text: str) -> str:
    return "".join(char if char.isalnum() else "_" for char in text)


def validate_manifest(manifest: dict[str, Any], records_by_id: dict[str, dict[str, Any]]) -> None:
    if manifest.get("schema_version") != "0.1.0":
        raise ValueError("manifest schema_version must be 0.1.0")
    require_string(manifest, "pilot_id", "manifest")
    tasks = manifest.get("tasks")
    if not isinstance(tasks, list) or not tasks:
        raise ValueError("manifest: tasks must be a nonempty list")
    for task in tasks:
        if task not in TASK_OUTPUT_KIND:
            raise ValueError(f"manifest: unsupported task {task!r}")
    options = prompt_options(manifest)
    source_context_mode = options["source_declaration_context"]
    if source_context_mode not in SOURCE_DECLARATION_CONTEXT_MODES:
        raise ValueError(
            "manifest: prompt_options.source_declaration_context must be one of "
            f"{sorted(SOURCE_DECLARATION_CONTEXT_MODES)}"
        )
    entries = manifest.get("records")
    if not isinstance(entries, list) or not entries:
        raise ValueError("manifest: records must be a nonempty list")
    seen: set[str] = set()
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            raise ValueError(f"manifest record {index}: expected object")
        record_id = require_string(entry, "record_id", f"manifest record {index}")
        if record_id in seen:
            raise ValueError(f"manifest: duplicate record id {record_id}")
        seen.add(record_id)
        if record_id not in records_by_id:
            raise ValueError(f"manifest: unknown record id {record_id}")
        selected_tasks = entry.get("task_overrides", tasks)
        if not isinstance(selected_tasks, list) or not selected_tasks:
            raise ValueError(f"manifest record {record_id}: selected tasks must be a nonempty list")
        available_tasks = task_map(records_by_id[record_id])
        for task in selected_tasks:
            if task not in TASK_OUTPUT_KIND:
                raise ValueError(f"manifest record {record_id}: unsupported task {task!r}")
            if task not in available_tasks:
                raise ValueError(f"manifest record {record_id}: record has no {task!r} task")


def prompt_variant(record: dict[str, Any], task_name: str, options: dict[str, Any]) -> str:
    suffix = ""
    if options.get("source_declaration_context", "full") == "none":
        suffix = "_no_decl_context"
    if task_name == "proof_completion":
        tags = set(record["tags"])
        if "general_n" in tags or str(record["id"]).endswith("_general_n"):
            return "proof_completion_v11_general_n" + suffix
        return "proof_completion_v10" + suffix
    return "statement_translation_v2" + suffix


def build_rows(manifest: dict[str, Any], records_by_id: dict[str, dict[str, Any]]) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    pilot_id = manifest["pilot_id"]
    default_tasks = manifest["tasks"]
    options = prompt_options(manifest)
    prompt_rows = []
    target_rows = []
    candidate_rows = []

    for entry in manifest["records"]:
        record = records_by_id[entry["record_id"]]
        tasks = entry.get("task_overrides", default_tasks)
        available_tasks = task_map(record)
        for task_name in tasks:
            task = available_tasks[task_name]
            prompt_id = f"{pilot_id}:{record['id']}:{task_name}"
            prompt_rows.append(
                {
                    "schema_version": "0.1.0",
                    "pilot_id": pilot_id,
                    "prompt_id": prompt_id,
                    "record_id": record["id"],
                    "task": task_name,
                    "category": record["category"],
                    "difficulty": record["difficulty"],
                    "expected_output": TASK_OUTPUT_KIND[task_name],
                    "prompt_variant": prompt_variant(record, task_name, options),
                    "prompt_options": options,
                    "prompt": build_prompt(record, task, options),
                }
            )
            target_rows.append(
                {
                    "schema_version": "0.1.0",
                    "pilot_id": pilot_id,
                    "prompt_id": prompt_id,
                    "record_id": record["id"],
                    "task": task_name,
                    "category": record["category"],
                    "difficulty": record["difficulty"],
                    "target": task["target"],
                    "formal_statement": theorem_statement(record),
                }
            )
            candidate_rows.append(
                {
                    "schema_version": "0.1.0",
                    "pilot_id": pilot_id,
                    "prompt_id": prompt_id,
                    "record_id": record["id"],
                    "task": task_name,
                    "candidate_id": f"{pilot_id}:{safe_id(record['id'])}:{task_name}:model_name",
                    "prediction": "",
                }
            )
    return prompt_rows, target_rows, candidate_rows


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def counter_dict(counter: Counter[str | int]) -> dict[str, int]:
    return {str(key): counter[key] for key in sorted(counter)}


def summarize(manifest: dict[str, Any], prompt_rows: list[dict[str, Any]], output_dir: Path) -> dict[str, Any]:
    return {
        "schema_version": "0.1.0",
        "report_kind": "model_pilot_preparation",
        "pilot_id": manifest["pilot_id"],
        "output_dir": str(output_dir.relative_to(ROOT)),
        "records": len(manifest["records"]),
        "prompts": len(prompt_rows),
        "by_task": counter_dict(Counter(row["task"] for row in prompt_rows)),
        "by_category": counter_dict(Counter(row["category"] for row in prompt_rows)),
        "by_difficulty": counter_dict(Counter(row["difficulty"] for row in prompt_rows)),
        "prompt_options": prompt_options(manifest),
        "files": {
            "manifest": str((output_dir / "manifest.json").relative_to(ROOT)),
            "prompts": str((output_dir / "prompts.jsonl").relative_to(ROOT)),
            "targets": str((output_dir / "targets.jsonl").relative_to(ROOT)),
            "candidate_template": str((output_dir / "candidate_template.jsonl").relative_to(ROOT)),
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path, help="model pilot manifest JSON")
    parser.add_argument("--output-root", type=Path, default=DEFAULT_OUTPUT_ROOT)
    parser.add_argument("--run-id", help="output directory name; defaults to manifest pilot_id")
    parser.add_argument("--json", action="store_true", help="emit machine-readable summary")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    manifest_path = args.manifest.resolve()
    manifest = load_json(manifest_path)
    records_by_id = load_records_by_id()
    validate_manifest(manifest, records_by_id)

    prompt_rows, target_rows, candidate_rows = build_rows(manifest, records_by_id)
    run_id = args.run_id or manifest["pilot_id"]
    output_dir = args.output_root.resolve() / run_id
    output_dir.mkdir(parents=True, exist_ok=True)

    shutil.copyfile(manifest_path, output_dir / "manifest.json")
    write_jsonl(output_dir / "prompts.jsonl", prompt_rows)
    write_jsonl(output_dir / "targets.jsonl", target_rows)
    write_jsonl(output_dir / "candidate_template.jsonl", candidate_rows)

    summary = summarize(manifest, prompt_rows, output_dir)
    (output_dir / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print(f"Prepared {summary['prompts']} prompts from {summary['records']} records.")
        print(f"Output: {summary['output_dir']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
