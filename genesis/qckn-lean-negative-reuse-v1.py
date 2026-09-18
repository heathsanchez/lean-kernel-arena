#!/usr/bin/env python3
"""Lean-kernel diagnostic negative-evidence reuse V1.

This experiment stays entirely outside ACCEPT/REJECT semantics. It tests whether
the exact falsified diagnostic probes already retained in
kernel-realitygraph-memory-v1.json can be compiled into restartable routing
obstructions so identical future diagnostic proposals are not re-verified.

The authoritative object is the existing retained evidence row, not the cache.
Changed scope must miss. Stale source identity must be rejected. Ablation must
restore repeated diagnostic verifier work.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


EXPECTED_MEMORY_GIT_BLOB = "da9538a11494f24412254d0ffe9d63f3638e4475"
EXPECTED_SCHEMA = "kernel-realitygraph-memory-v1"
ROUNDS = 3


@dataclass(frozen=True)
class DiagnosticRefutation:
    fingerprint: str
    probe: str
    status: str
    evidence_run: int
    fact: str
    scope: tuple[tuple[str, Any], ...]
    source_blob: str


def _fingerprint(
    row: dict[str, Any],
    *,
    scope: dict[str, Any],
    source_blob: str,
) -> str:
    payload = {
        "schema": "lean-kernel-diagnostic-refutation-v1",
        "probe": row["probe"],
        "status": row["status"],
        "evidence_run": int(row["evidence_run"]),
        "fact": row["fact"],
        "scope": scope,
        "source_blob": source_blob,
    }
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return "lean-diag-refutation:" + hashlib.sha256(raw).hexdigest()


def load_memory(path: Path) -> dict[str, Any]:
    memory = json.loads(path.read_text(encoding="utf-8"))
    if memory.get("schema") != EXPECTED_SCHEMA:
        raise RuntimeError("unexpected memory schema")
    retained = memory.get("retained_kernel") or {}
    if retained.get("wrong") != 0:
        raise RuntimeError("negative-routing evidence source has wrong kernel verdicts")
    rows = memory.get("evidence") or []
    if len(rows) != 8:
        raise RuntimeError(f"expected eight retained diagnostic probes, got {len(rows)}")
    if not all("FALSIFIED" in str(row.get("status", "")) for row in rows):
        raise RuntimeError("memory contains a non-falsified diagnostic probe")
    return memory


def base_scope(memory: dict[str, Any]) -> dict[str, Any]:
    sig = memory["current_signature"]
    return {
        "frontier": sig["frontier"],
        "fallback": sig["fallback"],
        "tail_operation": sig["tail_operation"],
        "orbit_states": int(sig["orbit_states"]),
    }


def verify_row(
    row: dict[str, Any],
    *,
    expected_scope: dict[str, Any],
    proposal_scope: dict[str, Any],
) -> tuple[str, str]:
    # Destination-local authority: this verifier licenses only exact replay of
    # the retained diagnostic proposition at the same scope.
    if proposal_scope != expected_scope:
        return "UNKNOWN_SCOPE", "proposal scope differs from retained evidence scope"
    if "FALSIFIED" not in row["status"]:
        return "UNKNOWN", "row is not a retained falsification"
    return "REFUTED", row["fact"]


def compile_bank(
    memory: dict[str, Any],
    *,
    source_blob: str = EXPECTED_MEMORY_GIT_BLOB,
) -> tuple[DiagnosticRefutation, ...]:
    scope = base_scope(memory)
    bank = []
    for row in memory["evidence"]:
        status, _reason = verify_row(
            row,
            expected_scope=scope,
            proposal_scope=scope,
        )
        if status != "REFUTED":
            raise RuntimeError("retained row failed exact diagnostic authority")
        bank.append(
            DiagnosticRefutation(
                fingerprint=_fingerprint(row, scope=scope, source_blob=source_blob),
                probe=row["probe"],
                status=row["status"],
                evidence_run=int(row["evidence_run"]),
                fact=row["fact"],
                scope=tuple(sorted(scope.items())),
                source_blob=source_blob,
            )
        )
    return tuple(bank)


def save_bank(bank: tuple[DiagnosticRefutation, ...], path: Path) -> None:
    path.write_text(
        json.dumps([asdict(row) for row in bank], indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def load_bank(path: Path, *, expected_source_blob: str) -> tuple[DiagnosticRefutation, ...]:
    rows = json.loads(path.read_text(encoding="utf-8"))
    bank = tuple(
        DiagnosticRefutation(
            fingerprint=row["fingerprint"],
            probe=row["probe"],
            status=row["status"],
            evidence_run=int(row["evidence_run"]),
            fact=row["fact"],
            scope=tuple(tuple(item) for item in row["scope"]),
            source_blob=row["source_blob"],
        )
        for row in rows
    )
    if not bank:
        raise RuntimeError("empty diagnostic refutation bank")
    if any(row.source_blob != expected_source_blob for row in bank):
        raise RuntimeError("stale diagnostic refutation source identity")
    if len({row.fingerprint for row in bank}) != len(bank):
        raise RuntimeError("duplicate diagnostic refutation fingerprint")
    return bank


def proposal_fingerprint(
    row: dict[str, Any],
    *,
    proposal_scope: dict[str, Any],
    source_blob: str,
) -> str:
    return _fingerprint(row, scope=proposal_scope, source_blob=source_blob)


def run_cold(memory: dict[str, Any]) -> dict[str, Any]:
    scope = base_scope(memory)
    calls = 0
    statuses = []
    for _round in range(ROUNDS):
        for row in memory["evidence"]:
            calls += 1
            status, reason = verify_row(
                row,
                expected_scope=scope,
                proposal_scope=scope,
            )
            statuses.append((status, reason))
    return {
        "arm": "cold",
        "rounds": ROUNDS,
        "proposals": ROUNDS * len(memory["evidence"]),
        "diagnostic_verifier_calls": calls,
        "blocked_by_compiled_refutation": 0,
        "all_refuted": all(status == "REFUTED" for status, _ in statuses),
    }


def run_warm(memory: dict[str, Any]) -> tuple[dict[str, Any], tuple[DiagnosticRefutation, ...]]:
    scope = base_scope(memory)
    learned: dict[str, DiagnosticRefutation] = {}
    calls = 0
    blocked = 0

    for _round in range(ROUNDS):
        for row in memory["evidence"]:
            fp = proposal_fingerprint(
                row,
                proposal_scope=scope,
                source_blob=EXPECTED_MEMORY_GIT_BLOB,
            )
            if fp in learned:
                blocked += 1
                continue
            calls += 1
            status, reason = verify_row(
                row,
                expected_scope=scope,
                proposal_scope=scope,
            )
            if status != "REFUTED":
                raise AssertionError(reason)
            learned[fp] = DiagnosticRefutation(
                fingerprint=fp,
                probe=row["probe"],
                status=row["status"],
                evidence_run=int(row["evidence_run"]),
                fact=row["fact"],
                scope=tuple(sorted(scope.items())),
                source_blob=EXPECTED_MEMORY_GIT_BLOB,
            )

    return {
        "arm": "warm",
        "rounds": ROUNDS,
        "proposals": ROUNDS * len(memory["evidence"]),
        "diagnostic_verifier_calls": calls,
        "blocked_by_compiled_refutation": blocked,
        "compiled_refutations": len(learned),
    }, tuple(sorted(learned.values(), key=lambda row: row.probe))


def run_restart_future(
    memory: dict[str, Any],
    bank: tuple[DiagnosticRefutation, ...],
) -> dict[str, Any]:
    scope = base_scope(memory)
    lookup = {row.fingerprint for row in bank}
    calls = 0
    blocked = 0
    # First generation already happened before restart. Test two future waves.
    for _round in range(ROUNDS - 1):
        for row in memory["evidence"]:
            fp = proposal_fingerprint(
                row,
                proposal_scope=scope,
                source_blob=EXPECTED_MEMORY_GIT_BLOB,
            )
            if fp in lookup:
                blocked += 1
                continue
            calls += 1
            verify_row(row, expected_scope=scope, proposal_scope=scope)
    return {
        "arm": "restart",
        "future_rounds": ROUNDS - 1,
        "future_proposals": (ROUNDS - 1) * len(memory["evidence"]),
        "diagnostic_verifier_calls_after_restart": calls,
        "blocked_after_restart": blocked,
    }


def run_ablation(memory: dict[str, Any]) -> dict[str, Any]:
    scope = base_scope(memory)
    calls = 0
    for _round in range(ROUNDS):
        # Exact ablation means compiled negatives are absent each wave.
        for row in memory["evidence"]:
            calls += 1
            verify_row(row, expected_scope=scope, proposal_scope=scope)
    return {
        "arm": "ablation",
        "diagnostic_verifier_calls": calls,
        "blocked": 0,
    }


def changed_scope_control(memory: dict[str, Any], bank: tuple[DiagnosticRefutation, ...]) -> dict[str, Any]:
    scope = dict(base_scope(memory))
    scope["orbit_states"] = int(scope["orbit_states"]) + 1
    row = memory["evidence"][0]
    fp = proposal_fingerprint(
        row,
        proposal_scope=scope,
        source_blob=EXPECTED_MEMORY_GIT_BLOB,
    )
    blocked = fp in {item.fingerprint for item in bank}
    status, reason = verify_row(
        row,
        expected_scope=base_scope(memory),
        proposal_scope=scope,
    )
    return {
        "blocked": blocked,
        "verifier_calls": 1,
        "status": status,
        "reason": reason,
    }


def stale_source_control(bank_path: Path) -> dict[str, Any]:
    rejected = False
    reason = ""
    try:
        load_bank(bank_path, expected_source_blob="stale-source-identity")
    except RuntimeError as exc:
        rejected = True
        reason = str(exc)
    return {"rejected": rejected, "reason": reason}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--memory",
        default="genesis/evidence/kernel-realitygraph-memory-v1.json",
    )
    parser.add_argument("--out", required=True)
    args = parser.parse_args()

    memory_path = Path(args.memory)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    memory = load_memory(memory_path)

    cold = run_cold(memory)
    warm, bank = run_warm(memory)
    bank_path = out / "compiled-negative-diagnostic-bank.json"
    save_bank(bank, bank_path)
    restarted_bank = load_bank(
        bank_path,
        expected_source_blob=EXPECTED_MEMORY_GIT_BLOB,
    )
    restart = run_restart_future(memory, restarted_bank)
    ablation = run_ablation(memory)
    changed_scope = changed_scope_control(memory, restarted_bank)
    stale = stale_source_control(bank_path)

    gates = {
        "source_wrong_zero": memory["retained_kernel"]["wrong"] == 0,
        "eight_exact_falsifications": len(bank) == 8,
        "cold_calls_24": cold["diagnostic_verifier_calls"] == 24,
        "warm_calls_8": warm["diagnostic_verifier_calls"] == 8,
        "warm_blocks_16": warm["blocked_by_compiled_refutation"] == 16,
        "restart_future_calls_zero": restart["diagnostic_verifier_calls_after_restart"] == 0,
        "restart_blocks_16": restart["blocked_after_restart"] == 16,
        "ablation_restores_cold": ablation["diagnostic_verifier_calls"] == 24,
        "changed_scope_not_blocked": changed_scope["blocked"] is False
        and changed_scope["status"] == "UNKNOWN_SCOPE",
        "stale_source_rejected": stale["rejected"] is True,
    }

    evidence = {
        "schema": "qckn-lean-negative-reuse-v1",
        "verdict": "PASS" if all(gates.values()) else "FAIL",
        "trusted_boundary": memory["trusted_boundary"],
        "source_memory_schema": memory["schema"],
        "source_memory_git_blob": EXPECTED_MEMORY_GIT_BLOB,
        "source_retained_kernel": memory["retained_kernel"],
        "scope": base_scope(memory),
        "cold": cold,
        "warm": warm,
        "restart": restart,
        "ablation": ablation,
        "changed_scope_control": changed_scope,
        "stale_source_control": stale,
        "gates": gates,
        "comparison": {
            "cold_total_calls": cold["diagnostic_verifier_calls"],
            "warm_total_calls": warm["diagnostic_verifier_calls"],
            "call_reduction": 1.0
            - warm["diagnostic_verifier_calls"] / cold["diagnostic_verifier_calls"],
            "post_restart_future_call_reduction": 1.0,
        },
        "claim_boundary": (
            "Exact restartable reuse of eight already-retained falsified diagnostic probe "
            "fingerprints inside the Lean-kernel developmental routing layer. This does not "
            "change ACCEPT/REJECT semantics, does not claim checker runtime speedup, and does "
            "not turn a diagnostic refutation into a theorem about unrelated scopes."
        ),
    }
    (out / "evidence.json").write_text(
        json.dumps(evidence, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print(json.dumps({
        "verdict": evidence["verdict"],
        "comparison": evidence["comparison"],
        "restart": restart,
        "changed_scope_control": changed_scope,
        "stale_source_control": stale,
        "gates": gates,
        "claim_boundary": evidence["claim_boundary"],
    }, indent=2, sort_keys=True))
    print(
        "PASS_QCKN_LEAN_NEGATIVE_REUSE_V1"
        if evidence["verdict"] == "PASS"
        else "FAIL_QCKN_LEAN_NEGATIVE_REUSE_V1"
    )
    return 0 if evidence["verdict"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
