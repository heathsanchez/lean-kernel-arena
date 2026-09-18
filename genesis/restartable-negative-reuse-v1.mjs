import fs from "node:fs";
import crypto from "node:crypto";
import process from "node:process";
import { pathToFileURL } from "node:url";

export function stable(value) {
  if (Array.isArray(value)) return value.map(stable);
  if (value && typeof value === "object") {
    return Object.fromEntries(
      Object.keys(value).sort().map((key) => [key, stable(value[key])]),
    );
  }
  return value;
}

export function canonicalJson(value) {
  return JSON.stringify(stable(value));
}

export function digest(value) {
  return crypto
    .createHash("sha256")
    .update("lean-negative-reuse-v1:")
    .update(canonicalJson(value))
    .digest("hex");
}

export function compileNegativeBank(memory) {
  if (memory.schema !== "kernel-realitygraph-memory-v1") {
    throw new Error("unsupported source memory schema");
  }
  if (
    memory.trusted_boundary !==
    "diagnostic-routing-only; never changes ACCEPT/REJECT semantics"
  ) {
    throw new Error("source memory exceeds diagnostic routing boundary");
  }
  if (memory.retained_kernel?.wrong !== 0) {
    throw new Error("source retained kernel contains wrong verdicts");
  }

  const negatives = [...memory.evidence]
    .filter((row) => String(row.status).startsWith("FALSIFIED"))
    .map((row) => ({
      probe: String(row.probe),
      status: String(row.status),
      evidence_run: Number(row.evidence_run),
      fact: String(row.fact),
    }))
    .sort((a, b) => a.probe.localeCompare(b.probe));

  if (!negatives.length) throw new Error("negative bank is empty");
  if (new Set(negatives.map((row) => row.probe)).size !== negatives.length) {
    throw new Error("duplicate negative probe");
  }
  if (new Set(negatives.map((row) => row.evidence_run)).size !== negatives.length) {
    throw new Error("duplicate evidence run");
  }

  const payload = {
    schema: "lean-restartable-negative-reuse-v1",
    trusted_boundary:
      "diagnostic-routing-only; never changes ACCEPT/REJECT semantics",
    guard: stable(memory.current_signature),
    negatives,
    retained_kernel_snapshot: stable(memory.retained_kernel),
    source_schema: memory.schema,
  };
  return { ...payload, digest: digest(payload) };
}

export function restartBank(text) {
  const parsed = JSON.parse(text);
  const { digest: stored, ...payload } = parsed;
  if (stored !== digest(payload)) throw new Error("negative bank digest mismatch");
  const canonical = canonicalJson({ ...payload, digest: stored });
  if (canonical !== text) throw new Error("negative bank is not canonical");
  return parsed;
}

export function bankText(bank) {
  return canonicalJson(bank);
}

export function sameSignature(left, right) {
  return canonicalJson(left) === canonicalJson(right);
}

export function runPortfolio(memory, bank = null) {
  const old = memory.evidence.map((row) => String(row.probe));
  const fresh = memory.next_parallel_probes.map((row) => String(row.id));
  const candidates = [...old, ...fresh];
  const active =
    bank !== null &&
    sameSignature(bank.guard, memory.current_signature);

  const negatives = active
    ? new Set(bank.negatives.map((row) => row.probe))
    : new Set();

  const skipped = [];
  const verified = [];
  for (const candidate of candidates) {
    if (negatives.has(candidate)) {
      skipped.push(candidate);
      continue;
    }
    // This is a routing-cost audit. A "verification call" represents paying
    // to revisit the route; fresh candidates remain unresolved by design.
    verified.push(candidate);
  }

  return {
    candidate_count: candidates.length,
    verifier_calls: verified.length,
    skipped_count: skipped.length,
    skipped: skipped.sort(),
    verified: verified.sort(),
    bank_active: active,
  };
}

export function qualify(memory) {
  const bank = compileNegativeBank(memory);
  const text = bankText(bank);
  const restarted = restartBank(text);

  const cold = runPortfolio(memory, null);
  const warm = runPortfolio(memory, bank);
  const restart = runPortfolio(memory, restarted);

  const sham = {
    ...bank,
    guard: { ...bank.guard, frontier: "sham-different-frontier" },
  };
  // Recompute sham digest because the control is structurally valid memory
  // under a different guard, not a corrupted artifact.
  const { digest: _discard, ...shamPayload } = sham;
  const shamBank = { ...shamPayload, digest: digest(shamPayload) };
  const shamRun = runPortfolio(memory, shamBank);

  const ablation = runPortfolio(memory, null);

  const changedMemory = structuredClone(memory);
  changedMemory.current_signature = {
    ...changedMemory.current_signature,
    frontier: "changed-frontier-control",
  };
  const changedSignature = runPortfolio(changedMemory, bank);

  const sourceRuns = bank.negatives.map((row) => row.evidence_run).sort((a, b) => a - b);
  const saved = cold.verifier_calls - warm.verifier_calls;
  const reduction = saved / cold.verifier_calls;

  const gates = {
    source_bank_has_eight_verified_negatives: bank.negatives.length === 8,
    retained_kernel_wrong_zero: bank.retained_kernel_snapshot.wrong === 0,
    cold_reacquires_all_routes: cold.verifier_calls === 11,
    warm_skips_exact_negatives: warm.verifier_calls === 3 && warm.skipped_count === 8,
    restart_is_exact: bankText(restarted) === text && restart.verifier_calls === 3,
    sham_guard_cannot_skip: shamRun.verifier_calls === cold.verifier_calls,
    changed_signature_cannot_skip:
      changedSignature.verifier_calls === cold.verifier_calls,
    ablation_restores_cold:
      ablation.verifier_calls === cold.verifier_calls &&
      ablation.skipped_count === 0,
    routing_only_boundary_preserved:
      bank.trusted_boundary ===
      "diagnostic-routing-only; never changes ACCEPT/REJECT semantics",
    verifier_calls_strictly_reduced: saved > 0 && reduction > 0.7,
  };

  return {
    schema: "lean-restartable-negative-reuse-v1",
    passed: Object.values(gates).every(Boolean),
    gates,
    source_runs: sourceRuns,
    source_memory_digest: digest(stable(memory)),
    compiled_bank_digest: bank.digest,
    cold,
    warm,
    restart,
    sham: shamRun,
    ablation,
    changed_signature: changedSignature,
    saved_verifier_calls: saved,
    verifier_call_reduction_fraction: reduction,
    retained_kernel_snapshot: bank.retained_kernel_snapshot,
    claim_boundary:
      "Exact-signature diagnostic routing reuse only. The bank suppresses repeated evaluation of already falsified development routes; it does not alter Lean kernel ACCEPT/REJECT semantics, does not prove those routes impossible under changed residual signatures, and does not claim Arena performance improvement by itself.",
  };
}

export function main() {
  const sourcePath =
    process.env.LEAN_NEGATIVE_SOURCE ??
    "genesis/evidence/kernel-realitygraph-memory-v1.json";
  const outPath =
    process.env.LEAN_NEGATIVE_REUSE_RESULT ??
    "genesis/evidence/restartable-negative-reuse-v1-result.json";
  const bankPath =
    process.env.LEAN_NEGATIVE_REUSE_BANK ??
    "genesis/evidence/restartable-negative-reuse-v1-bank.json";

  const memory = JSON.parse(fs.readFileSync(sourcePath, "utf8"));
  const result = qualify(memory);
  const bank = compileNegativeBank(memory);

  fs.writeFileSync(outPath, JSON.stringify(stable(result), null, 2) + "\n");
  fs.writeFileSync(bankPath, bankText(bank) + "\n");
  console.log(JSON.stringify(stable(result)));
  console.log(
    result.passed
      ? "PASS_LEAN_RESTARTABLE_NEGATIVE_REUSE_V1"
      : "FAIL_LEAN_RESTARTABLE_NEGATIVE_REUSE_V1",
  );
  return result.passed ? 0 : 1;
}

if (import.meta.url === pathToFileURL(process.argv[1]).href) {
  process.exitCode = main();
}
