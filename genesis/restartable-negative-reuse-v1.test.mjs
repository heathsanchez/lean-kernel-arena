import fs from "node:fs";
import test from "node:test";
import assert from "node:assert/strict";

import {
  bankText,
  compileNegativeBank,
  qualify,
  restartBank,
  runPortfolio,
} from "./restartable-negative-reuse-v1.mjs";

const memory = JSON.parse(
  fs.readFileSync(
    new URL("./evidence/kernel-realitygraph-memory-v1.json", import.meta.url),
    "utf8",
  ),
);

test("compiled negative bank is canonical and restartable", () => {
  const bank = compileNegativeBank(memory);
  const text = bankText(bank);
  const restarted = restartBank(text);
  assert.equal(bankText(restarted), text);
  assert.equal(restarted.negatives.length, 8);
  assert.equal(restarted.retained_kernel_snapshot.wrong, 0);
});

test("exact guard skips eight repeated falsified routes", () => {
  const bank = compileNegativeBank(memory);
  const cold = runPortfolio(memory, null);
  const warm = runPortfolio(memory, bank);
  assert.equal(cold.verifier_calls, 11);
  assert.equal(warm.verifier_calls, 3);
  assert.equal(warm.skipped_count, 8);
});

test("changed residual signature receives no skip", () => {
  const bank = compileNegativeBank(memory);
  const changed = structuredClone(memory);
  changed.current_signature.frontier = "changed";
  const result = runPortfolio(changed, bank);
  assert.equal(result.bank_active, false);
  assert.equal(result.verifier_calls, 11);
  assert.equal(result.skipped_count, 0);
});

test("qualification includes sham and ablation controls", () => {
  const result = qualify(memory);
  assert.equal(result.passed, true);
  assert.equal(result.sham.verifier_calls, result.cold.verifier_calls);
  assert.equal(result.ablation.verifier_calls, result.cold.verifier_calls);
  assert.equal(result.restart.verifier_calls, result.warm.verifier_calls);
  assert.ok(result.verifier_call_reduction_fraction > 0.7);
});
