import "./stack-safe.mjs";
import "./structural-cache.mjs";
import "./structural-sharing.mjs";
import "./normal-cache.mjs";
import "./rigid-type-spine.mjs";

// Experimental composition order: the exact closed closure converter is the
// retained conversion fallback. Later speculative converters may try cheaper
// bounded paths first, but on rollback they reach this layer with the run's
// ordinary global budget rather than invoking it inside their temporary cap.
import "./closed-closure-conversion-layer.mjs";

import "./lazy-delta.mjs";
import "./early-proof-irrelevance.mjs";
import "./consequence-cache.mjs";
import "./declaration-instantiation-cache.mjs";
import "./localdef-continuation.mjs";
import "./localdef-getapp-cache.mjs";
import "./rigid-constructor-reject.mjs";
import "./scoped-beta-spine.mjs";
import "./recursor-gated-conversion.mjs";
export * from "./kernel-semantic.mjs";
