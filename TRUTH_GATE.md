# TRUTH GATE — the GOD gate. Read this first.

Author: Benjamin Stanley Frohman. This file is the root instruction for every person and every
automated agent (every bot) that touches this repository. Load it before any other file.

**Only truth and honest, kernel-proved theorems pass this gate. Nothing from this repository is
published, released, deposited on Zenodo, cited or claimed unless the `truth-gate` check is green
on the exact commit being cited.** That is why it is the GOD gate: it sits above every other
check, and no other green check can stand in for it.

## The issue this gate fixes

A paper states its claim in English. Lean can only prove `formal_claim ↔ paper_claim` once
`paper_claim` is itself written in Lean. If `paper_claim` were simply *defined to be*
`formal_claim` (or an alias of it, or something that unfolds to it), the theorem
`intended_correspondence` would be `Iff.rfl`: it would be empty and prove nothing about the
paper. A green certificate could then "certify" a statement different from the one the paper
makes (drift), whether by accident or by an injected instruction.

## The fix rule (binding, permanent)

1. `paper_claim` is an **independent Lean transcription of the paper's exact claim**, written in
   the paper's own terms, with every hypothesis the paper states. The verbatim English quote,
   the paper path, its sha256 and the section are recorded in the doc comment of
   `Semantics.lean` **and** in this file (below).
2. `paper_claim` must **not** be defined as, reference, or trivially alias `formal_claim`.
3. `intended_correspondence : formal_claim ↔ paper_claim` must have a **substantive proof**. It
   may not be `Iff.rfl`, `rfl`, `exact Iff.rfl` or similar, and it may not use the main theorem
   (it is a statement-level equivalence, not "both sides happen to be provable").
4. `formal_claim` is exactly the statement of the repository's main theorem, and
   `paper_claim_holds` is the main theorem transported across the correspondence.
5. Only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, `admit`, `native_decide` or
   new `axiom` anywhere outside the draft directories in `TRUTH_GATE.lock`.
6. If the paper's English claim cannot be faithfully transcribed, or is not what Lean proves,
   the gate stays **red** and the mismatch is reported. Never patch over it: never weaken
   `paper_claim`, drop a hypothesis, or redefine it to match the formal side. If the
   formalization drifted, rewrite the formalization so it transports across the lock again.
7. Open problems stay hypotheses. No Millennium Prize problem is claimed solved; the gate only
   ensures the certificate proves precisely the locked claim and nothing else.
8. The locked region of `Semantics.lean`, the quote and `TRUTH_GATE.lock` change only with the
   author's explicit sign-off, as a PR that says "new lock" in its title.
9. Commits are authored by Benjamin Stanley Frohman only, with no AI co-author trailers. No
   force-push and no history rewriting.

## What `scripts/verify-lock.sh` checks mechanically

* `lake build` succeeds, with no `sorry` warning outside the draft directories;
* no `sorry` / `admit` / `native_decide` / `axiom` token outside the draft directories
  (comments and strings excluded);
* `Semantics.lean` has `PAPER_PATH`, `PAPER_SHA256`, `PAPER_SECTION` and a verbatim
  `PAPER_QUOTE`; the hash matches the paper file and the quote occurs in it; this file carries
  the same path, hash and quote;
* the lock region hash matches `TRUTH_GATE.lock`;
* `paper_claim`'s body does not mention `formal_claim`; the correspondence is not proved by
  `Iff.rfl`/`rfl`;
* in Lean: the bodies of `formal_claim` and `paper_claim` differ, the two are not
  definitionally equal, the correspondence proof does not reach the main theorem, the main
  theorem's statement is `formal_claim`, `paper_claim_holds` goes through the correspondence,
  and `#print axioms` shows only the three standard axioms.

What it cannot check: whether the transcription is the right reading of the English. That
reading is fixed once, in writing, below and in `Semantics.lean`, and is the author's sign-off.

## Running the gate locally

```
lake exe cache get
bash scripts/verify-lock.sh
```

Reports are written to `truth-gate-report/`.

## The locked claim of this repository

* Paper: `paper/companion.tex`
* sha256: `8e09c73f68a0779dd97cb479f322276352910a64ceff5e8def6c0a0529a77edd`
* Section: Section "Result 1: geometric uniqueness" (sec:geom), standing assumptions and Theorem thm:routeA ("Route A determines κ"), first two sentences
* Main theorem(s): `Frohman.Tether.routeA_determines_kappa_of_matching`
* Lock file: `TRUTH_GATE.lock`; semantics: `TetherMayForm/Semantics.lean`

Verbatim quote:

```
Throughout, $H$ is a real inner-product space with $\dim H\ge 3$, $u\in H$, $u\neq0$, and
$\Pi_u x = x-\frac{\ip{u}{x}}{\|u\|^2}u$.

Let $\omega\perp u$, $\|\omega\|=1$, $w\neq0$. Suppose $\T[\kappa,w,u]$ matches the stretching
coefficient $S$ in the sense $\T[\kappa,w,u](\omega,\omega)+S w=0$. Then $\kappa=S$.
```

```lean
def formal_claim : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], 3 ≤ Module.rank ℝ H →
    ∀ {S w κ : ℝ}, w ≠ 0 → ∀ {u ω : H}, u ≠ 0 →
      ⟪u, ω⟫ = 0 → ‖ω‖ = 1 → 𝔗_F[κ, w, u] ω ω + S * w = 0 → κ = S

def paper_claim : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], 3 ≤ Module.rank ℝ H →
    ∀ (u : H), u ≠ 0 → ∀ (κ w S : ℝ) (ω : H),
      ⟪ω, u⟫ = 0 → ‖ω‖ = 1 → w ≠ 0 →
      (let Pu : H → H := fun x => x - (⟪u, x⟫ / ‖u‖ ^ 2) • u;
        -(κ * w) * ⟪Pu ω, Pu ω⟫ + S * w = 0) →
      κ = S
```

See the doc comment of `TetherMayForm/Semantics.lean` for the fixed reading of the paper's terms and the scope.

## Re-audit (2026-11-16): this lock is NOT certifying

Status: **REOPENED. The gate is red on purpose.** `TRUTH_GATE.lock` carries `"certifying": false`, and
`scripts/truth_gate_check.py` fails while it does. Nothing was deleted: `Semantics.lean`, the quotes,
the hashes and the history are unchanged.

Rule applied (Benjamin Stanley Frohman, 2026-11-16):
* There are no partial locks. A lock certifies only a step on the correct path to the full theorem
  that is kernel-proved as the actual true answer, so that the next step can build on it.
* Drifted, dummy, placeholder or stand-in types, names or categories are rejected.
* Cross-ontology connections are not rejected for looking unrelated. The kernel check, and whether
  the piece genuinely helps reach the full structured proof, decide.
* `paper_claim` is an independent transcription of the verbatim paper quote, never an alias of
  `formal_claim`, and the correspondence is never `rfl`/`Iff.rfl`.

Locked claim under review: routeA_determines_kappa_of_matching (Theorem thm:routeA, first two sentences only)

Why it is reopened:
* Partial lock. Only the first two sentences of Theorem thm:routeA are locked. Its third sentence ("Consequently, in dim ≥ 3 with S ≥ 0, w > 0, a correction is admissible for Route A iff B = T[κ,w,u] with κ = S.") is not.
* Not a certified step toward the paper's goal. The locked part is the one-line computation Π_u ω = ω ⇒ (S − κ)w = 0. The paper's proof itself says "κ is a free parameter … and S is supplied, not derived". The companion two-part paper (BenFrohman/frohmanian-tether-manuscript-2026-06-01, `two_part/tether_two_part.tex`) shows the tether does not modify the Navier–Stokes vector field. No step toward Navier–Stokes regularity is certified.

What would re-certify it: A lock needs the complete Theorem thm:routeA, including the admissibility characterization. It also needs a stated reason why the matching premise is realized on the path to the paper's main result, if one exists.
