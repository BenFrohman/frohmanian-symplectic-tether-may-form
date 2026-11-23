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

## Failure classes (what a red Truth Gate means)

A red Truth Gate is not automatically a math failure. Since 2026-11-17, `scripts/verify-lock.sh`
runs every phase even after one fails. `scripts/truth_gate_classify.py` then sorts each failure
into exactly one class and prints a `TRUTH GATE VERDICT` block at the end of the log. The block
also goes to the job summary and to `truth-gate-report/classification.json`.

This exists because of frohmanian-tether-sdiff PR #13 (run 44039231121). That PR changed only CI,
but its merge ref was built on a main whose lock still had the old `paper_claim` form. The gate
printed `TRUTH GATE FAIL: this lock is NOT certifying` and `TRUTH GATE STATIC FAIL`, which read like
a proof failure, though every kernel check was green.

| Class | Raised by | What the verdict prints | What fixes it |
|---|---|---|---|
| **KERNEL/PROOF** | `lake build` fails; `sorry`/`admit`/`native_decide`/`axiom` outside the draft dirs; nonstandard axioms; a missing or ill-typed locked declaration; `intended_correspondence` fails to check | `KERNEL/PROOF FAILURE (a proof does not check)` and `This is a proof failure`, with the failing lines | Fix the proof. **This is the only class ever described as a proof failure.** |
| **LOCK-FORM** | `paper_claim` reuses a repository Prop or definition; a vacuous alias of `formal_claim`; an `rfl` correspondence; a partial lock; a lock marked `"certifying": false`; an edited lock region; missing `PAPER_*` fields | `LOCK-FORM: lock wording/form problem, not a math failure`, each offending identifier with `file:line` in the Semantics file and the `file:line` of its repository declaration, then the independent transcription that is required | Rewrite the paper side from the paper's own definition, in the paper's symbols, and prove `intended_correspondence` with real reasoning. A new lock needs the author's sign-off. |
| **PAPER-HASH** | the paper's sha256 differs from the lock | `PAPER-HASH: the paper changed after the lock (not a math failure)`, the commit whose bytes match the lock, every changed line, whether only copyright/license/attribution lines changed, and whether the locked quote is still verbatim | If the edit is intended, update `paper_sha256` in `TRUTH_GATE.lock`, the `PAPER_SHA256:` line in the Semantics file and the hash in this file, all in one commit. If the quote changed, that is a statement change and needs sign-off. |
| **STALE-BASE** | a PR's merge ref was built on an older main, and main has since changed the lock, a Semantics file, a paper or a gate script | `STALE-BASE: branch is behind main's lock; update branch (not a math failure)` | The workflow re-merges the PR head onto the current main and judges that merge, which is what would actually land. It goes red only if that merge conflicts, and then it says to update the branch. |

Two more labels can appear in the verdict:

* **`[INHERITED]`** appears when the PR touches no lock, vocabulary, Semantics or paper file but a
  LOCK-FORM or PAPER-HASH failure remains. The failure comes from main, so it has to be fixed on
  main.
* **`UNCLASSIFIED`** appears when a checker crashed or printed a message no rule recognises. It is
  shown verbatim and is never presumed to be a math failure.

The last line always states the classes, for example
`VERDICT: FAIL (LOCK-FORM). Kernel checks passed: no math was found false.`

### Lock-form lint (runs on every PR, no Lean needed)

The `lock-form-lint` job in `.github/workflows/truth-gate.yml` runs
`python3 scripts/truth_gate_classify.py lint --fetch-deps`. It collects every declaration in
`lean_roots` and in the author's own Lake dependencies (every non-Mathlib package in
`lake-manifest.json`), then reads `paper_claim` and any paper-side helper defined in the Semantics
file. It rejects:

1. any Prop that is a whole hypothesis or the conclusion of `formal_claim` (for example the old
   sdiff form `(∀ ν > 0, PeriodicTetherClosingBound ν) → …`). This is never allowed, with or without
   a vocabulary entry;
2. any other repository name that is not listed, with a reason, in `TRUTH_GATE.vocabulary.json`
   (basic notions such as the velocity-field type);
3. any name in `paper_forbidden_names`, and any mention of `formal_claim`.

`TRUTH_GATE.vocabulary.json` is lint configuration. It cannot change the locked claim, because the
lock region hash still pins `paper_claim`. For an existing author-approved lock, it records only the
basic names that the approved claim already uses. Any new name on the paper side goes into the
new-lock PR together with the author's sign-off.

### Tests

`scripts/tests/test_truth_gate_classify.py` has one throw-away fixture repository per class:

* KERNEL/PROOF: build error, sorry, nonstandard axioms;
* LOCK-FORM: named hypothesis Prop, unlisted repository name, alias, non-certifying,
  partial lock, vacuous lock;
* PAPER-HASH: copyright-only change, and a change to the quote;
* STALE-BASE: re-merge onto the current main, and a merge conflict;
* `[INHERITED]` label.

The `lock-form-lint` job runs them on every PR:

```
python3 -m unittest discover -s scripts/tests -p 'test_truth_gate_classify.py' -v
```

## The locked claim of this repository

* Paper: `paper/companion.tex`
* sha256: `c41c4bf8e7092056915bccceea2a26d1ecd148eeee57f1e557b0f4be731c4419`
* Section: Section "Result 1: geometric uniqueness" (sec:geom), standing assumptions, Definition def:routeA and Theorem thm:routeA, all three sentences
* Main theorem(s): `Frohman.Tether.routeA_determines_kappa_of_matching`, `Frohman.Tether.routeA_admissible_iff`
* Lock file: `TRUTH_GATE.lock`; semantics: `TetherMayForm/Semantics.lean`

Verbatim quote:

```
Throughout, $H$ is a real inner-product space with $\dim H\ge 3$, $u\in H$, $u\neq0$, and
$\Pi_u x = x-\frac{\ip{u}{x}}{\|u\|^2}u$.

Let $\omega\perp u$ with $\|\omega\|=1$, and let $S,w\in\mathbb R$. A bilinear form $B$ on $H$ is a
\emph{correction admissible for Route~A} if all of the following hold:
$B(F,G)=B(G,F)$ for all $F,G$;
(C1) $B(gF,gG)=B(F,G)$ for all $F,G$ and every linear isometry $g$ of $H$ onto $H$ with $gu=u$;
(C2) $B(F,u)=0$ for all $F$;
(C3-A) $B(F,F)\le0$ for all $F$, $B(\omega,\omega)+Sw=0$, and $\tfrac12\bigl(B(F,G)-B(G,F)\bigr)=0$ for all $F,G\perp u$.

Let $\omega\perp u$, $\|\omega\|=1$, $w\neq0$. Suppose $\T[\kappa,w,u]$ matches the stretching
coefficient $S$ in the sense $\T[\kappa,w,u](\omega,\omega)+S w=0$. Then $\kappa=S$.
Consequently, in $\dim\ge3$ with $S\ge0$, $w>0$, and $\omega$ as above, a bilinear form $B$ is a
correction admissible for Route~A (Definition~\ref{def:routeA}) iff $B=\T[\kappa,w,u]$ with $\kappa=S$.
```

```lean
def formal_claim : Prop :=
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], 3 ≤ Module.rank ℝ H →
    ∀ {S w κ : ℝ}, w ≠ 0 → ∀ {u ω : H}, u ≠ 0 →
      ⟪u, ω⟫ = 0 → ‖ω‖ = 1 → 𝔗_F[κ, w, u] ω ω + S * w = 0 → κ = S) ∧
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], 3 ≤ Module.rank ℝ H →
    ∀ {S w : ℝ}, 0 ≤ S → 0 < w → ∀ {u ω : H}, u ≠ 0 → ⟪u, ω⟫ = 0 → ‖ω‖ = 1 →
      ∀ B : LinearMap.BilinForm ℝ H,
        IsAdmissibleCorrection u (RouteAFeedback S w u ω) B ↔ ∃ κ, κ = S ∧ B = 𝔗_F[κ, w, u])

def paper_claim : Prop :=
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], 3 ≤ Module.rank ℝ H →
    ∀ (u : H), u ≠ 0 → ∀ (κ w S : ℝ) (ω : H),
      ⟪ω, u⟫ = 0 → ‖ω‖ = 1 → w ≠ 0 →
      (let Pu : H → H := fun x => x - (⟪u, x⟫ / ‖u‖ ^ 2) • u;
        -(κ * w) * ⟪Pu ω, Pu ω⟫ + S * w = 0) →
      κ = S) ∧
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], 3 ≤ Module.rank ℝ H →
    ∀ (u : H), u ≠ 0 → ∀ (S w : ℝ) (ω : H),
      ⟪ω, u⟫ = 0 → ‖ω‖ = 1 → 0 ≤ S → 0 < w →
      ∀ B : LinearMap.BilinForm ℝ H,
        ((∀ F G, B F G = B G F) ∧
          (∀ g : H ≃ₗᵢ[ℝ] H, g u = u → ∀ F G, B (g F) (g G) = B F G) ∧
          (∀ F, B F u = 0) ∧
          ((∀ F, B F F ≤ 0) ∧ B ω ω + S * w = 0 ∧
            ∀ F G, ⟪F, u⟫ = 0 → ⟪G, u⟫ = 0 → (B F G - B G F) / 2 = 0)) ↔
        ∃ κ : ℝ, κ = S ∧
          let Pu : H → H := fun x => x - (⟪u, x⟫ / ‖u‖ ^ 2) • u;
          ∀ F G, B F G = -(κ * w) * ⟪Pu F, Pu G⟫)
```

See the doc comment of `TetherMayForm/Semantics.lean` for the fixed reading of the paper's terms and the scope.

## Status (2026-11-23): still NOT certifying

`TRUTH_GATE.lock` keeps `"certifying": false`, so the gate stays red on purpose.

Fixed on 2026-11-23: the 2026-11-16 re-audit's named gap. The third sentence of Theorem thm:routeA was
not locked and used the undefined phrase "admissible for Route A". The paper now defines it
(Definition def:routeA, exactly the Lean `IsAdmissibleCorrection u (RouteAFeedback S w u ω)`), and the
new theorem `routeA_admissible_iff` proves the equivalence in any dimension (the given unit `ω ⊥ u`
replaces the finite-dimensional choice of `e₀`). The lock now covers all of thm:routeA.

On the re-audit's second point: no reason is given in this repository why the matching premise
`T(ω,ω) + S w = 0` is realized for Navier–Stokes. `S` is supplied, not derived. The lock certifies an
exact statement about the abstract model and no step toward Navier–Stokes regularity.

Still open (why the gate is red): no theorem stated in a paper may sit outside a lock, and 15 stated
results of `paper/companion.tex` are not yet locked: Lemma (Basic properties), thm:unique, thm:jacobi,
Theorem (Metriplectic split), prop:ce, prop:shear, thm:fieldjacobi, Theorem (Curl of forced NS),
Theorem (Biot–Savart on trigonometric polynomials), Corollary (Velocity form ⇒ vorticity form), the
`L^2` tether-term Lemma, thm:L2, Lemma (Tether is sign-definite at `H^1`), thm:H1, Theorem (Global
smoothness of the tethered system, conditional).

The history of the 2026-11-16 re-audit is in git (`git log -p TRUTH_GATE.md`).
