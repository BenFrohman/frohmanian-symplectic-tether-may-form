/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import TetherMayForm.Main

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/companion.tex
PAPER_SHA256: 8e09c73f68a0779dd97cb479f322276352910a64ceff5e8def6c0a0529a77edd
PAPER_SECTION: Section "Result 1: geometric uniqueness" (sec:geom), standing assumptions and Theorem thm:routeA ("Route A determines κ"), first two sentences

Standing assumptions of the section, quoted verbatim:

PAPER_QUOTE_BEGIN
Throughout, $H$ is a real inner-product space with $\dim H\ge 3$, $u\in H$, $u\neq0$, and
$\Pi_u x = x-\frac{\ip{u}{x}}{\|u\|^2}u$.
PAPER_QUOTE_END

Locked claim, quoted verbatim:

PAPER_QUOTE_BEGIN
Let $\omega\perp u$, $\|\omega\|=1$, $w\neq0$. Suppose $\T[\kappa,w,u]$ matches the stretching
coefficient $S$ in the sense $\T[\kappa,w,u](\omega,\omega)+S w=0$. Then $\kappa=S$.
PAPER_QUOTE_END

Reading of the paper's terms (fixed here, once):
* `H` is a real inner-product space with `dim H ≥ 3` (`3 ≤ Module.rank ℝ H`), `u ∈ H`, `u ≠ 0`;
* `Π_u x = x - (⟪u, x⟫ / ‖u‖²) u` and `T[κ, w, u](F, G) = -(κ w) ⟪Π_u F, Π_u G⟫` are written out with
  the paper's formulas (definition in the same section), not with the library's `piU` and
  `frohmanianTether`;
* `ω ⊥ u` is `⟪ω, u⟫ = 0`.
The theorem's last sentence ("Consequently, in dim ≥ 3 ... iff ...") is a separate claim and is
not locked here.

`formal_claim` is the statement of `Frohman.Tether.routeA_determines_kappa_of_matching`, which
assumes exactly these hypotheses. (The older `routeA_determines_kappa` assumes the stronger
`RouteAFeedback`, which includes nonpositivity, i.e. `κ w ≥ 0`, and reduced Jacobi; it does not
certify the paper's sentence for `κ w < 0`.)

Scope: an algebraic identity fixing the coefficient once matching is assumed. `S` is supplied, not
derived; the Frohmanian Tether Hypothesis stays open; no regularity or Millennium claim is made.
-/

namespace TruthGate

open Frohman.Tether
open scoped InnerProductSpace RealInnerProductSpace

-- TRUTH-GATE LOCK BEGIN
/-- The repository's main statement (`routeA_determines_kappa_of_matching`). -/
def formal_claim : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], 3 ≤ Module.rank ℝ H →
    ∀ {S w κ : ℝ}, w ≠ 0 → ∀ {u ω : H}, u ≠ 0 →
      ⟪u, ω⟫ = 0 → ‖ω‖ = 1 → 𝔗_F[κ, w, u] ω ω + S * w = 0 → κ = S

/-- The paper's Theorem thm:routeA (first two sentences), with `Π_u` and `T` by the paper's formulas. -/
def paper_claim : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], 3 ≤ Module.rank ℝ H →
    ∀ (u : H), u ≠ 0 → ∀ (κ w S : ℝ) (ω : H),
      ⟪ω, u⟫ = 0 → ‖ω‖ = 1 → w ≠ 0 →
      (let Pu : H → H := fun x => x - (⟪u, x⟫ / ‖u‖ ^ 2) • u;
        -(κ * w) * ⟪Pu ω, Pu ω⟫ + S * w = 0) →
      κ = S

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h H _ _ hdim u hu κ w S ω hperp hunit hw hm
    refine h H hdim hw hu (by rw [real_inner_comm]; exact hperp) hunit ?_
    simp only [frohmanianTether_apply, piU_apply]
    exact hm
  · intro h H _ _ hdim S w κ hw u ω hu hperp hunit hm
    refine h H hdim u hu κ w S ω (by rw [real_inner_comm]; exact hperp) hunit hw ?_
    simp only [frohmanianTether_apply, piU_apply] at hm
    exact hm
-- TRUTH-GATE LOCK END

/-- The main theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim := by
  intro H _ _ hdim S w κ hw u ω hu hperp hunit hm
  exact routeA_determines_kappa_of_matching hdim hw hu hperp hunit hm

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
