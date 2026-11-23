/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import TetherMayForm.Main

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/companion.tex
PAPER_SHA256: fcac43d492be996335eb58bfaf77dfd47aa5ef750257b9fb2095e6a54ac8b9b1
PAPER_SECTION: Section "Result 1: geometric uniqueness" (sec:geom), standing assumptions, Definition def:routeA and Theorem thm:routeA ("Route A determines κ"), all three sentences

Standing assumptions of the section, quoted verbatim:

PAPER_QUOTE_BEGIN
Throughout, $H$ is a real inner-product space with $\dim H\ge 3$, $u\in H$, $u\neq0$, and
$\Pi_u x = x-\frac{\ip{u}{x}}{\|u\|^2}u$.
PAPER_QUOTE_END

Definition def:routeA, quoted verbatim:

PAPER_QUOTE_BEGIN
Let $\omega\perp u$ with $\|\omega\|=1$, and let $S,w\in\mathbb R$. A bilinear form $B$ on $H$ is a
\emph{correction admissible for Route~A} if all of the following hold:
$B(F,G)=B(G,F)$ for all $F,G$;
(C1) $B(gF,gG)=B(F,G)$ for all $F,G$ and every linear isometry $g$ of $H$ onto $H$ with $gu=u$;
(C2) $B(F,u)=0$ for all $F$;
(C3-A) $B(F,F)\le0$ for all $F$, $B(\omega,\omega)+Sw=0$, and $\tfrac12\bigl(B(F,G)-B(G,F)\bigr)=0$ for all $F,G\perp u$.
PAPER_QUOTE_END

Locked claim (Theorem thm:routeA, complete), quoted verbatim:

PAPER_QUOTE_BEGIN
Let $\omega\perp u$, $\|\omega\|=1$, $w\neq0$. Suppose $\T[\kappa,w,u]$ matches the stretching
coefficient $S$ in the sense $\T[\kappa,w,u](\omega,\omega)+S w=0$. Then $\kappa=S$.
Consequently, in $\dim\ge3$ with $S\ge0$, $w>0$, and $\omega$ as above, a bilinear form $B$ is a
correction admissible for Route~A (Definition~\ref{def:routeA}) iff $B=\T[\kappa,w,u]$ with $\kappa=S$.
PAPER_QUOTE_END

Reading of the paper's terms (fixed here, once):
* `H` is a real inner-product space with `dim H ≥ 3` (`3 ≤ Module.rank ℝ H`; no finite dimension),
  `u ∈ H`, `u ≠ 0`;
* `Π_u x = x - (⟪u, x⟫ / ‖u‖²) u` and `T[κ, w, u](F, G) = -(κ w) ⟪Π_u F, Π_u G⟫` are written out with
  the paper's formulas, not with the library's `piU` and `frohmanianTether`;
* `ω ⊥ u` is `⟪ω, u⟫ = 0`; "a bilinear form `B` on `H`" is a Mathlib `LinearMap.BilinForm ℝ H`;
* "linear isometry `g` of `H` onto `H`" is a Mathlib `H ≃ₗᵢ[ℝ] H`;
* "`B = T[κ, w, u]` with `κ = S`" is `∃ κ, κ = S ∧ ∀ F G, B F G = T[κ, w, u](F, G)`.

`formal_claim` is the conjunction of the statements of `Frohman.Tether.routeA_determines_kappa_of_matching`
(first two sentences) and `Frohman.Tether.routeA_admissible_iff` (third sentence, any dimension).

Scope: an exact statement about the abstract inner-product-space model. `S` is supplied, not
derived; the matching premise is a hypothesis, and no reason is given in this repository why it is
realized for Navier–Stokes. The Frohmanian Tether Hypothesis stays open; no regularity or
Millennium claim is made.
-/

namespace TruthGate

open Frohman.Tether
open scoped InnerProductSpace RealInnerProductSpace

-- TRUTH-GATE LOCK BEGIN
/-- The repository's main statements: `routeA_determines_kappa_of_matching` (first two sentences
of `thm:routeA`) and `routeA_admissible_iff` (third sentence). -/
def formal_claim : Prop :=
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], 3 ≤ Module.rank ℝ H →
    ∀ {S w κ : ℝ}, w ≠ 0 → ∀ {u ω : H}, u ≠ 0 →
      ⟪u, ω⟫ = 0 → ‖ω‖ = 1 → 𝔗_F[κ, w, u] ω ω + S * w = 0 → κ = S) ∧
  (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], 3 ≤ Module.rank ℝ H →
    ∀ {S w : ℝ}, 0 ≤ S → 0 < w → ∀ {u ω : H}, u ≠ 0 → ⟪u, ω⟫ = 0 → ‖ω‖ = 1 →
      ∀ B : LinearMap.BilinForm ℝ H,
        IsAdmissibleCorrection u (RouteAFeedback S w u ω) B ↔ ∃ κ, κ = S ∧ B = 𝔗_F[κ, w, u])

/-- The paper's Theorem thm:routeA (all three sentences) with Definition def:routeA, written with
the paper's formulas for `Π_u` and `T` and the paper's conditions (C1), (C2), (C3-A). -/
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

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  have hT : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (κ w : ℝ) (u : H)
      (B : LinearMap.BilinForm ℝ H),
      B = 𝔗_F[κ, w, u] ↔
        ∀ F G, B F G = -(κ * w) * ⟪F - (⟪u, F⟫ / ‖u‖ ^ 2) • u, G - (⟪u, G⟫ / ‖u‖ ^ 2) • u⟫ := by
    intro H _ _ κ w u B
    constructor
    · rintro rfl F G
      rw [frohmanianTether_apply, piU_apply, piU_apply]
    · intro h
      refine LinearMap.ext₂ fun F G => ?_
      rw [h F G, frohmanianTether_apply, piU_apply, piU_apply]
  have hA : ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (S w : ℝ) (u ω : H)
      (B : LinearMap.BilinForm ℝ H), ⟪u, ω⟫ = 0 → ‖ω‖ = 1 →
      (IsAdmissibleCorrection u (RouteAFeedback S w u ω) B ↔
        ((∀ F G, B F G = B G F) ∧
          (∀ g : H ≃ₗᵢ[ℝ] H, g u = u → ∀ F G, B (g F) (g G) = B F G) ∧
          (∀ F, B F u = 0) ∧
          ((∀ F, B F F ≤ 0) ∧ B ω ω + S * w = 0 ∧
            ∀ F G, ⟪F, u⟫ = 0 → ⟪G, u⟫ = 0 → (B F G - B G F) / 2 = 0))) := by
    intro H _ _ S w u ω B hω hn
    constructor
    · intro h
      refine ⟨h.symm, h.c1, h.c2, h.c3.nonpos, h.c3.matches_stretching, ?_⟩
      intro F G hF hG
      have := h.c3.jacobi_reduced F G (by rw [real_inner_comm]; exact hF)
        (by rw [real_inner_comm]; exact hG)
      rwa [antiPart_apply] at this
    · rintro ⟨hs, h1, h2, hnp, hm, hj⟩
      refine ⟨hs, h1, h2, ⟨hnp, hω, hn, hm, ?_⟩⟩
      intro F G hF hG
      rw [antiPart_apply]
      exact hj F G (by rw [real_inner_comm]; exact hF) (by rw [real_inner_comm]; exact hG)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro H _ _ hdim u hu κ w S ω hperp hunit hw hm
      refine h1 H hdim hw hu (by rw [real_inner_comm]; exact hperp) hunit ?_
      simp only [frohmanianTether_apply, piU_apply]
      exact hm
    · intro H _ _ hdim u hu S w ω hperp hunit hS hw B
      have hω : ⟪u, ω⟫ = 0 := by rw [real_inner_comm]; exact hperp
      rw [← hA S w u ω B hω hunit, h2 H hdim hS hw hu hω hunit B]
      exact exists_congr fun κ => and_congr Iff.rfl (hT κ w u B)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro H _ _ hdim S w κ hw u ω hu hperp hunit hm
      refine h1 H hdim u hu κ w S ω (by rw [real_inner_comm]; exact hperp) hunit hw ?_
      simp only [frohmanianTether_apply, piU_apply] at hm
      exact hm
    · intro H _ _ hdim S w hS hw u ω hu hω hunit B
      rw [hA S w u ω B hω hunit, h2 H hdim u hu S w ω (by rw [real_inner_comm]; exact hω) hunit hS hw B]
      exact exists_congr fun κ => and_congr Iff.rfl (hT κ w u B).symm
-- TRUTH-GATE LOCK END

/-- The main theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim :=
  ⟨fun _ _ _ hdim _ _ _ hw _ _ hu hperp hunit hm =>
      routeA_determines_kappa_of_matching hdim hw hu hperp hunit hm,
    fun _ _ _ hdim _ _ hS hw _ _ hu hω hn B => routeA_admissible_iff hdim hS hw hu hω hn B⟩

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
