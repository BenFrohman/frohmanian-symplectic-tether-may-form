/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import TetherMayForm.Metriplectic

/-!
# TetherMayForm.RouteA

Author: Benjamin Frohman (prepared with assistance from Grok; not a co-author).
# C3, Route A form (May 20 2026 slide; May 21 PASS 2 wording)
May 20 "Route A" slide (phone image, no server date): C3 = "Negative Feedback at |ω|
maxima + 5-step + 9-term Jacobi on reduced orbit (D→C→A→B)".
May 21 PASS 2 text (Full_Living_Document…md, Drive, modified 2026-05-24): "When the
evolution of the mollified sup-norm functional M_ε(t) = ‖ω_ε(t)‖_{L∞} is computed at a
spatial maximum point, the correction must contribute a term whose leading-order
contribution is exactly −κ M_ε(t)² with κ > 0 … the classical stretching term
contributes exactly +M_ε(t)² … forces κ = C_CZ(3)."
## Abstract model
* `ω : H` — the normalized vorticity direction at the maximizer of `|ω|²` (unit,
  orthogonal to `u`, i.e. on the reduced orbit).
* `S` — the stretching coefficient there (May: `C_CZ(3)`); `w` — the weight `∫|ω|²`.
* **Feedback at the maximum**: `B(ω,ω) ≤ 0` everywhere, and at `ω` the feedback cancels
  stretching exactly: `B(ω,ω) + S·w = 0`. So `κ` is *defined by matching*, `κ = S`.
* **Jacobi on the reduced orbit**: the correction adds no antisymmetric (Poisson)
  part on `uᗮ`, so the Poisson tensor of the combined bracket on the reduced orbit is the
  classical one, and the classical Jacobi identity is inherited. This is the abstract
  shadow of the "9-term Jacobi" check; the 9-term cyclic expansion itself is not
  formalized. The "5-step" is the uniqueness proof (Basic.lean, steps 1–5).
-/

namespace Frohman.Tether

open Submodule
open scoped InnerProductSpace RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **C3, Route A (May 20).** -/
structure RouteAFeedback (S w : ℝ) (u ω : H) (B : LinearMap.BilinForm ℝ H) : Prop where
  nonpos : ∀ F, B F F ≤ 0
  maximizer_reduced : ⟪u, ω⟫ = 0
  maximizer_unit : ‖ω‖ = 1
  matches_stretching : B ω ω + S * w = 0
  jacobi_reduced : ∀ F G, ⟪u, F⟫ = 0 → ⟪u, G⟫ = 0 → antiPart B F G = 0

/-- Route A C3 implies the earlier one-direction C3, with `κ = S` fixed by matching. -/
theorem RouteAFeedback.toControllable {S w : ℝ} {u ω : H} {B : LinearMap.BilinForm ℝ H}
    (h : RouteAFeedback S w u ω B) : ProducesControllableNegativeFeedback S w u B :=
  ⟨h.nonpos, ω, h.maximizer_reduced, h.maximizer_unit, by linarith [h.matches_stretching]⟩

/-- Jacobi compatibility: on the reduced orbit the Poisson part of `P + B` is `P`. -/
theorem RouteAFeedback.poisson_unchanged {S w : ℝ} {u ω : H} {B : LinearMap.BilinForm ℝ H}
    (h : RouteAFeedback S w u ω B) (P : LinearMap.BilinForm ℝ H) (hP : ∀ F, P F F = 0)
    (F G : H) (hF : ⟪u, F⟫ = 0) (hG : ⟪u, G⟫ = 0) :
    antiPart (P + B) F G = P F G := by
  have hA : P G F = -P F G := by
    have := hP (F + G); simp [hP F, hP G] at this; linarith
  have := h.jacobi_reduced F G hF hG
  rw [antiPart_apply] at this ⊢
  simp only [LinearMap.add_apply, hA]; linarith

/-- The tether satisfies Route A C3 with `κ = S`, at any reduced unit maximizer. -/
theorem frohmanianTether_routeA {S w : ℝ} (hS : 0 ≤ S) (hw : 0 ≤ w) {u ω : H}
    (hω : ⟪u, ω⟫ = 0) (hn : ‖ω‖ = 1) : RouteAFeedback S w u ω 𝔗_F[S, w, u] where
  nonpos := frohmanianTether_self_nonpos hS hw u
  maximizer_reduced := hω
  maximizer_unit := hn
  matches_stretching := by
    rw [frohmanianTether_apply, piU_eq_self_of_inner_eq_zero hω, real_inner_self_eq_norm_sq,
      hn]; ring
  jacobi_reduced := fun F G _ _ => by rw [antiPart_frohmanianTether]; rfl

/-- Within the tether family, Route A C3 forces the coefficient to be `S w`. -/
theorem routeA_fixes_coefficient {S w : ℝ} {u ω : H} (c : ℝ)
    (h : RouteAFeedback S w u ω 𝔗_F[c, 1, u]) : c = S * w :=
  feedback_fixes_coefficient c h.toControllable

/-- **Uniqueness of the Minimal Metric Tether — Route A C3.** In dimension ≥ 3, with a
reduced unit maximizer `ω`, a symmetric correction satisfies C1, C2 and Route A C3 iff it
equals `𝔗_F[S, w, u]`: the coefficient is the stretching coefficient, by matching. -/
theorem uniqueness_routeA_iff [FiniteDimensional ℝ H] (hdim : 3 ≤ Module.finrank ℝ H)
    {S w : ℝ} (hS : 0 ≤ S) (hw : 0 ≤ w) (u ω : H) (hu : u ≠ 0)
    (hω : ⟪u, ω⟫ = 0) (hn : ‖ω‖ = 1) (B : LinearMap.BilinForm ℝ H) :
    IsAdmissibleCorrection u (RouteAFeedback S w u ω) B ↔ B = 𝔗_F[S, w, u] := by
  constructor
  · intro hB
    exact uniqueness_of_minimal_metric_tether hdim S w u hu _
      (fun c hc => routeA_fixes_coefficient c hc) B hB
  · rintro rfl
    exact frohmanianTether_admissible S w u _ (frohmanianTether_routeA hS hw hω hn)

/-- For the tether itself the two C3 versions agree (given a reduced unit maximizer). -/
theorem routeA_iff_controllable_on_tether {S w : ℝ} (hS : 0 ≤ S) (hw : 0 ≤ w) {u ω : H}
    (hω : ⟪u, ω⟫ = 0) (hn : ‖ω‖ = 1) :
    RouteAFeedback S w u ω 𝔗_F[S, w, u] ↔ ProducesControllableNegativeFeedback S w u 𝔗_F[S, w, u] :=
  ⟨RouteAFeedback.toControllable, fun _ => frohmanianTether_routeA hS hw hω hn⟩

/-- **Schur step at a given unit direction (any dimension).** A symmetric correction obeying C1
and C2 equals `𝔗_F[-B(e₀,e₀), 1, u]` as soon as one unit `e₀ ⟂ u` is given. No finite
dimension is used: the only isometries needed are reflections in hyperplanes `(ℝ ∙ v)ᗮ`. -/
theorem admissible_eq_frohmanianTether_of_unit (u e₀ : H) (he₀ : ⟪u, e₀⟫ = 0)
    (hn₀ : ‖e₀‖ = 1) (B : LinearMap.BilinForm ℝ H)
    (hsymm : ∀ F G, B F G = B G F) (hC1 : InvariantUnderCoadjointAction u B)
    (hC2 : DegenerateWRTKineticEnergy u B) :
    B = 𝔗_F[-B e₀ e₀, 1, u] := by
  have hq : ∀ x, B x x = B e₀ e₀ * ⟪piU u x, piU u x⟫ := by
    intro x
    rw [degeneracy_forces_projection u B hsymm hC2 x x]
    set p := piU u x with hp
    by_cases hp0 : p = 0
    · simp [hp0]
    have hnp : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
    set e := ‖p‖⁻¹ • p
    have hpe : p = ‖p‖ • e := by simp [e, smul_smul, mul_inv_cancel₀ hnp]
    have he : ⟪u, e⟫ = 0 := by simp [e, inner_smul_right, hp, inner_u_piU]
    have hne : ‖e‖ = ‖e₀‖ := by
      rw [hn₀]; simp [e, norm_smul, inv_mul_cancel₀ hnp]
    have hB := diag_eq_of_norm_eq u B hC1 he he₀ hne
    rw [hpe]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, real_inner_self_eq_norm_sq, hB]
    rw [← hpe]; ring
  refine LinearMap.ext₂ fun x y => ?_
  rw [frohmanianTether_apply]
  have h1 := hq (x + y)
  have h2 := hq x
  have h3 := hq y
  simp only [map_add, LinearMap.add_apply, inner_add_left, inner_add_right] at h1
  rw [hsymm y x, real_inner_comm (piU u x) (piU u y)] at h1
  linear_combination (h1 - h2 - h3) / 2

/-- **Route A admissibility, third sentence of the companion paper's Theorem `thm:routeA`
(any dimension).** For `S ≥ 0`, `w > 0` and a unit `ω ⟂ u`, a bilinear form `B` is a correction
admissible for Route A (symmetric, C1, C2, Route A C3) iff `B = 𝔗_F[κ, w, u]` with `κ = S`.
Unlike `frohmanian_symplectic_tether_theorem`, no `FiniteDimensional` instance is assumed: the
given unit `ω ⟂ u` plays the role of `e₀`. The standing assumption `3 ≤ Module.rank ℝ H` and
`u ≠ 0` of the paper's section are kept so that the statement is the paper's; the proof does not
need them. -/
theorem routeA_admissible_iff (_hdim : 3 ≤ Module.rank ℝ H) {S w : ℝ} (hS : 0 ≤ S)
    (hw : 0 < w) {u ω : H} (_hu : u ≠ 0) (hω : ⟪u, ω⟫ = 0) (hn : ‖ω‖ = 1)
    (B : LinearMap.BilinForm ℝ H) :
    IsAdmissibleCorrection u (RouteAFeedback S w u ω) B ↔ ∃ κ, κ = S ∧ B = 𝔗_F[κ, w, u] := by
  constructor
  · intro hB
    have hBeq := admissible_eq_frohmanianTether_of_unit u ω hω hn B hB.symm hB.c1 hB.c2
    have hc : -B ω ω = S * w := by
      have h3 := hB.c3
      rw [hBeq] at h3
      exact routeA_fixes_coefficient _ h3
    refine ⟨S, rfl, ?_⟩
    rw [hBeq, hc]
    ext x y
    simp [frohmanianTether_apply]
  · rintro ⟨κ, rfl, rfl⟩
    exact frohmanianTether_admissible κ w u _ (frohmanianTether_routeA hS hw.le hω hn)

end Frohman.Tether
