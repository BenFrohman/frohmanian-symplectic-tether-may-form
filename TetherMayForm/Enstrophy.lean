/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Attempt at `NSTetherEnstrophyInequality` (LOCAL)

Vorticity equation (3D NS): `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω` (+ the 𝔗_F feedback term in the
modified model). At a spatial maximizer `x*` of `|ω|`, with `y = |ω(x*)|`:
  `y y' = ω·Sω + ν ω·Δω + 𝔗_F[κ,w,u](ω,ω)`,
where `ω·Sω` is the stretching term (`S` = strain), `ν ω·Δω ≤ 0` at a maximum, and the
advection term drops (`∇|ω|² = 0` there).
* Stretching: a Calderón–Zygmund-type bound `|ω·Sω| ≤ C y³` (named Prop below; the true
  L∞ CZ estimate has a log loss, so this is itself an assumption).
* Tether: in the MODIFIED model the contribution is `𝔗_F[κ,w,u](ω,ω) = −(κw)⟪Π_uω,Π_uω⟫`
  (`frohmanianTether_orth_self`: `= −κ w ‖ω‖²` for `ω ⟂ u`), κ = S by Route A. Here `w` is the
  SCALAR weight of 𝔗_F (not the vorticity ω). The `y⁴` needs the quartic weight `w = y²`
  (`QuarticWeight`); this is an explicit hypothesis, NOT derived from the uniqueness
  theorem (C1–C3 fix the shape and κ, never `w`). With constant `w` one only gets `−κ w y²`.
* Young absorption with ε = κ/4 of the cross term `2ab` (a = y²) costs `κ/2`, plus `C_abs`.
Result: `y' ≤ C y² − (κ/2 − C_abs) y³`.

In unmodified NS (no 𝔗_F term) there is no cubic damping term; `nsOnly_not_sufficient` shows
the pointwise NS data are consistent with `y' = C y²`, which violates the target.
-/
import TetherMayForm.TetheredLyapunov

namespace Frohman.Tether

/-- Young with ε = κ/4: `2ab ≤ (κ/2) a² + (2/κ) b²`. -/
theorem young_kappa_quarter {κ a b : ℝ} (hκ : 0 < κ) :
    2 * a * b ≤ κ / 2 * a ^ 2 + 2 / κ * b ^ 2 := by
  have h : 0 ≤ (κ * a - 2 * b) ^ 2 / (2 * κ) := by positivity
  have e : (κ * a - 2 * b) ^ 2 / (2 * κ) = κ / 2 * a ^ 2 + 2 / κ * b ^ 2 - 2 * a * b := by
    field_simp; ring
  linarith

/-- Pointwise data at a maximizer of `|ω|` for the energy identity `y y' = St + V + tetherTerm + E`. -/
structure MaxPointData where
  y : ℝ
  y' : ℝ
  St : ℝ   -- stretching ω·Sω
  V : ℝ    -- viscous ν ω·Δω
  tetherTerm : ℝ   -- tether contribution 𝔗_F[κ,w,u](ω,ω) (0 in true NS)
  b : ℝ    -- cross-term amplitude, E = 2 y² b

/-- Named Prop: Calderón–Zygmund-type stretching bound at the maximizer, `ω·Sω ≤ C y³`.
Literature: `S = sym ∇u` is a CZ singular integral of `ω` (Biot–Savart), bounded on `Lᵖ`,
1<p<∞ (Calderón–Zygmund, Acta Math. 88 (1952)), but NOT on `L∞`: the true bound has a log
loss, `‖S‖∞ ≤ C(1 + ‖ω‖_BMO log(e + ‖ω‖_{Hˢ}))` (Kozono–Taniuchi, Comm. Math. Phys. 214 (2000)
191–200, BMO version of BKM). So this pure `y³` bound is STRONGER than what is known. -/
def StretchingCZ (d : MaxPointData) (C : ℝ) : Prop := d.St ≤ C * d.y ^ 3
/-- Named Prop: `ν ω·Δω ≤ 0` at a spatial maximum of `|ω|` (classical maximum principle:
at a max of `|ω|²`, `Δ|ω|² ≤ 0` and `ω·Δω = ½Δ|ω|² − |∇ω|² ≤ 0`). True for C² fields at an
interior max; not formalized (needs second-derivative test on `𝕋³`). -/
def ViscousAtMax (d : MaxPointData) : Prop := d.V ≤ 0
/-- Named Prop: the cross term is controlled, `(2/κ) b² ≤ C_abs y⁴` (model-specific; no
literature source — this is a structural assumption of the May Layer 2 argument). -/
def CrossControlled (d : MaxPointData) (κ Cabs : ℝ) : Prop := 2 / κ * d.b ^ 2 ≤ Cabs * d.y ^ 4
/-- Named Prop: identity at the maximizer, `y y' = ω·Sω + νω·Δω + 𝔗_F term + cross`. For a
C¹ field this is `½ d/dt|ω|²` along the max (advection vanishes since `∇|ω|²=0`); making
`y = sup|ω|` differentiable requires a Danskin/Hamilton-type envelope argument (one-sided
derivative), not formalized. -/
def EnergyIdentity (d : MaxPointData) : Prop :=
  d.y * d.y' = d.St + d.V + d.tetherTerm + 2 * d.y ^ 2 * d.b
/-- Consequence form used below: the 𝔗_F contribution equals `−κ y⁴`. It is DERIVED from
`TetherFeedbackOf` + `QuarticWeight` in `tetherFeedback_of_frohmanianTether`. -/
def TetherFeedback (d : MaxPointData) (κ : ℝ) : Prop := d.tetherTerm = -κ * d.y ^ 4

section Derived
open scoped InnerProductSpace RealInnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `𝔗_F[κ,w,u](ω,ω) = −κ w ‖ω‖²` for `ω ⟂ u`. -/
theorem frohmanianTether_orth_self (κ w : ℝ) {u ω : H} (h : ⟪u, ω⟫ = 0) :
    𝔗_F[κ, w, u] ω ω = -κ * w * ‖ω‖ ^ 2 := by
  rw [frohmanianTether_apply, piU_eq_self_of_inner_eq_zero h, real_inner_self_eq_norm_sq]
  ring

/-- MODIFIED model: the tether contribution at the maximizer IS `𝔗_F[κ,w,u](ω,ω)`, with
`ω ⟂ u` the vorticity at the maximizer and `‖ω‖ = y`. -/
def TetherFeedbackOf (d : MaxPointData) (κ w : ℝ) (u ω : H) : Prop :=
  d.tetherTerm = 𝔗_F[κ, w, u] ω ω ∧ ⟪u, ω⟫ = 0 ∧ ‖ω‖ = d.y

/-- Explicit hypothesis: the quartic Lyapunov weight `w = y²` (scalar weight of 𝔗_F). -/
def QuarticWeight (d : MaxPointData) (w : ℝ) : Prop := w = d.y ^ 2

/-- With the quartic weight, the 𝔗_F contribution is `−κ y⁴`. -/
theorem tetherFeedback_of_frohmanianTether {d : MaxPointData} {κ w : ℝ} {u ω : H}
    (hT : TetherFeedbackOf d κ w u ω) (hw : QuarticWeight d w) : TetherFeedback d κ := by
  obtain ⟨h1, h2, h3⟩ := hT
  unfold TetherFeedback QuarticWeight at *
  rw [h1, frohmanianTether_orth_self κ w h2, h3, hw]; ring

/-- Without the quartic weight (any constant `w`): only `−κ w y²`. -/
theorem tetherTerm_of_frohmanianTether {d : MaxPointData} {κ w : ℝ} {u ω : H}
    (hT : TetherFeedbackOf d κ w u ω) : d.tetherTerm = -κ * w * d.y ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := hT
  rw [h1, frohmanianTether_orth_self κ w h2, h3]

end Derived

/-- **Pointwise derivation (tether-modified system).** -/
theorem tether_pointwise_inequality {d : MaxPointData} {C κ Cabs : ℝ} (hκ : 0 < κ)
    (hy : 0 < d.y) (hE : EnergyIdentity d) (hS : StretchingCZ d C) (hV : ViscousAtMax d)
    (hT : TetherFeedback d κ) (hX : CrossControlled d κ Cabs) :
    d.y' ≤ C * d.y ^ 2 - (κ / 2 - Cabs) * d.y ^ 3 := by
  unfold EnergyIdentity StretchingCZ ViscousAtMax TetherFeedback CrossControlled at *
  have hY := young_kappa_quarter (κ := κ) (a := d.y ^ 2) (b := d.b) hκ
  have key : d.y * d.y' ≤ d.y * (C * d.y ^ 2 - (κ / 2 - Cabs) * d.y ^ 3) := by
    have : 2 * d.y ^ 2 * d.b ≤ κ / 2 * (d.y ^ 2) ^ 2 + Cabs * d.y ^ 4 := by nlinarith
    nlinarith
  exact le_of_mul_le_mul_left key hy

/-- Same, phrased with `kappaDD`, κ = S. -/
theorem tether_pointwise_kappaDD {d : MaxPointData} {C S Cabs : ℝ} (hS0 : 0 < S)
    (hy : 0 < d.y) (hE : EnergyIdentity d) (hS : StretchingCZ d C) (hV : ViscousAtMax d)
    (hT : TetherFeedback d S) (hX : CrossControlled d S Cabs) :
    d.y' ≤ C * d.y ^ 2 - (S / 2 - Cabs) * d.y ^ 3 :=
  tether_pointwise_inequality hS0 hy hE hS hV hT hX

/-- **True NS gap.** With `tetherTerm = 0` (no 𝔗_F term) all NS pointwise hypotheses hold for data with
`y' = C y²`, which violates `y' ≤ C y² − κ'' y³` whenever κ'' > 0. So the cubic damping is
NOT derivable from these NS inputs; it comes only from the added tether term. -/
theorem nsOnly_not_sufficient {C κ κ'' Cabs : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) (hCabs : 0 ≤ Cabs)
    (hκ'' : 0 < κ'') :
    ∃ d : MaxPointData, d.tetherTerm = 0 ∧ 0 < d.y ∧ EnergyIdentity d ∧ StretchingCZ d C ∧
      ViscousAtMax d ∧ CrossControlled d κ Cabs ∧ ¬ d.y' ≤ C * d.y ^ 2 - κ'' * d.y ^ 3 := by
  refine ⟨⟨1, C, C, 0, 0, 0⟩, rfl, one_pos, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [EnergyIdentity, StretchingCZ, ViscousAtMax, CrossControlled] <;> linarith

/-- **Pointwise derivation from 𝔗_F (tether-modified system)**, κ = S (Route A), quartic
weight `w = y²` explicit. -/
theorem tether_pointwise_frohmanianTether {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {d : MaxPointData} {C S Cabs w : ℝ} {u ω : H} (hS0 : 0 < S)
    (hy : 0 < d.y) (hE : EnergyIdentity d) (hS : StretchingCZ d C) (hV : ViscousAtMax d)
    (hT : TetherFeedbackOf d S w u ω) (hw : QuarticWeight d w) (hX : CrossControlled d S Cabs) :
    d.y' ≤ C * d.y ^ 2 - (S / 2 - Cabs) * d.y ^ 3 :=
  tether_pointwise_inequality hS0 hy hE hS hV (tetherFeedback_of_frohmanianTether hT hw) hX

end Frohman.Tether
