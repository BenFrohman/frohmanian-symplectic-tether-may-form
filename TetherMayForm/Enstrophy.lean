/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Attempt at `NSTetherEnstrophyInequality` (LOCAL)

Vorticity equation (3D NS): `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω` (+ tether term `Tω` in the
modified model). At a spatial maximizer `x*` of `|ω|`, with `y = |ω(x*)|`:
  `y y' = ω·Sω + ν ω·Δω + ω·Tω`,
where `ω·Sω` is the stretching term (`S` = strain), `ν ω·Δω ≤ 0` at a maximum, and the
advection term drops (`∇|ω|² = 0` there).
* Stretching: a Calderón–Zygmund-type bound `|ω·Sω| ≤ C y³` (named Prop below; the true
  L∞ CZ estimate has a log loss, so this is itself an assumption).
* Tether: in the MODIFIED model the tether contributes `ω·Tω = −κ y⁴`, κ = S by Route A.
* Young absorption with ε = κ/4 of the cross term `2ab` (a = y²) costs `κ/2`, plus `C_abs`.
Result: `y' ≤ C y² − (κ/2 − C_abs) y³`.

In unmodified NS (`T = 0`) there is no cubic damping term; `nsOnly_not_sufficient` shows
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

/-- Pointwise data at a maximizer of `|ω|` for the energy identity `y y' = St + V + Tt + E`. -/
structure MaxPointData where
  y : ℝ
  y' : ℝ
  St : ℝ   -- stretching ω·Sω
  V : ℝ    -- viscous ν ω·Δω
  Tt : ℝ   -- tether ω·Tω (0 in true NS)
  b : ℝ    -- cross-term amplitude, E = 2 y² b

/-- Named Prop: CZ-type stretching bound at the maximizer. -/
def StretchingCZ (d : MaxPointData) (C : ℝ) : Prop := d.St ≤ C * d.y ^ 3
/-- Named Prop: viscous term is nonpositive at a maximum of |ω| (max principle). -/
def ViscousAtMax (d : MaxPointData) : Prop := d.V ≤ 0
/-- Named Prop: the cross term is controlled, `(2/κ) b² ≤ C_abs y⁴`. -/
def CrossControlled (d : MaxPointData) (κ Cabs : ℝ) : Prop := 2 / κ * d.b ^ 2 ≤ Cabs * d.y ^ 4
/-- Energy identity at the maximizer. -/
def EnergyIdentity (d : MaxPointData) : Prop :=
  d.y * d.y' = d.St + d.V + d.Tt + 2 * d.y ^ 2 * d.b
/-- MODIFIED model: the tether 𝔗_F[κ,w,u] adds `−κ y⁴` (κ = S from Route A). -/
def TetherFeedback (d : MaxPointData) (κ : ℝ) : Prop := d.Tt = -κ * d.y ^ 4

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

/-- **True NS gap.** With `Tt = 0` all NS pointwise hypotheses hold for data with
`y' = C y²`, which violates `y' ≤ C y² − κ'' y³` whenever κ'' > 0. So the cubic damping is
NOT derivable from these NS inputs; it comes only from the added tether term. -/
theorem nsOnly_not_sufficient {C κ κ'' Cabs : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) (hCabs : 0 ≤ Cabs)
    (hκ'' : 0 < κ'') :
    ∃ d : MaxPointData, d.Tt = 0 ∧ 0 < d.y ∧ EnergyIdentity d ∧ StretchingCZ d C ∧
      ViscousAtMax d ∧ CrossControlled d κ Cabs ∧ ¬ d.y' ≤ C * d.y ^ 2 - κ'' * d.y ^ 3 := by
  refine ⟨⟨1, C, C, 0, 0, 0⟩, rfl, one_pos, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [EnergyIdentity, StretchingCZ, ViscousAtMax, CrossControlled] <;> linarith

end Frohman.Tether
