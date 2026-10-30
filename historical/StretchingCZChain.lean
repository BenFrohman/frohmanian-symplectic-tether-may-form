/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.

Not built (outside the `TetherMayForm` library). These theorems assume `StretchingCZ`
(`ω·Sω ≤ C y³` at the maximizer), which is false as an `L∞` estimate (Calderón–Zygmund fails at
`p = ∞`). They were removed from the build. The log-loss replacement is in
`TetherMayForm/LogLoss.lean`.
-/
import TetherMayForm.Final

namespace Frohman.Tether

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

/-- **Pointwise derivation from 𝔗_F (tether-modified system)**, κ = S (Route A), quartic
weight `w = y²` explicit. -/
theorem tether_pointwise_frohmanianTether {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {d : MaxPointData} {C S Cabs w : ℝ} {u ω : H} (hS0 : 0 < S)
    (hy : 0 < d.y) (hE : EnergyIdentity d) (hS : StretchingCZ d C) (hV : ViscousAtMax d)
    (hT : TetherFeedbackOf d S w u ω) (hw : QuarticWeight d w) (hX : CrossControlled d S Cabs) :
    d.y' ≤ C * d.y ^ 2 - (S / 2 - Cabs) * d.y ^ 3 :=
  tether_pointwise_inequality hS0 hy hE hS hV (tetherFeedback_of_frohmanianTether hT hw) hX

section Quartic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pointwise tethered inequality with no `QuarticWeight` hypothesis. -/
theorem tether_pointwise_quartic {d : MaxPointData} {C S Cabs : ℝ} {u ω : H} (hS0 : 0 < S)
    (hy : 0 < d.y) (hE : EnergyIdentity d) (hS : StretchingCZ d C) (hV : ViscousAtMax d)
    (hT : TetherFeedbackQuartic d S u ω) (hX : CrossControlled d S Cabs) :
    d.y' ≤ C * d.y ^ 2 - (S / 2 - Cabs) * d.y ^ 3 :=
  tether_pointwise_inequality hS0 hy hE hS hV (tetherFeedback_of_quartic hT) hX

end Quartic

end Frohman.Tether
