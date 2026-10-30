/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Discharging cited propositions

`L4L2Holder` is proved for any probability space. This includes the normalized (unit-volume) torus,
with `E = ½∫|ω|²` and `Q = ∫|ω|⁴`. The proof uses the nonnegativity of variance
(Jensen for `t ↦ t²`) applied to `g = |ω|²`.
-/
import TetherMayForm.EnstrophyL2
import Mathlib.Probability.Moments.Variance

namespace Frohman.Tether.CitedProps
open MeasureTheory ProbabilityTheory

/-- `(∫ g)² ≤ ∫ g²` on a probability space, for `g ∈ L²`. -/
theorem sq_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g : Ω → ℝ} (hg : MemLp g 2 μ) : (∫ s, g s ∂μ) ^ 2 ≤ ∫ s, g s ^ 2 ∂μ := by
  have h := variance_nonneg g μ
  rw [variance_eq_sub hg] at h
  simpa [Pi.pow_apply] using h

/-- **`L4L2Holder` discharged.** On a probability space, with `g x = |ω(x)|²` square-integrable
for each time, `E x = ½∫ g x` and `Q x = ∫ (g x)²`, the cited Hölder inequality holds. -/
theorem l4l2Holder_of_prob {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (g : ℝ → Ω → ℝ) (T : ℝ) (hg : ∀ x, MemLp (g x) 2 μ) :
    EnstrophyL2.L4L2Holder (fun x => (1 / 2) * ∫ s, g x s ∂μ) (fun x => ∫ s, g x s ^ 2 ∂μ) T := by
  intro x _
  have := sq_integral_le (hg x)
  simpa [← mul_assoc] using this

end Frohman.Tether.CitedProps
