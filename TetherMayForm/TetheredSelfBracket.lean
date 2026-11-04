/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman.

# The tethered self-bracket `{F,F}_tethered = 𝔗_F(F,F)`, nonzero in general

If the classical part `P` is alternating (`P F F = 0`, as for the Lie–Poisson bracket),
then `{F,F}_tethered = P F F + 𝔗_F(F,F) = 𝔗_F(F,F) = -κ w ‖Π_u F‖²`.
Explicit witness on `ℝ³`: `u = e₁`, `F = e₂` gives `{F,F}_tethered = -κ w`, nonzero
whenever `κ w ≠ 0`. So the tethered sum is not alternating, hence not a Poisson bracket.
-/
import TetherMayForm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Frohman.Tether.SelfBracket

open Frohman.Tether
open scoped InnerProductSpace RealInnerProductSpace

section general
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem tetheredBracket_self (P : LinearMap.BilinForm ℝ H) (hP : ∀ F, P F F = 0)
    (κ w : ℝ) (u F : H) :
    tetheredBracket P κ w u F F = frohmanianTether κ w u F F := by
  simp [tetheredBracket, hP F]

theorem tetheredBracket_self_eq (P : LinearMap.BilinForm ℝ H) (hP : ∀ F, P F F = 0)
    (κ w : ℝ) (u F : H) :
    tetheredBracket P κ w u F F = -(κ * w) * ‖piU u F‖ ^ 2 := by
  rw [tetheredBracket_self P hP, frohmanianTether_apply, real_inner_self_eq_norm_sq]

end general

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Witness: `u = e₁`, `F = e₂` gives `{F,F}_tethered = -κ w`. -/
theorem witness (P : LinearMap.BilinForm ℝ E3) (hP : ∀ F, P F F = 0) (κ w : ℝ) :
    tetheredBracket P κ w (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 1 1) = -(κ * w) := by
  have he : ⟪(EuclideanSpace.single 0 1 : E3), EuclideanSpace.single 1 1⟫ = 0 := by
    simp [PiLp.inner_apply, Fin.sum_univ_three]
  rw [tetheredBracket_self_eq P hP, piU_eq_self_of_inner_eq_zero he]
  simp

theorem witness_ne_zero (P : LinearMap.BilinForm ℝ E3) (hP : ∀ F, P F F = 0) {κ w : ℝ}
    (h : κ * w ≠ 0) :
    tetheredBracket P κ w (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 1 1) ≠ 0 := by
  rw [witness P hP]; exact neg_ne_zero.mpr h

/-- Hence the tethered sum is not alternating (not a Poisson bracket) when `κ w ≠ 0`. -/
theorem tetheredBracket_not_alternating (P : LinearMap.BilinForm ℝ E3) (hP : ∀ F, P F F = 0)
    {κ w : ℝ} (h : κ * w ≠ 0) :
    ¬ ∀ F, tetheredBracket P κ w (EuclideanSpace.single 0 1) F F = 0 :=
  fun hall => witness_ne_zero P hP h (hall _)

end Frohman.Tether.SelfBracket

#print axioms Frohman.Tether.SelfBracket.tetheredBracket_not_alternating
#print axioms Frohman.Tether.SelfBracket.tetheredBracket_self_eq
