/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Metriplectic (Morrison) reading of the field-level tethered bracket

The test splits the bracket `{·,·} = br + T` into two parts, as Morrison does:
1. antisymmetric (classical) part `br`: Jacobi holds (`FieldJacobi.jacF_eq_zero`);
2. symmetric part `T = tetF`: we check symmetry (`tetF_symm`), degeneracy in the energy
   direction `dH = u` (`tetF_energy_left/right`, because `Π_u u = 0`), and the sign of its quadratic form
   `dissF a = −(κw)⟨Π_u a,Π_u a⟩` at the two shear tests.
The mixed Jacobi failures in `FieldJacobi` are *not* required to vanish in the
metriplectic framework. There, Jacobi is asked only of the antisymmetric part.
Statements concern the tethered bracket on trigonometric polynomials only, not plain NS.
-/
import TetherMayForm.FieldJacobi

namespace Frohman.Tether.FieldMetriplectic
open Frohman.Tether.FieldJacobi
open scoped Matrix

noncomputable section

theorem pr_comm (a b : Fld) : pr a b = pr b a := by
  induction a using Finsupp.induction_linear with
  | zero => simp [pr_zero_left, pr_zero_right]
  | add a a' ha ha' => rw [pr_add_left, pr_add_right, ha, ha']
  | single p v =>
    induction b using Finsupp.induction_linear with
    | zero => simp [pr_zero_left, pr_zero_right]
    | add b b' hb hb' => rw [pr_add_left, pr_add_right, hb, hb']
    | single q z =>
      rw [pr_single, pr_single, Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : q = -p
      · subst h; simp [dotProduct_comm]
      · have h' : ¬ p = -q := fun e => h (by rw [e, neg_neg])
        simp [h, h']

/-- Symmetry of the tether part. -/
theorem tetF_symm (κ w : ℂ) (u a b : Fld) : tetF κ w u a b = tetF κ w u b a := by
  simp only [tetF, pr_comm (piF u a)]

theorem piF_self {u : Fld} (hu : pr u u ≠ 0) : piF u u = 0 := by
  simpa using piF_smul_self hu 1

/-- Degeneracy: `T(dH,·) = 0` for `H = ½⟨u,u⟩`, `dH = u`. -/
theorem tetF_energy_left {u : Fld} (hu : pr u u ≠ 0) (κ w : ℂ) (b : Fld) :
    tetF κ w u u b = 0 := by simp [tetF, piF_self hu, pr_zero_left]

theorem tetF_energy_right {u : Fld} (hu : pr u u ≠ 0) (κ w : ℂ) (a : Fld) :
    tetF κ w u a u = 0 := by rw [tetF_symm]; exact tetF_energy_left hu κ w a

/-- Quadratic form of the symmetric part. -/
def dissF (κ w : ℂ) (u a : Fld) : ℂ := -(κ * w) * pr (piF u a) (piF u a)

theorem pr_uY_uY : pr uY uY = 1 / 2 := by
  simp [uY, pr_add_left, pr_add_right, pr_single, dotProduct,
    Fin.sum_univ_three, ky, funext_iff, Fin.forall_fin_succ]; ring_nf; simp; norm_num

theorem pr_uX_uX : pr uX uX = 1 / 2 := by
  simp [uX, pr_add_left, pr_add_right, pr_single, dotProduct,
    Fin.sum_univ_three, kx, funext_iff, Fin.forall_fin_succ]; ring_nf; simp; norm_num

theorem dissF_energy_uY (κ w : ℂ) : dissF κ w uY uY = 0 := by
  simp [dissF, piF_self (by rw [pr_uY_uY]; norm_num : pr uY uY ≠ 0), pr_zero_left]

theorem dissF_energy_uX (κ w : ℂ) : dissF κ w uX uX = 0 := by
  simp [dissF, piF_self (by rw [pr_uX_uX]; norm_num : pr uX uX ≠ 0), pr_zero_left]

/-- Shear `(sin y,0,0)`, test direction `(0,0,sin x)`: value `−κw/2`. -/
theorem dissF_shearY (κ w : ℂ) : dissF κ w uY aZ = -(κ * w) / 2 := by
  rw [dissF, piF_of_pr_zero pr_uY_aZ, pr_aZ_aZ]; ring

/-- Shear `(sin x,0,0)`, test direction `(1,0,0)`: value `−κw`. -/
theorem dissF_shearX (κ w : ℂ) : dissF κ w uX eX = -(κ * w) := by
  rw [dissF, piF_of_pr_zero pr_uX_eX, pr_eX_eX]; ring

/-- Sign (dissipative) condition at both shears, for real `κw ≥ 0`. -/
theorem dissF_shear_nonpos {κ w : ℝ} (h : 0 ≤ κ * w) :
    (dissF κ w uY aZ).re ≤ 0 ∧ (dissF κ w uY aZ).im = 0 ∧
    (dissF κ w uX eX).re ≤ 0 ∧ (dissF κ w uX eX).im = 0 := by
  rw [dissF_shearY, dissF_shearX]
  have e : ((κ : ℂ) * w) = ((κ * w : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith

end
end Frohman.Tether.FieldMetriplectic
