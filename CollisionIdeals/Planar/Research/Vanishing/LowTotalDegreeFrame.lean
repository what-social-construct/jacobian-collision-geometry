import CollisionIdeals.Planar.Research.KellerFrameExtension
import CollisionIdeals.General.Galois.ConjugatePolynomialPresentation
import CollisionIdeals.General.Normalization.BaseTransversality
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Affine generator values of low-total-degree planar Keller frames

If both coordinate polynomials have total degree at most two, the
inverse-Jacobian frame sends each source coordinate to an affine-linear
polynomial. The already constructed normal-closure frames satisfy the
same bound in the actual finite conjugate-coordinate presentation.

The hypothesis concerns total polynomial degree, not generic map degree.
It is not asserted for arbitrary planar Keller maps.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals

noncomputable section

open MvPolynomial

private theorem scalar_partial_totalDegree_le_one
    (P : PlanePolynomial) (hP : P.totalDegree ≤ 2) (a : ℂ) (j : Fin 2) :
    (C a * pderiv j P).totalDegree ≤ 1 := by
  have hPartial : (pderiv j P).totalDegree ≤ 1 := by
    by_cases hzero : pderiv j P = 0
    · simp [hzero]
    · have h := totalDegree_pderiv_lt j P hzero
      omega
  apply (totalDegree_mul (C a) (pderiv j P)).trans
  simpa only [totalDegree_C, zero_add] using hPartial

/-- Low total degree, independently of a Jacobian hypothesis, bounds
the polynomial coefficients of the first inverse-Jacobian frame. -/
theorem planarKellerFirstFrame_X_totalDegree_le_one
    (F : PlanarPolynomialMap) (c : ℂ)
    (hDegree : ∀ j : Fin 2, (F j).totalDegree ≤ 2) (j : Fin 2) :
    (planarKellerFirstFrame F c (X j)).totalDegree ≤ 1 := by
  fin_cases j
  · simpa [planarKellerFirstFrame, Derivation.smul_apply, Algebra.smul_def] using
      scalar_partial_totalDegree_le_one (F 1) (hDegree 1) c⁻¹ 1
  · simpa [planarKellerFirstFrame, Derivation.smul_apply, Algebra.smul_def] using
      scalar_partial_totalDegree_le_one (F 1) (hDegree 1) c⁻¹ 0

theorem planarKellerSecondFrame_X_totalDegree_le_one
    (F : PlanarPolynomialMap) (c : ℂ)
    (hDegree : ∀ j : Fin 2, (F j).totalDegree ≤ 2) (j : Fin 2) :
    (planarKellerSecondFrame F c (X j)).totalDegree ≤ 1 := by
  fin_cases j
  · simpa [planarKellerSecondFrame, Derivation.smul_apply, Algebra.smul_def] using
      scalar_partial_totalDegree_le_one (F 0) (hDegree 0) c⁻¹ 1
  · simpa [planarKellerSecondFrame, Derivation.smul_apply, Algebra.smul_def] using
      scalar_partial_totalDegree_le_one (F 0) (hDegree 0) c⁻¹ 0

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance lowDegreeFrameBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

/-- Each actual conjugate generator has an affine representative for its
normal-closure frame derivative. The representative is the renamed source
frame polynomial on the same sheet. -/
theorem exists_affine_conjugateFrame_generator
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c)
    (hDegree : ∀ j : Fin 2, (F j).totalDegree ≤ 2)
    (i : Fin 2) (gj : D.galoisGroup × Fin 2) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    ∃ p : MvPolynomial (D.galoisGroup × Fin 2) ℂ,
      p.totalDegree ≤ 1 ∧
      (Fin.cases (planarKellerFirstFrameNormal D c)
        (fun _ => planarKellerSecondFrameNormal D c) i : Derivation ℂ N N)
          (polynomialConjugateSourceMap D gj.1 (X gj.2)) =
        polynomialConjugateCoordinateEval D p := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  fin_cases i
  · refine ⟨rename (fun j : Fin 2 => (gj.1, j))
      (planarKellerFirstFrame F c (X gj.2)), ?_, ?_⟩
    · exact (totalDegree_rename_le _ _).trans
        (planarKellerFirstFrame_X_totalDegree_le_one F c hDegree gj.2)
    · rw [polynomialConjugateCoordinateEval_rename]
      exact planarKellerFirstFrameNormal_conjugate_polynomial D c hc hJ gj.1 (X gj.2)
  · refine ⟨rename (fun j : Fin 2 => (gj.1, j))
      (planarKellerSecondFrame F c (X gj.2)), ?_, ?_⟩
    · exact (totalDegree_rename_le _ _).trans
        (planarKellerSecondFrame_X_totalDegree_le_one F c hDegree gj.2)
    · rw [polynomialConjugateCoordinateEval_rename]
      exact planarKellerSecondFrameNormal_conjugate_polynomial D c hc hJ gj.1 (X gj.2)

end

end CollisionIdeals
