import CollisionIdeals.Planar.Research.Vanishing.BaseFrame
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Polynomial subtraction in the target coordinates

The existing second Keller-frame identity gives the Jacobian of
`(P, Q^r - ell P^s)`. Only the exponent-one operation is used as a
target-coordinate shear: its explicit triangular inverse preserves the
Jacobian constant and the same coordinate-image subalgebra of the
original polynomial source.

For general `r`, the displayed Jacobian contains `r * Q^(r-1)`.
No general power-subtraction map is asserted to be Keller or to have
the same coordinate-image algebra.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

open MvPolynomial

private theorem jacobianDet_pair_eq_const_mul_secondFrame
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0) (H : PlanePolynomial) :
    jacobianDet (![F 0, H] : PlanarPolynomialMap) =
      C c * planarKellerSecondFrame F c H := by
  have hInv : (C c : PlanePolynomial) * C c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  rw [jacobianDet_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, planarKellerSecondFrame,
    Derivation.add_apply, Derivation.smul_apply, Algebra.smul_def]
  change pderiv 0 (F 0) * pderiv 1 H - pderiv 1 (F 0) * pderiv 0 H =
    C c * (-(C c⁻¹ * pderiv 1 (F 0)) * pderiv 0 H +
      (C c⁻¹ * pderiv 0 (F 0)) * pderiv 1 H)
  calc
    _ = (C c * C c⁻¹) *
        (pderiv 0 (F 0) * pderiv 1 H - pderiv 1 (F 0) * pderiv 0 H) := by
      rw [hInv, one_mul]
    _ = _ := by ring

private theorem jacobianDet_coordinatePolynomial
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c) (p : PlanePolynomial) :
    jacobianDet (![F 0, coordinateAlgHom F p] : PlanarPolynomialMap) =
      C c * coordinateAlgHom F (pderiv 1 p) := by
  rw [jacobianDet_pair_eq_const_mul_secondFrame F c hc,
    planarKellerSecondFrame_coordinateAlgHom F c hc hJ]

/-- A thin corollary of the existing target-polynomial Keller-frame
identity. For `r ≠ 1`, the additional polynomial factor is retained. -/
theorem jacobianDet_power_subtraction
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c) (ell : ℂ) (r s : ℕ) :
    jacobianDet (![F 0, (F 1) ^ r - C ell * (F 0) ^ s] : PlanarPolynomialMap) =
      C (r : ℂ) * (F 1) ^ (r - 1) * C c := by
  let p : PlanePolynomial := X 1 ^ r - C ell * X 0 ^ s
  have hImage : coordinateAlgHom F p = (F 1) ^ r - C ell * (F 0) ^ s := by
    simp [p, coordinateAlgHom]
  have hDerivative : coordinateAlgHom F (pderiv 1 p) =
      C (r : ℂ) * (F 1) ^ (r - 1) := by
    simp [p, coordinateAlgHom]
  have h := jacobianDet_coordinatePolynomial F c hc hJ p
  rw [hImage, hDerivative] at h
  calc
    _ = C c * (C (r : ℂ) * (F 1) ^ (r - 1)) := h
    _ = _ := by ring

/-- General power subtraction is still an element of the original
coordinate-image algebra. This is not equality of image algebras for
the transformed pair, and it needs no Keller hypothesis. -/
theorem powerSubtraction_mem_polynomialImageAlgebra
    (F : PlanarPolynomialMap) (ell : ℂ) (r s : ℕ) :
    (F 1) ^ r - C ell * (F 0) ^ s ∈ polynomialMapImageAlgebra F := by
  change ∃ p : PlanePolynomial,
    coordinateAlgHom F p = (F 1) ^ r - C ell * (F 0) ^ s
  refine ⟨X 1 ^ r - C ell * X 0 ^ s, ?_⟩
  simp [coordinateAlgHom]

/-- The actual triangular map of the target affine plane. Its inverse
uses `-ell` with the same exponent. -/
def targetShear (ell : ℂ) (s : ℕ) : PlanarPolynomialMap :=
  ![X 0, X 1 - C ell * X 0 ^ s]

/-- Exponent-one subtraction on the target pair of the original map. -/
def targetSubtract (F : PlanarPolynomialMap) (ell : ℂ) (s : ℕ) :
    PlanarPolynomialMap :=
  ![F 0, F 1 - C ell * (F 0) ^ s]

/-- The displayed target shear has its explicit polynomial triangular
inverse. No Keller hypothesis is needed for this identity. -/
theorem coordinateAlgHom_targetShear_comp_neg (ell : ℂ) (s : ℕ) :
    (coordinateAlgHom (targetShear ell s)).comp
      (coordinateAlgHom (targetShear (-ell) s)) = AlgHom.id ℂ PlanePolynomial := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [coordinateAlgHom, targetShear]

/-- Target subtraction is exactly composition with the existing
coordinate-ring map of the triangular target shear. -/
theorem coordinateAlgHom_targetSubtract
    (F : PlanarPolynomialMap) (ell : ℂ) (s : ℕ) :
    coordinateAlgHom (targetSubtract F ell s) =
      (coordinateAlgHom F).comp (coordinateAlgHom (targetShear ell s)) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [coordinateAlgHom, targetSubtract, targetShear]

/-- Actual target-coordinate shear preserves the original Jacobian
constant, unlike general power subtraction. -/
theorem targetSubtract_jacobian
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c) (ell : ℂ) (s : ℕ) :
    planarJacobianDet (targetSubtract F ell s) = C c := by
  simpa [planarJacobianDet, targetSubtract] using
    jacobianDet_power_subtraction F c hc hJ ell 1 s

theorem targetSubtract_isKeller
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F) (ell : ℂ) (s : ℕ) :
    IsPlanarKeller (targetSubtract F ell s) := by
  obtain ⟨c, hc, hJ⟩ := hKeller
  exact ⟨c, hc, targetSubtract_jacobian F c hc hJ ell s⟩

/-- Equality of the same coordinate-image subalgebras inside the original
polynomial source, proved with the explicit inverse target shear. -/
theorem coordinateAlgHom_targetSubtract_range
    (F : PlanarPolynomialMap) (ell : ℂ) (s : ℕ) :
    (coordinateAlgHom (targetSubtract F ell s)).range = (coordinateAlgHom F).range := by
  rw [coordinateAlgHom_targetSubtract]
  apply le_antisymm
  · exact AlgHom.range_comp_le_range _ _
  · intro z hz
    obtain ⟨p, hp⟩ := hz
    refine ⟨coordinateAlgHom (targetShear (-ell) s) p, ?_⟩
    change coordinateAlgHom F (coordinateAlgHom (targetShear ell s)
      (coordinateAlgHom (targetShear (-ell) s) p)) = z
    have hInverse := AlgHom.congr_fun (coordinateAlgHom_targetShear_comp_neg ell s) p
    change coordinateAlgHom (targetShear ell s)
      (coordinateAlgHom (targetShear (-ell) s) p) = p at hInverse
    rw [hInverse]
    exact hp

end

end CollisionIdeals.Planar
