import CollisionIdeals.Planar.Basic

/-!
# The planar Keller frame

For a planar map with constant nonzero Jacobian `c`, the inverse Jacobian
matrix defines two polynomial derivations dual to the target coordinates.
This file constructs the frame on the polynomial source ring and proves the
four duality identities. The extension to fraction fields and the marked
normal closure is constructed in `Planar.Research.KellerFrameExtension`;
the prospective secant--trace landing argument uses that extended frame.
-/

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

noncomputable section

/-- The polynomial derivation dual to the first coordinate of a planar map. -/
def planarKellerFirstFrame
    (F : PlanarPolynomialMap) (c : ℂ) :
    Derivation ℂ PlanePolynomial PlanePolynomial :=
  (C c⁻¹ * pderiv 1 (F 1)) • pderiv 0 -
    (C c⁻¹ * pderiv 0 (F 1)) • pderiv 1

/-- The polynomial derivation dual to the second coordinate of a planar map. -/
def planarKellerSecondFrame
    (F : PlanarPolynomialMap) (c : ℂ) :
    Derivation ℂ PlanePolynomial PlanePolynomial :=
  (-(C c⁻¹ * pderiv 1 (F 0))) • pderiv 0 +
    (C c⁻¹ * pderiv 0 (F 0)) • pderiv 1

theorem planarKellerFirstFrame_apply_first
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c) :
    planarKellerFirstFrame F c (F 0) = 1 := by
  simp only [planarKellerFirstFrame, Derivation.sub_apply, Derivation.smul_apply,
    Algebra.smul_def, map_mul]
  change C c⁻¹ * pderiv 1 (F 1) * pderiv 0 (F 0) -
      C c⁻¹ * pderiv 0 (F 1) * pderiv 1 (F 0) = 1
  calc
    _ = C c⁻¹ * planarJacobianDet F := by
      rw [planarJacobianDet, jacobianDet_fin_two]
      ring
    _ = 1 := by
      rw [hJ]
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]

theorem planarKellerFirstFrame_apply_second
    (F : PlanarPolynomialMap) (c : ℂ) :
    planarKellerFirstFrame F c (F 1) = 0 := by
  simp only [planarKellerFirstFrame, Derivation.sub_apply, Derivation.smul_apply,
    Algebra.smul_def, map_mul]
  change C c⁻¹ * pderiv 1 (F 1) * pderiv 0 (F 1) -
      C c⁻¹ * pderiv 0 (F 1) * pderiv 1 (F 1) = 0
  ring

theorem planarKellerSecondFrame_apply_first
    (F : PlanarPolynomialMap) (c : ℂ) :
    planarKellerSecondFrame F c (F 0) = 0 := by
  simp only [planarKellerSecondFrame, Derivation.add_apply, Derivation.smul_apply,
    Algebra.smul_def, map_mul, map_neg]
  change -(C c⁻¹ * pderiv 1 (F 0)) * pderiv 0 (F 0) +
      C c⁻¹ * pderiv 0 (F 0) * pderiv 1 (F 0) = 0
  ring

theorem planarKellerSecondFrame_apply_second
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c) :
    planarKellerSecondFrame F c (F 1) = 1 := by
  simp only [planarKellerSecondFrame, Derivation.add_apply, Derivation.smul_apply,
    Algebra.smul_def, map_mul, map_neg]
  change -(C c⁻¹ * pderiv 1 (F 0)) * pderiv 0 (F 1) +
      C c⁻¹ * pderiv 0 (F 0) * pderiv 1 (F 1) = 1
  rw [show -(C c⁻¹ * pderiv 1 (F 0)) * pderiv 0 (F 1) +
      C c⁻¹ * pderiv 0 (F 0) * pderiv 1 (F 1) =
      C c⁻¹ * planarJacobianDet F by
        rw [planarJacobianDet, jacobianDet_fin_two]
        ring]
  rw [hJ]
  rw [← map_mul, inv_mul_cancel₀ hc, map_one]

end

end CollisionIdeals
