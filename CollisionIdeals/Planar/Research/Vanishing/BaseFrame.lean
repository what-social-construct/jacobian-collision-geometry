import CollisionIdeals.Planar.Research.KellerFrameExtension

/-!
# The Keller frame on target polynomials

The inverse-Jacobian frame differentiates every polynomial in the target
coordinates by the corresponding target partial derivative. The same
identities hold for its actual extensions to the marked normal closure,
on every conjugate polynomial sheet.

These identities concern the source and field extensions. They do not assert preservation
of a normalization local ring at a boundary prime.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/-- The first Keller frame differentiates an arbitrary target polynomial
by its first target partial derivative. -/
theorem planarKellerFirstFrame_coordinateAlgHom
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c) (p : PlanePolynomial) :
    planarKellerFirstFrame F c (coordinateAlgHom F p) =
      coordinateAlgHom F (MvPolynomial.pderiv 0 p) := by
  simpa only [coordinateAlgHom_X, planarKellerFirstFrame_apply_first F c hc hJ,
    planarKellerFirstFrame_apply_second, mul_one, mul_zero, add_zero] using
    planarDerivation_chainRule (planarKellerFirstFrame F c) (coordinateAlgHom F) p

/-- The second Keller frame differentiates an arbitrary target polynomial
by its second target partial derivative. -/
theorem planarKellerSecondFrame_coordinateAlgHom
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c) (p : PlanePolynomial) :
    planarKellerSecondFrame F c (coordinateAlgHom F p) =
      coordinateAlgHom F (MvPolynomial.pderiv 1 p) := by
  simpa only [coordinateAlgHom_X, planarKellerSecondFrame_apply_first,
    planarKellerSecondFrame_apply_second F c hc hJ, mul_zero, mul_one, zero_add] using
    planarDerivation_chainRule (planarKellerSecondFrame F c) (coordinateAlgHom F) p

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
  [Algebra (PolynomialMapBaseFunctionField F) N]

/-- On every conjugate sheet, the extended first Keller frame has the
same target-polynomial derivative. -/
theorem planarKellerFirstFrameNormal_conjugate_coordinateAlgHom
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c)
    (g : D.galoisGroup) (p : PlanePolynomial) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarKellerFirstFrameNormal D c
        (polynomialConjugateSourceMap D g (coordinateAlgHom F p)) =
      polynomialConjugateSourceMap D g
        (coordinateAlgHom F (MvPolynomial.pderiv 0 p)) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  rw [planarKellerFirstFrameNormal_conjugate_polynomial D c hc hJ,
    planarKellerFirstFrame_coordinateAlgHom F c hc hJ]

/-- On every conjugate sheet, the extended second Keller frame has the
same target-polynomial derivative. -/
theorem planarKellerSecondFrameNormal_conjugate_coordinateAlgHom
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c)
    (g : D.galoisGroup) (p : PlanePolynomial) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarKellerSecondFrameNormal D c
        (polynomialConjugateSourceMap D g (coordinateAlgHom F p)) =
      polynomialConjugateSourceMap D g
        (coordinateAlgHom F (MvPolynomial.pderiv 1 p)) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  rw [planarKellerSecondFrameNormal_conjugate_polynomial D c hc hJ,
    planarKellerSecondFrame_coordinateAlgHom F c hc hJ]

end

end CollisionIdeals
