import CollisionIdeals.Planar.Research.InvariantFrame
import CollisionIdeals.General.Normalization.DerivationQuotient

/-!
# The actual Keller-frame action modulo the target base

The existing normal-closure frames preserve the actual invariant algebra
and restrict to the target partials on its original base image. They
therefore descend to the same standard module quotient used in the target
section comparison. The resulting operators satisfy the coordinate
Leibniz rules; no operators are taken as additional hypotheses.

This supplies neither a preserved finite stage nor a uniform annihilator.
The quotient is not redefined and is not identified here with filtered-Ext
local cohomology or with the collision-ring obstruction.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace CollisionIdeals

noncomputable section

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance quotientActionBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance quotientActionConjugateAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

@[reducible] local instance quotientActionInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

/-- Descend the actual indexed Keller frame to the existing module quotient
of the invariant algebra by the original target-base image. -/
def planarKellerInvariantQuotientOperator
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c) (i : Fin 2) :
    (polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D))) →+
    polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)) := by
  letI := D.finiteIntermediate
  exact algebraQuotientDerivationOperator (polynomialImageCoordinatePartial F i)
    (planarKellerInvariantFrame D c hc hJ i)
    (planarKellerInvariantFrame_algebraMap D c hc hJ i)

@[simp]
theorem planarKellerInvariantQuotientOperator_mk
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c) (i : Fin 2)
    (z : polynomialConjugateInvariantAlgebra D) :
    planarKellerInvariantQuotientOperator D c hc hJ i (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (planarKellerInvariantFrame D c hc hJ i z) := rfl

/-- The constructed quotient operator has the target-coordinate Leibniz
rule for the original base action. -/
theorem planarKellerInvariantQuotientOperator_leibniz
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c) (i : Fin 2)
    (b : PolynomialImageAlgebra F)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D))) :
    letI := D.finiteIntermediate
    planarKellerInvariantQuotientOperator D c hc hJ i (b • q) =
      polynomialImageCoordinatePartial F i b • q +
        b • planarKellerInvariantQuotientOperator D c hc hJ i q := by
  letI := D.finiteIntermediate
  exact algebraQuotientDerivationOperator_leibniz (polynomialImageCoordinatePartial F i)
    (planarKellerInvariantFrame D c hc hJ i)
    (planarKellerInvariantFrame_algebraMap D c hc hJ i)
    (planarKellerInvariantFrame_leibniz D c hc hJ i) b q

/-- A planar Keller map supplies both quotient Leibniz operators internally.
No frame-preservation or operator-existence premise is supplied. -/
theorem planarKellerInvariantQuotient_exists_leibniz
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F) :
    letI := D.finiteIntermediate
    let M := polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D))
    ∃ nabla : Fin 2 → M →+ M, ∀ (i : Fin 2) (b : PolynomialImageAlgebra F) (q : M),
      nabla i (b • q) = polynomialImageCoordinatePartial F i b • q + b • nabla i q := by
  letI := D.finiteIntermediate
  obtain ⟨c, hc, hJ⟩ := hKeller
  exact ⟨fun i => planarKellerInvariantQuotientOperator D c hc hJ i,
    fun i b q => planarKellerInvariantQuotientOperator_leibniz D c hc hJ i b q⟩

end

end CollisionIdeals
