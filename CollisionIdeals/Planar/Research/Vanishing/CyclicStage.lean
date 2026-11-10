import CollisionIdeals.Planar.Research.InvariantQuotientAction
import CollisionIdeals.General.Keller.ConjugateInvariantSections
import CollisionIdeals.General.Normalization.DerivationCyclicStage

/-!
# Testing the cyclic finite stage of an actual boundary class

The standard cyclic stage `B q` is finite over the target base. If a class
in the actual invariant-algebra quotient is nonzero, some constructed
target-coordinate operator sends it outside that stage.

This is an escape certificate, not a preservation hypothesis. It does not
assert that a nonzero class exists or establish a Keller-specific bound
on larger stages, and it does not prove planar vanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace CollisionIdeals

noncomputable section

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance cyclicStageBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance cyclicStageBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance cyclicStageBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toSMul

@[reducible] local instance cyclicStageConjugateAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

@[reducible] local instance cyclicStageInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

/-- A nonzero actual target-boundary class cannot have its cyclic finite
stage preserved by both constructed coordinate operators. -/
theorem planarKellerInvariantQuotient_cyclic_escape
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)))
    (hq : q ≠ 0) :
    ∃ i : Fin 2, planarKellerInvariantQuotientOperator D c hc hJ i q ∉
      Submodule.span (PolynomialImageAlgebra F) {q} := by
  letI := D.finiteIntermediate
  letI : FiniteDimensional (PolynomialMapBaseFunctionField F) N := D.finiteNormal
  letI : Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N := inferInstance
  obtain ⟨⟨a, ha⟩, haq⟩ :=
    polynomialConjugateInvariantAlgebra_quotient_isTorsion D (x := q)
  exact exists_polynomial_leibniz_not_mem_span_singleton
    (AlgEquiv.ofInjective (coordinateAlgHom F)
      (coordinateAlgHom_injective_of_finiteDimensional F))
    (fun i => planarKellerInvariantQuotientOperator D c hc hJ i)
    (fun i b m => planarKellerInvariantQuotientOperator_leibniz D c hc hJ i b m)
    q hq ⟨a, nonZeroDivisors.ne_zero ha, haq⟩

end

end CollisionIdeals
