import CollisionIdeals.General.Keller.ConjugateInvariantBoundary
import CollisionIdeals.General.Normalization.PolynomialConormal
import CollisionIdeals.General.Normalization.FiniteConormalTest

/-!
# The actual target-boundary conormal criterion

Transport the target polynomial partials to the coordinate-image algebra.
These are target-coordinate derivatives, not ordinary source partials of
the evaluated polynomial. Apply the existing conormal construction to the
actual reduced boundary ideal.

In characteristic zero, vanishing of all these components is equivalent
to the target open being the whole target. This criterion requires no
principal boundary equation. It does not prove the components vanish for
a Keller map.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

private theorem cotangent_finite_of_fg {B : Type*} [CommRing B]
    (I : Ideal B) (hI : I.FG) : Module.Finite B I.Cotangent := by
  letI : Module.Finite B I := Module.Finite.of_fg hI
  exact Module.Finite.of_surjective I.toCotangent I.toCotangent_surjective

variable {k : Type u} [Field k] {n : ℕ}

/-- The partial in a target coordinate, transported to the actual
coordinate-image algebra of a generically finite polynomial map. -/
def polynomialImageCoordinatePartial (F : PolynomialSelfMap k n)
    [FiniteDimensional (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F)] (i : Fin n) :
    Derivation k (PolynomialImageAlgebra F) (PolynomialImageAlgebra F) :=
  polynomialEquivPartial
    (AlgEquiv.ofInjective (coordinateAlgHom F)
      (coordinateAlgHom_injective_of_finiteDimensional F)) i

/-- Target evaluation intertwines the transported partial with the
partial of the target polynomial before evaluation. -/
theorem polynomialImageCoordinatePartial_rangeRestrict
    (F : PolynomialSelfMap k n)
    [FiniteDimensional (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F)] (i : Fin n)
    (p : SourceRing k (Fin n)) :
    polynomialImageCoordinatePartial F i ((coordinateAlgHom F).rangeRestrict p) =
      (coordinateAlgHom F).rangeRestrict (MvPolynomial.pderiv i p) := by
  exact polynomialEquivPartial_apply_equiv
    (AlgEquiv.ofInjective (coordinateAlgHom F)
      (coordinateAlgHom_injective_of_finiteDimensional F)) i p

variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

/-- The actual conormal module is finitely generated over the target base.
This does not assert that it is cyclic or choose a boundary equation. -/
theorem polynomialConjugateInvariantBoundary_cotangent_finite
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Module.Finite (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantBoundaryIdeal D hKeller).Cotangent :=
  cotangent_finite_of_fg _ (polynomialConjugateInvariantBoundaryIdeal_fg D hKeller)

/-- The actual boundary's coordinate conormal components vanish exactly
when its target open is the whole target. This does not establish either
side for an arbitrary Keller map. -/
theorem polynomialConjugateInvariantBoundary_conormal_eq_zero_iff
    [CharZero k]
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    letI := D.finiteIntermediate
    (∀ i : Fin n, derivationConormalComponent (polynomialImageCoordinatePartial F i)
      (polynomialConjugateInvariantBoundaryIdeal D hKeller) = 0) ↔
      polynomialConjugateInvariantTargetOpen D hKeller = ⊤ := by
  letI := D.finiteIntermediate
  exact (forall_polynomialEquivPartial_conormalComponent_eq_zero_iff
    (AlgEquiv.ofInjective (coordinateAlgHom F)
      (coordinateAlgHom_injective_of_finiteDimensional F))
    (polynomialConjugateInvariantBoundaryIdeal D hKeller)
    (polynomialConjugateInvariantBoundaryIdeal_ne_bot D hKeller)).trans
    (polynomialConjugateInvariantBoundaryIdeal_eq_top_iff D hKeller)

/-- Any finite generating set for the actual boundary ideal tests its
emptiness by the target-coordinate derivatives of those generators. -/
theorem polynomialConjugateInvariantBoundary_generator_test_iff
    [CharZero k] (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (generators : Finset (PolynomialImageAlgebra F))
    (hGenerators : Ideal.span (generators : Set (PolynomialImageAlgebra F)) =
      polynomialConjugateInvariantBoundaryIdeal D hKeller) :
    letI := D.finiteIntermediate
    (∀ i : Fin n, ∀ f ∈ generators, polynomialImageCoordinatePartial F i f ∈
      polynomialConjugateInvariantBoundaryIdeal D hKeller) ↔
      polynomialConjugateInvariantTargetOpen D hKeller = ⊤ := by
  letI := D.finiteIntermediate
  exact (forall_derivationConormalComponent_eq_zero_iff_on_generators
    (polynomialImageCoordinatePartial F)
    (polynomialConjugateInvariantBoundaryIdeal D hKeller) generators hGenerators).symm.trans
    (polynomialConjugateInvariantBoundary_conormal_eq_zero_iff D hKeller)

/-- The actual boundary supplies a finite test internally. This constructs
the test, not a proof that its generator derivatives belong to the ideal. -/
theorem polynomialConjugateInvariantBoundary_exists_finset_test
    [CharZero k] (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    letI := D.finiteIntermediate
    ∃ generators : Finset (PolynomialImageAlgebra F),
      Ideal.span (generators : Set (PolynomialImageAlgebra F)) =
        polynomialConjugateInvariantBoundaryIdeal D hKeller ∧
      ((∀ i : Fin n, ∀ f ∈ generators, polynomialImageCoordinatePartial F i f ∈
        polynomialConjugateInvariantBoundaryIdeal D hKeller) ↔
        polynomialConjugateInvariantTargetOpen D hKeller = ⊤) := by
  letI := D.finiteIntermediate
  obtain ⟨generators, hGenerators⟩ := polynomialConjugateInvariantBoundaryIdeal_fg D hKeller
  exact ⟨generators, hGenerators,
    polynomialConjugateInvariantBoundary_generator_test_iff D hKeller generators hGenerators⟩

end

end CollisionIdeals
