import CollisionIdeals.General.Normalization.Polynomial
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Finite normalization of a generically finite polynomial map

For a polynomial map between affine spaces of the same dimension, finiteness
of the induced function-field extension implies algebraic independence of
the coordinate polynomials. Its coordinate-image algebra is therefore a
polynomial ring, in particular normal. Finite separable extensions then have
finite integral closures over this algebra.

These are the finiteness fields of a normalization cover, not its
Zariski-main open immersion or its divisorial inertia data.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- A generically finite polynomial map of equal-dimensional affine spaces
has algebraically independent coordinate polynomials. -/
theorem coordinateAlgHom_injective_of_finiteDimensional
    (F : PolynomialSelfMap k n)
    [FiniteDimensional (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F)] :
    Function.Injective (coordinateAlgHom F) := by
  let B := PolynomialImageAlgebra F
  let A := SourceRing k (Fin n)
  let K := PolynomialMapBaseFunctionField F
  let L := PolynomialMapSourceFunctionField F
  letI : Algebra.IsAlgebraic B L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := B) (K := K) (C := L)).mpr
      (Algebra.IsAlgebraic.of_finite K L)
  have hBA : Algebra.IsAlgebraic B A :=
    (IsFractionRing.isAlgebraic_iff' B A L).mpr inferInstance
  have hB : B = Algebra.adjoin k (Set.range F) :=
    (Algebra.adjoin_range_eq_range_aeval k F).symm
  haveI : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range F)) A := hB ▸ hBA
  have hF := Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite
    k F (by simp [SourceRing])
  exact (algebraicIndependent_iff_injective_aeval.mp hF.1)

/-- The coordinate image of a generically finite polynomial map is normal. -/
theorem polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional
    (F : PolynomialSelfMap k n)
    [FiniteDimensional (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F)] :
    IsIntegrallyClosed (PolynomialImageAlgebra F) :=
  IsIntegrallyClosed.of_equiv
    (AlgEquiv.ofInjective (coordinateAlgHom F)
      (coordinateAlgHom_injective_of_finiteDimensional F)).toRingEquiv

/-- Every coordinate-image algebra of a polynomial map is Noetherian. -/
theorem polynomialImageAlgebra_isNoetherianRing
    (F : PolynomialSelfMap k n) : IsNoetherianRing (PolynomialImageAlgebra F) :=
  isNoetherianRing_of_surjective (SourceRing k (Fin n)) (PolynomialImageAlgebra F)
    (coordinateAlgHom F).rangeRestrict.toRingHom
    (coordinateAlgHom F).rangeRestrict_surjective

/-- The intermediate normalization is finite for a finite separable generic
extension. No scheme-normalization model is supplied as an input. -/
theorem polynomialIntermediateNormalization_finite
    (F : PolynomialSelfMap k n)
    [FiniteDimensional (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F)]
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F)] :
    IsPolynomialIntermediateNormalizationFinite F := by
  letI := polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  letI := polynomialImageAlgebra_isNoetherianRing F
  exact IsIntegralClosure.finite (PolynomialImageAlgebra F)
    (PolynomialMapBaseFunctionField F) (PolynomialMapSourceFunctionField F)
    (PolynomialIntermediateNormalizationRing F)

/-- The normal-closure normalization is finite whenever the marked finite
normal closure is separable. -/
theorem polynomialNormalClosureNormalization_finite
    {F : PolynomialSelfMap k n} {N : Type u} [Field N]
    [Algebra (PolynomialMapBaseFunctionField F) N]
    [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N) :
    IsPolynomialFiniteNormalizationInExtension (F := F) (N := N) := by
  letI := D.finiteIntermediate
  letI := D.finiteNormal
  letI := polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  letI := polynomialImageAlgebra_isNoetherianRing F
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : IsScalarTower (PolynomialImageAlgebra F)
      (PolynomialMapBaseFunctionField F) N :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact IsIntegralClosure.finite (PolynomialImageAlgebra F)
    (PolynomialMapBaseFunctionField F) N
    (PolynomialNormalizationInExtensionRing (F := F) (N := N))

end

end CollisionIdeals
