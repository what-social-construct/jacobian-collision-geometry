import CollisionIdeals.General.Normalization.Polynomial
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# A finite source fills its intermediate normalization

If the intermediate ring is integrally closed in the overring and is
module-finite over the base, the existing map from its relative integral
closure is bijective. For a polynomial source this makes the canonical
source-to-intermediate-normalization morphism an isomorphism and removes
its deleted boundary.

Finiteness of the actual source is an explicit input. This file does not
deduce it from generic finiteness or from the Keller condition.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

section General

variable (B A E : Type u) [CommRing B] [CommRing A] [CommRing E]
  [Algebra B A] [Algebra B E] [Algebra A E] [IsScalarTower B A E]
  [IsIntegralClosure A A E] [Module.Finite B A]

/-- An actual finite intermediate ring is the entire relative integral
closure, provided it is integrally closed in the chosen overring. -/
theorem normalizationToIntermediate_surjective_of_finite :
    Function.Surjective
      (normalizationToIntermediate (B := B) (A := A) (E := E)) := by
  intro a
  let x : normalizedCoordinateRing B E :=
    ⟨algebraMap A E a,
      (IsIntegral.of_finite B a).map (IsScalarTower.toAlgHom B A E)⟩
  refine ⟨x, ?_⟩
  apply IsIntegralClosure.algebraMap_injective A A E
  exact algebraMap_normalizationToIntermediate (B := B) (A := A) (E := E) x

/-- The canonical normalization map is bijective under source finiteness. -/
theorem normalizationToIntermediate_bijective_of_finite :
    Function.Bijective
      (normalizationToIntermediate (B := B) (A := A) (E := E)) :=
  ⟨normalizationToIntermediate_injective (B := B) (A := A) (E := E),
    normalizationToIntermediate_surjective_of_finite B A E⟩

/-- Finiteness makes the existing intermediate-normalization morphism an
isomorphism; no open-immersion or Keller hypothesis is required. -/
theorem intermediateToNormalization_isIso_of_finite :
    IsIso (intermediateToNormalization (B := B) (A := A) (E := E)) := by
  let e := AlgEquiv.ofBijective
    (normalizationToIntermediate (B := B) (A := A) (E := E))
    (normalizationToIntermediate_bijective_of_finite B A E)
  letI : IsIso (CommRingCat.ofHom
      (normalizationToIntermediate (B := B) (A := A) (E := E)).toRingHom) :=
    inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
  unfold intermediateToNormalization
  infer_instance

end General

section Polynomial

variable {k : Type u} [Field k] {n : ℕ}
  (F : PolynomialSelfMap k n)
  [Module.Finite (PolynomialImageAlgebra F) (PolynomialSourceCoordinateRing k n)]

/-- A finite polynomial source fills its intermediate normalization. -/
theorem polynomialSourceToIntermediateNormalization_isIso_of_finite :
    IsIso (polynomialSourceToIntermediateNormalization F) :=
  intermediateToNormalization_isIso_of_finite
    (PolynomialImageAlgebra F) (PolynomialSourceCoordinateRing k n)
    (PolynomialMapSourceFunctionField F)

/-- The deleted intermediate-normalization boundary is empty for an
actual finite polynomial source. This is not the target-open boundary
ideal and does not assume that either boundary has already vanished. -/
theorem polynomialIntermediateNormalizationBoundary_eq_empty_of_finite :
    polynomialIntermediateNormalizationBoundary F = ∅ := by
  letI := polynomialSourceToIntermediateNormalization_isIso_of_finite F
  have hsurj : Function.Surjective
      (polynomialSourceToIntermediateNormalization F).base :=
    (polynomialSourceToIntermediateNormalization F).surjective
  rw [polynomialIntermediateNormalizationBoundary, Set.range_eq_univ.mpr hsurj,
    Set.compl_univ]

end Polynomial

end

end CollisionIdeals
