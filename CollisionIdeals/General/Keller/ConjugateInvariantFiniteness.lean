import CollisionIdeals.General.Keller.ConjugateInvariantConormal
import CollisionIdeals.General.Normalization.FullOpenAlgebra

/-!
# Empty invariant target boundary implies source finiteness

If the actual target open is the whole target, its fixed algebra is the
base algebra. The all-conjugate algebra is already finite over that fixed
algebra, so it becomes finite over the base. The original polynomial
source embeds in it and is finite as a submodule over the Noetherian base.

These are conditional consequences of an empty boundary, not a proof that
the boundary is empty. No principal equation, free-action comparison, or
new rigidity input is used.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

private theorem finite_of_surjective_algebraMap
    (B I : Type*) [CommRing B] [CommRing I] [Algebra B I]
    (h : Function.Surjective (algebraMap B I)) : Module.Finite B I :=
  Module.Finite.of_surjective (Algebra.linearMap B I) h

private theorem finite_of_injective_algHom
    {B A E : Type*} [CommRing B] [CommRing A] [CommRing E]
    [Algebra B A] [Algebra B E] [IsNoetherianRing B] [Module.Finite B E]
    (f : A →ₐ[B] E) (hf : Function.Injective f) : Module.Finite B A :=
  Module.Finite.of_injective f.toLinearMap hf

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

set_option synthInstance.maxHeartbeats 80000 in
/-- A unit actual boundary ideal makes the canonical base-to-fixed-algebra
map bijective. This is not an unconditional identification of the rings. -/
theorem polynomialConjugateInvariantAlgebra_algebraMap_bijective_of_boundary_eq_top
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (hBoundary : polynomialConjugateInvariantBoundaryIdeal D hKeller = ⊤) :
    Function.Bijective
      (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)) := by
  letI := polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller D hKeller
  exact algebraMap_bijective_of_specMap_isOpenImmersion_of_opensRange_eq_top
    (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)
    ((polynomialConjugateInvariantBoundaryIdeal_eq_top_iff D hKeller).mp hBoundary)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- Empty target boundary upgrades the existing invariant-ring finiteness
to finiteness of the all-conjugate algebra over the target base. -/
theorem polynomialConjugateAlgebra_finite_of_boundary_eq_top
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (hBoundary : polynomialConjugateInvariantBoundaryIdeal D hKeller = ⊤) :
    Module.Finite (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI := finite_of_surjective_algebraMap
    (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)
    (polynomialConjugateInvariantAlgebra_algebraMap_bijective_of_boundary_eq_top
      D hKeller hBoundary).surjective
  letI := polynomialConjugateAlgebra_finite_over_invariants D
  letI : IsScalarTower (PolynomialImageAlgebra F)
      (polynomialConjugateInvariantAlgebra D) (polynomialConjugateAlgebra D) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.trans (polynomialConjugateInvariantAlgebra D)
    (polynomialConjugateAlgebra D)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- The polynomial source is finite over its coordinate-image algebra
when the actual invariant target boundary is empty. -/
theorem polynomialSource_finite_of_conjugateInvariantBoundary_eq_top
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (hBoundary : polynomialConjugateInvariantBoundaryIdeal D hKeller = ⊤) :
    Module.Finite (PolynomialImageAlgebra F) (PolynomialSourceCoordinateRing k n) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI := polynomialImageAlgebra_isNoetherianRing F
  letI := polynomialConjugateAlgebra_finite_of_boundary_eq_top D hKeller hBoundary
  let f : PolynomialSourceCoordinateRing k n →ₐ[PolynomialImageAlgebra F]
      polynomialConjugateAlgebra D :=
    (polynomialConjugateSourceMapOverImage D 1).codRestrict
      (polynomialConjugateAlgebra D) (polynomialConjugateAlgebra_polynomial_mem D 1)
  apply finite_of_injective_algHom (B := PolynomialImageAlgebra F)
    (A := PolynomialSourceCoordinateRing k n) (E := polynomialConjugateAlgebra D) f
  intro x y hxy
  apply IsFractionRing.injective (PolynomialSourceCoordinateRing k n)
    (PolynomialMapSourceFunctionField F)
  apply D.embedding.injective
  exact congrArg Subtype.val hxy

/-- Vanishing of the actual coordinate conormal components is sufficient
for source finiteness, by the proved empty-boundary criterion. -/
theorem polynomialSource_finite_of_conjugateInvariantBoundary_conormal_eq_zero
    [CharZero k] (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (hConormal : letI := D.finiteIntermediate
      ∀ i : Fin n, derivationConormalComponent (polynomialImageCoordinatePartial F i)
        (polynomialConjugateInvariantBoundaryIdeal D hKeller) = 0) :
    Module.Finite (PolynomialImageAlgebra F) (PolynomialSourceCoordinateRing k n) := by
  apply polynomialSource_finite_of_conjugateInvariantBoundary_eq_top D hKeller
  apply (polynomialConjugateInvariantBoundaryIdeal_eq_top_iff D hKeller).mpr
  exact (polynomialConjugateInvariantBoundary_conormal_eq_zero_iff D hKeller).mp hConormal

end

end CollisionIdeals
