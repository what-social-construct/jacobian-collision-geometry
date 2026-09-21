import CollisionIdeals.General.Keller.ConjugateInvariantSource
import CollisionIdeals.General.Keller.ConjugateInvariantFiniteness

/-!
# Source regularity characterizes the actual empty target boundary

For a Keller map, every element of the fixed algebra is regular on the
marked polynomial source exactly when the canonical base-to-fixed-algebra
map is surjective. This is equivalent to the actual target boundary ideal
being the unit ideal.

The statements use the existing inclusions rather than identifying rings
with different subtype presentations. They characterize an empty boundary;
they do not assert source regularity or boundary emptiness for every map.
No characteristic-zero, purity, or Galois-rigidity input is used here.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n} {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

/-- Regularity of every fixed element on the marked source is exactly
surjectivity of the canonical base-to-fixed-algebra map. -/
theorem polynomialConjugateInvariantAlgebra_source_regular_iff_surjective
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    (∀ z : polynomialConjugateInvariantAlgebra D,
      (z.val : N) ∈ Set.range (polynomialConjugateSourceMapOverImage D 1)) ↔
      Function.Surjective
        (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)) := by
  constructor
  · intro h z
    exact (polynomialConjugateInvariantAlgebra_mem_source_iff_mem_base D hKeller z).mp (h z)
  · intro h z
    exact (polynomialConjugateInvariantAlgebra_mem_source_iff_mem_base D hKeller z).mpr (h z)

set_option synthInstance.maxHeartbeats 80000 in
/-- The canonical base-to-fixed-algebra map is surjective exactly when
the actual target boundary ideal is the unit ideal. -/
theorem polynomialConjugateInvariantAlgebra_surjective_iff_boundary_eq_top
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Function.Surjective
      (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)) ↔
      polynomialConjugateInvariantBoundaryIdeal D hKeller = ⊤ := by
  constructor
  · intro hSurjective
    have hInjective : Function.Injective
        (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)) := by
      intro x y hxy
      apply IsFractionRing.injective (PolynomialImageAlgebra F)
        (PolynomialMapBaseFunctionField F)
      apply (algebraMap (PolynomialMapBaseFunctionField F) N).injective
      exact congrArg (fun z : polynomialConjugateInvariantAlgebra D => (z.val : N)) hxy
    letI : IsIso (Spec.map (CommRingCat.ofHom
        (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)))) :=
      isIso_SpecMap_iff.mpr ⟨hInjective, hSurjective⟩
    apply (polynomialConjugateInvariantBoundaryIdeal_eq_top_iff D hKeller).mpr
    exact Scheme.Hom.opensRange_of_isIso _
  · intro hBoundary
    exact (polynomialConjugateInvariantAlgebra_algebraMap_bijective_of_boundary_eq_top
      D hKeller hBoundary).surjective

/-- Source regularity of the fixed algebra characterizes emptiness of
the actual target boundary, without asserting either condition. -/
theorem polynomialConjugateInvariantAlgebra_source_regular_iff_boundary_eq_top
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    (∀ z : polynomialConjugateInvariantAlgebra D,
      (z.val : N) ∈ Set.range (polynomialConjugateSourceMapOverImage D 1)) ↔
      polynomialConjugateInvariantBoundaryIdeal D hKeller = ⊤ :=
  (polynomialConjugateInvariantAlgebra_source_regular_iff_surjective D hKeller).trans
    (polynomialConjugateInvariantAlgebra_surjective_iff_boundary_eq_top D hKeller)

end

end CollisionIdeals
