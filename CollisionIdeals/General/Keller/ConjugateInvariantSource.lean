import CollisionIdeals.General.Keller.SourceIntersection
import CollisionIdeals.General.Galois.ConjugateInvariants

/-!
# Source-regular elements of the actual fixed algebra

The Keller source/base-field intersection theorem identifies the part of
the existing fixed algebra that is regular on the marked polynomial
source: it is exactly the image of the coordinate-image base.

This does not assert that every fixed-algebra element is source-regular.
In particular, the inclusion needed to remove the target boundary is not
assumed or proved here. No new intersection algebra is defined.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n} {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

/-- A fixed-algebra element belongs to the marked polynomial source iff
it comes from the target base. This is a pointwise intersection theorem,
not a claim that the entire fixed algebra belongs to the source. -/
theorem polynomialConjugateInvariantAlgebra_mem_source_iff_mem_base
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (z : polynomialConjugateInvariantAlgebra D) :
    (z.val : N) ∈ Set.range (polynomialConjugateSourceMapOverImage D 1) ↔
      z ∈ Set.range
        (algebraMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D)) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨t, ht⟩ :=
      (polynomialConjugateInvariantAlgebra_mem_iff_baseField D z.val).mp z.property
    have hField : algebraMap (PolynomialSourceCoordinateRing k n)
        (PolynomialMapSourceFunctionField F) a ∈
        Set.range (algebraMap (PolynomialMapBaseFunctionField F)
          (PolynomialMapSourceFunctionField F)) := by
      refine ⟨t, D.embedding.injective ?_⟩
      change D.embedding (algebraMap (PolynomialMapBaseFunctionField F)
        (PolynomialMapSourceFunctionField F) t) =
        D.embedding (algebraMap (PolynomialSourceCoordinateRing k n)
          (PolynomialMapSourceFunctionField F) a)
      rw [D.embedding.commutes]
      exact ht.trans ha.symm
    have hSource :=
      (polynomialSource_mem_range_baseField_iff_of_isKeller F hKeller a).mp hField
    let b : PolynomialImageAlgebra F := ⟨a, hSource⟩
    refine ⟨b, Subtype.ext (Subtype.ext ?_)⟩
    change algebraMap (PolynomialImageAlgebra F) N b = (z.val : N)
    rw [← (polynomialConjugateSourceMapOverImage D 1).commutes b]
    exact ha
  · rintro ⟨b, rfl⟩
    refine ⟨algebraMap (PolynomialImageAlgebra F) (PolynomialSourceCoordinateRing k n) b, ?_⟩
    exact (polynomialConjugateSourceMapOverImage D 1).commutes b

end

end CollisionIdeals
