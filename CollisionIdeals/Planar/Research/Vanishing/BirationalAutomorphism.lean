import CollisionIdeals.General.Automorphism.Criteria
import CollisionIdeals.General.Keller.SourceIntersection

/-!
# Birational Keller maps are polynomial automorphisms

The existing source-intersection theorem says `A ∩ K = B`. When the
function-field extension is trivial, every polynomial source element
belongs to the embedded base field, hence already to the coordinate-image
algebra. Thus substitution is surjective; Keller injectivity gives the
polynomial automorphism. No Ax--Grothendieck or Galois-rigidity input is used.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- A Keller map inducing a trivial function-field extension is a
polynomial automorphism, by the existing source/base-field intersection. -/
theorem isPolynomialAutomorphism_of_isKeller_of_functionFieldExtensionTrivial
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F)
    (hTrivial : PolynomialFunctionFieldExtensionTrivial F) :
    IsPolynomialAutomorphism F := by
  have hSurjective : Function.Surjective (coordinateAlgHom F) := by
    intro a
    have hBase :
        algebraMap (SourceRing k (Fin n)) (PolynomialMapSourceFunctionField F) a ∈
          Set.range (algebraMap (PolynomialMapBaseFunctionField F)
            (PolynomialMapSourceFunctionField F)) := by
      exact hTrivial (algebraMap (SourceRing k (Fin n))
        (PolynomialMapSourceFunctionField F) a)
    exact (polynomialSource_mem_range_baseField_iff_of_isKeller F hKeller a).mp hBase
  have hBijective : Function.Bijective (coordinateAlgHom F) :=
    ⟨coordinateAlgHom_injective_of_isKeller F hKeller, hSurjective⟩
  simpa only [IsPolynomialAutomorphism, coordinateAlgHom, MvPolynomial.aeval_eq_bind₁]
    using hBijective

end

end CollisionIdeals
