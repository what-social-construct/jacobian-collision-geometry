import CollisionIdeals.General.Galois.ConjugateAlgebra
import CollisionIdeals.General.Keller.Etale

/-!
# Unramifiedness of the all-conjugate polynomial algebra

For a Keller map, each polynomial source algebra is étale over the
coordinate-image algebra. Since their conjugate images generate the actual
all-conjugate algebra, uniqueness of infinitesimal lifts passes to that
algebra. Together with its existing finite-generation theorem, this proves
unramifiedness.

No tensor-product component, flatness, or étale quotient is assumed here.
In particular, this theorem does not identify an invariant open or assert
that its boundary is empty.
-/

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance conjugateUnramifiedBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

/-- Uniqueness of infinitesimal lifts holds on the actual all-conjugate
algebra because it holds on every generating polynomial source sheet. -/
theorem polynomialConjugateAlgebra_formallyUnramified_of_isKeller
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Algebra.FormallyUnramified (PolynomialImageAlgebra F)
      (polynomialConjugateAlgebra D) := by
  letI : Algebra.Etale (PolynomialImageAlgebra F)
      (PolynomialSourceCoordinateRing k n) :=
    polynomialSource_etale_of_isKeller F hKeller
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro T _ _ I hI f₁ f₂ h
  let source (g : D.galoisGroup) :
      PolynomialSourceCoordinateRing k n →ₐ[PolynomialImageAlgebra F]
        polynomialConjugateAlgebra D :=
    (polynomialConjugateSourceMapOverImage D g).codRestrict
      (polynomialConjugateAlgebra D)
      (polynomialConjugateAlgebra_polynomial_mem D g)
  have hsource (g : D.galoisGroup) :
      f₁.comp (source g) = f₂.comp (source g) := by
    apply Algebra.FormallyUnramified.comp_injective I hI
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, h]
  apply AlgHom.ext
  rintro ⟨z, hz⟩
  refine Algebra.adjoin_induction
    (p := fun z hz => f₁ ⟨z, hz⟩ = f₂ ⟨z, hz⟩) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨⟨g, i⟩, rfl⟩
    exact AlgHom.congr_fun (hsource g) (X i)
  · intro b
    exact (f₁.commutes b).trans (f₂.commutes b).symm
  · intro x y hx hy hfx hfy
    change f₁ (⟨x, hx⟩ + ⟨y, hy⟩) = f₂ (⟨x, hx⟩ + ⟨y, hy⟩)
    exact (map_add f₁ (⟨x, hx⟩ : polynomialConjugateAlgebra D) ⟨y, hy⟩).trans
      ((congrArg₂ (· + ·) hfx hfy).trans
        (map_add f₂ (⟨x, hx⟩ : polynomialConjugateAlgebra D) ⟨y, hy⟩).symm)
  · intro x y hx hy hfx hfy
    change f₁ (⟨x, hx⟩ * ⟨y, hy⟩) = f₂ (⟨x, hx⟩ * ⟨y, hy⟩)
    exact (map_mul f₁ (⟨x, hx⟩ : polynomialConjugateAlgebra D) ⟨y, hy⟩).trans
      ((congrArg₂ (· * ·) hfx hfy).trans
        (map_mul f₂ (⟨x, hx⟩ : polynomialConjugateAlgebra D) ⟨y, hy⟩).symm)

/-- The existing finite generation upgrades formal unramifiedness to
unramifiedness; no flatness conclusion is included. -/
theorem polynomialConjugateAlgebra_unramified_of_isKeller
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    Algebra.Unramified (PolynomialImageAlgebra F)
      (polynomialConjugateAlgebra D) where
  formallyUnramified :=
    polynomialConjugateAlgebra_formallyUnramified_of_isKeller D hKeller
  finiteType := polynomialConjugateAlgebra_finiteType D

end

end CollisionIdeals
