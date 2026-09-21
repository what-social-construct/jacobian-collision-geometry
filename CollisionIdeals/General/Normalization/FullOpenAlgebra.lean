import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# A full affine open recovers the base algebra

An open immersion of affine schemes whose image is the whole target is
an isomorphism. Consequently its defining algebra map is bijective.
This converts a proved empty-boundary statement into an algebraic
identification; it does not prove that the boundary is empty.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

universe u

/-- When the open immersion induced by a `B`-algebra has full image,
its algebra map is bijective. No finite-type or domain assumptions are
needed beyond the supplied open immersion. -/
theorem algebraMap_bijective_of_specMap_isOpenImmersion_of_opensRange_eq_top
    (B I : Type u) [CommRing B] [CommRing I] [Algebra B I]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B I)))]
    (hfull : (Spec.map (CommRingCat.ofHom (algebraMap B I))).opensRange = ⊤) :
    Function.Bijective (algebraMap B I) := by
  exact isIso_SpecMap_iff.mp
    (isIso_of_isOpenImmersion_of_opensRange_eq_top _ hfull)

end CollisionIdeals
