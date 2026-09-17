import CollisionIdeals.Planar.NormalizationDiagram

set_option autoImplicit false

namespace CollisionIdeals.Planar

open AlgebraicGeometry

noncomputable section

/--
Specialized branch purity for a finite normal cover of the complex affine
plane.

The normalized-cover data already contains finiteness. Unramifiedness at
every height-one prime promotes to étaleness of the entire normalization
morphism.
-/
def BranchPurityA2 : Prop :=
  ∀ {F : PlanarPolynomialMap}
    {N : Type} [Field N]
    [Algebra (PlanarBaseFunctionField F) N]
    (_M : PlanarNormalizedCover (F := F) (N := N)),
    NoCodimensionOneRamification (F := F) (N := N) →
      Etale
        (planarNormalizationInExtensionToBase
          (F := F) (N := N))

/--
Triviality of connected finite étale covers of `𝔸²_ℂ`, specialized to the
normal-closure model.
-/
def AffinePlaneFiniteEtaleRigidity : Prop :=
  ∀ {F : PlanarPolynomialMap}
    {N : Type} [Field N]
    [Algebra (PlanarBaseFunctionField F) N]
    (M : PlanarNormalizedCover (F := F) (N := N)),
    Etale
        (planarNormalizationInExtensionToBase
          (F := F) (N := N)) →
      M.normalClosure.ExtensionTrivial

end

end CollisionIdeals.Planar
