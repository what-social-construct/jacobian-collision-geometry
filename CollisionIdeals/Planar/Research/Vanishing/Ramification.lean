import CollisionIdeals.General.Automorphism.GenericDegreeOne
import CollisionIdeals.General.Keller.Etale
import CollisionIdeals.General.Keller.Normalization
import CollisionIdeals.Planar.External.Interfaces
import CollisionIdeals.Planar.Statements.Vanishing

/-!
# The ramification route to planar vanishing

The direct endgame needs only a finite normalized cover and the Keller
condition, not the larger collision model with conjugate-sheet indices.
The canonical cover is already constructed from the Keller condition.

Purity and finite-etale rigidity are explicit theorem inputs. The remaining
planar no-ramification statement is also an explicit input: this file proves
the reduction to the existing `PlanarVanishing` target, not that target itself.
It imports no custom literature axioms or collision-model constructor.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

/-- For the direct no-ramification route, the finite normalized cover suffices.
Conjugate centers, inertia indices, and a full Keller collision model are not
inputs to this endgame. -/
theorem planarVanishing_of_normalizedCover_noCodimensionOneRamification
    {F : PlanarPolynomialMap} {N : Type} [Field N]
    [Algebra (PlanarBaseFunctionField F) N]
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (hKeller : IsKeller F)
    (C : PlanarNormalizedCover (F := F) (N := N))
    (hNoRamification : NoCodimensionOneRamification (F := F) (N := N)) :
    obstructionIdeal F = ⊥ := by
  have hExtensionTrivial : C.normalClosure.ExtensionTrivial :=
    hFiniteEtaleRigidity C (hPurity C hNoRamification)
  exact obstructionIdeal_eq_bot_of_functionFieldExtensionTrivial F
    (KellerEtaleBridge.toKellerFlatBridge F (kellerEtaleBridge F) hKeller)
    (PolynomialNormalClosureData.functionFieldExtensionTrivial_of_extensionTrivial
      C.normalClosure hExtensionTrivial)

/-- The canonical cover removes the model-supply premise from the direct
planar-vanishing reduction. What remains is proving no height-one ramification
for every planar Keller map, together with the stated literature inputs. -/
theorem planarVanishing_of_canonicalNoCodimensionOneRamification
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (hNoRamification : ∀ F : PlanarPolynomialMap, IsKeller F →
      NoCodimensionOneRamification
        (F := F) (N := PolynomialCanonicalNormalClosure F)) :
    PlanarVanishing := by
  intro F hKeller
  exact planarVanishing_of_normalizedCover_noCodimensionOneRamification
    hPurity hFiniteEtaleRigidity hKeller
    (polynomialNormalizedCoverOfIsKeller F hKeller)
    (hNoRamification F hKeller)

end

end CollisionIdeals.Planar
