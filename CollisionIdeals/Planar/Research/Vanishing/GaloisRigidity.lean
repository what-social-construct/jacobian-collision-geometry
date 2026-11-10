import CollisionIdeals.General.Automorphism.GaloisRigidity
import CollisionIdeals.Planar.Research.Vanishing.BirationalAutomorphism
import CollisionIdeals.Planar.Research.Vanishing.NormalRamification
import CollisionIdeals.Planar.Research.Vanishing.Ramification

/-!
# Planar Keller--Galois rigidity from the geometric endgame

Normality of the original function-field extension makes its marked fixing
subgroup trivial. A visible inertia-fixed sheet then excludes every ramified
height-one normalization prime. Purity and affine-plane finite-etale rigidity
trivialize the canonical extension. The existing source-intersection theorem
then gives polynomial invertibility without Ax--Grothendieck.

The two geometric results remain explicit theorem inputs. This file imports
no custom literature axioms, proves no universal planar vanishing statement,
and does not replace the dimension-three rigidity input.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar.Research

noncomputable section

/-- In the normal case, the two geometric inputs trivialize the original
function-field extension, with its canonical closure constructed internally. -/
theorem planarFunctionFieldExtensionTrivial_of_normal_of_geometry
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (hNormal : Normal (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F)) :
    PolynomialFunctionFieldExtensionTrivial F := by
  let C := polynomialNormalizedCoverOfIsKeller F hKeller
  have hNoRamification :=
    polynomialCanonicalNoCodimensionOneRamification_of_isKeller_of_normal
      F hKeller hNormal
  have hExtensionTrivial : C.normalClosure.ExtensionTrivial :=
    hFiniteEtaleRigidity C (hPurity C hNoRamification)
  exact PolynomialNormalClosureData.functionFieldExtensionTrivial_of_extensionTrivial
    C.normalClosure hExtensionTrivial

/-- Normality supplies the no-ramification premise of the existing planar
vanishing endgame. No universal boundary-vanishing premise is added. -/
theorem planarVanishing_of_normal_of_geometry
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (hNormal : Normal (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F)) :
    obstructionIdeal F = ⊥ := by
  exact obstructionIdeal_eq_bot_of_functionFieldExtensionTrivial F
    (KellerEtaleBridge.toKellerFlatBridge F (kellerEtaleBridge F) hKeller)
    (planarFunctionFieldExtensionTrivial_of_normal_of_geometry
      hPurity hFiniteEtaleRigidity F hKeller hNormal)

/-- Planar Keller--Galois rigidity is derived from purity and affine-plane
finite-etale rigidity, not taken as a third independent literature input. -/
theorem complexKellerGaloisRigidity_two_of_geometry
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity) :
    ComplexKellerGaloisRigidity 2 := by
  intro F hKeller hNormal
  exact isPolynomialAutomorphism_of_isKeller_of_functionFieldExtensionTrivial
    F hKeller
    (planarFunctionFieldExtensionTrivial_of_normal_of_geometry
      hPurity hFiniteEtaleRigidity F hKeller hNormal)

end

end CollisionIdeals.Planar.Research
