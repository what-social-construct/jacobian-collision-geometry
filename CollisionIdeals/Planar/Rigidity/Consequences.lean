import CollisionIdeals.General.Automorphism.Criteria
import CollisionIdeals.General.Automorphism.GenericDegreeOne
import CollisionIdeals.General.Keller.CollisionModel
import CollisionIdeals.General.Galois.NormalClosure
import CollisionIdeals.Planar.Boundary.Separation
import CollisionIdeals.Planar.External.Assumptions
import CollisionIdeals.Planar.Rigidity.Interfaces

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

/--
The shared Keller collision-normalization model, specialized to the
complex affine plane.  PlanarHiddenInertia names the positive
boundary-supported orbit obstruction; its negation remains separate.
-/
abbrev PlanarKellerCollisionModel
    (F : PlanarPolynomialMap) :=
  PolynomialKellerCollisionModel F

namespace PlanarKellerCollisionModel

variable {F : PlanarPolynomialMap}

/-- The canonical pulled-back boundary package carried by a Keller model. -/
def boundaryIdealData (M : PlanarKellerCollisionModel F) :
    letI : Field M.N := M.fieldN
    letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
    BoundaryIdealData M.diagram := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
  exact
    { ramificationRealization := M.ramificationRealization
      sourceEtale := M.kellerEtale M.keller }

/--
The two external algebraic-geometry inputs first trivialize the supplied
normal closure over the planar base field.  This is the type-correct
formal counterpart of `N = K`.  The hNoHidden argument excludes exactly
the positive PlanarHiddenInertia boundary obstruction.
-/
theorem normalClosureExtensionTrivial
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    letI : Field M.N := M.fieldN
    letI : Algebra (PlanarBaseFunctionField F) M.N :=
      M.algebraN
    M.diagram.cover.normalClosure.ExtensionTrivial := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N :=
    M.algebraN
  have hNoCodimensionOneRamification :
      NoCodimensionOneRamification
        (F := F) (N := M.N) :=
    M.diagram.noCodimensionOneRamification
      M.ramifiedConjugateCentersInBoundary_of_keller
      hNoHidden
  have hNormalizationEtale :
      AlgebraicGeometry.Etale
        (planarNormalizationInExtensionToBase
          (F := F) (N := M.N)) :=
    hPurity M.diagram.cover hNoCodimensionOneRamification
  exact
    hFiniteEtaleRigidity M.diagram.cover hNormalizationEtale

/--
The two external algebraic-geometry inputs turn the Keller collision
model and the separate no-hidden-inertia hypothesis into the type-correct
equality `L = K`.
-/
theorem functionFieldExtensionTrivial
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    PlanarFunctionFieldExtensionTrivial F := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N :=
    M.algebraN
  exact
    PolynomialNormalClosureData.functionFieldExtensionTrivial_of_extensionTrivial
      M.diagram.cover.normalClosure
      (M.normalClosureExtensionTrivial
        hPurity hFiniteEtaleRigidity hNoHidden)

end PlanarKellerCollisionModel

/--
Once height-one ramification has been eliminated, purity and finite-étale
rigidity give the complete planar collision-vanishing endgame.
-/
theorem planarVanishing_of_noCodimensionOneRamification
    {F : PlanarPolynomialMap}
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hNoRamification :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
      NoCodimensionOneRamification (F := F) (N := M.N)) :
    obstructionIdeal F = ⊥ := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
  have hNormalizationEtale :
      AlgebraicGeometry.Etale
        (planarNormalizationInExtensionToBase
          (F := F) (N := M.N)) :=
    hPurity M.diagram.cover hNoRamification
  have hExtensionTrivial :
      M.diagram.cover.normalClosure.ExtensionTrivial :=
    hFiniteEtaleRigidity M.diagram.cover hNormalizationEtale
  have hFunctionFieldTrivial :
      PlanarFunctionFieldExtensionTrivial F :=
    PolynomialNormalClosureData.functionFieldExtensionTrivial_of_extensionTrivial
      M.diagram.cover.normalClosure hExtensionTrivial
  exact
    obstructionIdeal_eq_bot_of_functionFieldExtensionTrivial
      F (M.kellerFlat M.keller) hFunctionFieldTrivial

/--
The global boundary-coherence route.  Once the explicit local-cohomology
bridge removes the intermediate-normalization boundary, moving-sheet
coverage is automatic; the common codimension-one endgame then applies.
-/
theorem planarVanishing_of_boundaryCoherence
    {F : PlanarPolynomialMap}
    (hBridge : BoundaryCoherenceBridge)
    (M : PlanarKellerCollisionModel F)
    (hCoherence : PlanarBoundaryCoherence F) :
    obstructionIdeal F = ⊥ := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
  apply planarVanishing_of_noCodimensionOneRamification
    ExternalAssumptions.branchPurityA2
    ExternalAssumptions.affinePlaneFiniteEtaleRigidity M
  apply M.boundaryIdealData.noCodimensionOneRamification_of_movingSheetCoverage
  intro E
  obtain ⟨q, hqIndex⟩ := M.diagram.exists_one_lt_inertiaIndex E
  let g : NormalizationGaloisGroup M.diagram := q.out
  have hq :
      DoubleCoset.mk
          (decompositionGroupAt (PlanarBaseFunctionField F)
            (M.diagram.valuationAt E).valuationRing)
          M.diagram.cover.normalClosure.intermediateFixingSubgroup g = q :=
    DoubleCoset.out_eq' _ _ q
  refine ⟨g, ?_, ?_⟩
  · intro hgFixed
    have hIndexOne :
        M.diagram.inertiaIndex E
            (DoubleCoset.mk
              (decompositionGroupAt (PlanarBaseFunctionField F)
                (M.diagram.valuationAt E).valuationRing)
              M.diagram.cover.normalClosure.intermediateFixingSubgroup g) = 1 :=
      (inertiaQuotientIndex_eq_one_iff _ _).mpr hgFixed
    exact (Nat.ne_of_gt (hq ▸ hqIndex)) hIndexOne
  · change
      (conjugateToIntermediate M.diagram g).base E.1 ∈
        Set.range (polynomialSourceToIntermediateNormalization F).base
    rw [← Set.notMem_compl_iff]
    change
      (conjugateToIntermediate M.diagram g).base E.1 ∉
        polynomialIntermediateNormalizationBoundary F
    rw [hBridge F hCoherence]
    exact Set.notMem_empty _

/--
The divisorial module-theoretic route: finite-length Kähler differentials first
eliminate height-one ramification through the explicit support bridge, after
which purity and finite-étale rigidity complete the planar endgame.
-/
theorem planarVanishing_of_ramificationRigidity
    {F : PlanarPolynomialMap}
    (hBridge : RamificationRigidityBridge)
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hRigidity :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
      PlanarRamificationRigidity (F := F) (N := M.N)) :
    obstructionIdeal F = ⊥ := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N := M.algebraN
  exact
    planarVanishing_of_noCodimensionOneRamification
      hPurity hFiniteEtaleRigidity M
      (hBridge M.diagram.cover hRigidity)

/--
The hypothesis-parametrized planar divisorial endgame.

All concrete normalization and collision data is carried by M.
The planar no-hidden-inertia statement—the negation of the positive
boundary-supported orbit predicate—and the two external algebraic-geometry
inputs remain explicit arguments.
-/
theorem planarVanishing_of
    {F : PlanarPolynomialMap}
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    obstructionIdeal F = ⊥ := by
  exact
    obstructionIdeal_eq_bot_of_functionFieldExtensionTrivial
      F (M.kellerFlat M.keller)
      (M.functionFieldExtensionTrivial
        hPurity hFiniteEtaleRigidity hNoHidden)

/--
The user-facing theorem with the two external algebraic-geometry
assumptions supplied by the dedicated assumptions module.
-/
theorem planarVanishing_assuming_standardGeometry
    {F : PlanarPolynomialMap}
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    obstructionIdeal F = ⊥ :=
  planarVanishing_of
    ExternalAssumptions.branchPurityA2
    ExternalAssumptions.affinePlaneFiniteEtaleRigidity
    M hNoHidden

/--
The explicit conjugate-coverage route through the planar divisorial endgame.
Coverage supplies an inertia-moving affine center for every ramified
divisor; such a center contradicts the boundary conclusion from étaleness,
so no hidden inertia remains.
-/
theorem planarVanishing_of_conjugateCoverage
    {F : PlanarPolynomialMap}
    (M : PlanarKellerCollisionModel F)
    (hCoverage :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarConjugateCoverage M.diagram) :
    obstructionIdeal F = ⊥ := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N :=
    M.algebraN
  exact
    planarVanishing_assuming_standardGeometry M
      (noHiddenInertia_of_conjugateCoverage M.diagram hCoverage)

/--
The canonical pulled-back-open form of moving-sheet coverage yields planar
collision vanishing.  The boundary ideals are constructed from `M.diagram`;
only the exact pointwise coverage statement remains a hypothesis.
-/
theorem planarVanishing_of_movingSheetCoverage
    {F : PlanarPolynomialMap}
    (M : PlanarKellerCollisionModel F)
    (hCoverage :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarMovingSheetCoverage M.diagram) :
    obstructionIdeal F = ⊥ := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N :=
    M.algebraN
  exact
    planarVanishing_of_noCodimensionOneRamification
      ExternalAssumptions.branchPurityA2
      ExternalAssumptions.affinePlaneFiniteEtaleRigidity M
      (M.boundaryIdealData.noCodimensionOneRamification_of_movingSheetCoverage
        hCoverage)

/--
The finite-group, ideal-theoretic route through the planar divisorial
endgame.  Boundary separation says that no height-one prime can contain both
the fixed-locus ideal of a nontrivial subgroup and all boundaries of the
sheets moved by that subgroup.
-/
theorem planarVanishing_of_boundarySeparation
    {F : PlanarPolynomialMap}
    (M : PlanarKellerCollisionModel F)
    (hSeparation :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarBoundarySeparation M.diagram) :
    obstructionIdeal F = ⊥ := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N :=
    M.algebraN
  exact
    planarVanishing_of_noCodimensionOneRamification
      ExternalAssumptions.branchPurityA2
      ExternalAssumptions.affinePlaneFiniteEtaleRigidity M
      (M.boundaryIdealData.noCodimensionOneRamification hSeparation)

/--
Using the third external literature theorem, Ax--Grothendieck, the
hypothesis-parametrized ideal-vanishing result yields a polynomial automorphism.
-/
theorem planarAutomorphism_assuming_externalLiterature
    {F : PlanarPolynomialMap}
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    IsPolynomialAutomorphism F := by
  apply ExternalAssumptions.axGrothendieckA2 F
  exact
    pointMap_injective_of_collisionIdeal_eq_diagonalIdeal F
      ((obstructionIdeal_eq_bot_iff F).1
        (planarVanishing_assuming_standardGeometry M hNoHidden))

/-- The strong boundary-coherence route reaches the automorphism endpoint. -/
theorem planarAutomorphism_of_boundaryCoherence
    {F : PlanarPolynomialMap}
    (hBridge : BoundaryCoherenceBridge)
    (M : PlanarKellerCollisionModel F)
    (hCoherence : PlanarBoundaryCoherence F) :
    IsPolynomialAutomorphism F := by
  apply ExternalAssumptions.axGrothendieckA2 F
  exact
    pointMap_injective_of_collisionIdeal_eq_diagonalIdeal F
      ((obstructionIdeal_eq_bot_iff F).1
        (planarVanishing_of_boundaryCoherence hBridge M hCoherence))

/--
Planar boundary separation, together with the isolated standard geometric
inputs, yields the polynomial-automorphism conclusion.
-/
theorem planarAutomorphism_of_boundarySeparation
    {F : PlanarPolynomialMap}
    (M : PlanarKellerCollisionModel F)
    (hSeparation :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarBoundarySeparation M.diagram) :
    IsPolynomialAutomorphism F := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N :=
    M.algebraN
  apply ExternalAssumptions.axGrothendieckA2 F
  exact
    pointMap_injective_of_collisionIdeal_eq_diagonalIdeal F
      ((obstructionIdeal_eq_bot_iff F).1
        (planarVanishing_of_boundarySeparation M hSeparation))

end

end CollisionIdeals.Planar
