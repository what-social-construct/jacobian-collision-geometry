import CollisionIdeals.General.Keller.Interfaces
import CollisionIdeals.General.Normalization.VisibleRamification

/-!
# Collision-normalization models for Keller maps

This is the dimension-independent package used before any
dimension-specific hidden-inertia rigidity theorem.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k]
variable {n : ℕ}

/--
The collision/normalization model for one polynomial Keller map.

It packages the Keller certificate, finite normalization diagram,
Keller-to-étale and Keller-to-flat bridges, and the realization of
double-coset inertia indices as geometric ramification indices.  It does
not contain a no-hidden-inertia assertion.
-/
structure PolynomialKellerCollisionModel
    (F : PolynomialSelfMap k n) where
  keller : IsKeller F
  N : Type u
  fieldN : Field N
  algebraN : Algebra (PolynomialMapBaseFunctionField F) N
  diagram :
    letI : Field N := fieldN
    letI : Algebra (PolynomialMapBaseFunctionField F) N := algebraN
    PolynomialNormalizationDiagram (F := F) (N := N)
  kellerEtale : KellerEtaleBridge F
  kellerFlat : KellerFlatBridge F
  ramificationRealization :
    letI : Field N := fieldN
    letI : Algebra (PolynomialMapBaseFunctionField F) N := algebraN
    diagram.ConjugateRamificationRealization

namespace PolynomialKellerCollisionModel

variable {F : PolynomialSelfMap k n}

/--
Assemble a Keller collision model from a supplied normalization diagram and
its ramification realization.  Flatness is derived from the étale bridge;
this constructor does not assert existence of the normal closure or of the
normalization data.
-/
noncomputable def ofNormalizationDiagram
    (hKeller : IsKeller F)
    {N : Type u} [Field N]
    [Algebra (PolynomialMapBaseFunctionField F) N]
    (diagram : PolynomialNormalizationDiagram (F := F) (N := N))
    (kellerEtale : KellerEtaleBridge F)
    (ramificationRealization :
      diagram.ConjugateRamificationRealization) :
    PolynomialKellerCollisionModel F where
  keller := hKeller
  N := N
  fieldN := inferInstance
  algebraN := inferInstance
  diagram := diagram
  kellerEtale := kellerEtale
  kellerFlat :=
    KellerEtaleBridge.toKellerFlatBridge F kellerEtale
  ramificationRealization := ramificationRealization

/--
For a Keller collision model, every conjugate center with nontrivial
relative inertia lies in the deleted normalization boundary.
-/
theorem ramifiedConjugateCentersInBoundary_of_keller
    (M : PolynomialKellerCollisionModel F) :
    letI : Field M.N := M.fieldN
    letI : Algebra (PolynomialMapBaseFunctionField F) M.N := M.algebraN
    M.diagram.RamifiedConjugateCentersInBoundary := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PolynomialMapBaseFunctionField F) M.N := M.algebraN
  exact
    M.diagram.ramifiedConjugateCentersInBoundary
      M.ramificationRealization
      (M.kellerEtale M.keller)

/--
An actual ramified height-one point in a Keller collision model produces
a hidden-inertia orbit.

Core-freeness of the marked normal closure moves some conjugate sheet,
while the Keller étale bridge places every center with nontrivial relative
inertia in the deleted boundary.
-/
theorem hasHiddenInertiaOrbit_of_ramifiedCodimensionOnePoint
    [PerfectField (PolynomialMapBaseFunctionField F)]
    (M : PolynomialKellerCollisionModel F)
    (E :
      letI : Field M.N := M.fieldN
      letI : Algebra (PolynomialMapBaseFunctionField F) M.N :=
        M.algebraN
      PolynomialRamifiedCodimensionOnePoint
        (F := F) (N := M.N)) :
    letI : Field M.N := M.fieldN
    letI : Algebra (PolynomialMapBaseFunctionField F) M.N :=
      M.algebraN
    M.diagram.HasHiddenInertiaOrbit := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PolynomialMapBaseFunctionField F) M.N :=
    M.algebraN
  exact
    ⟨E, M.diagram.exists_one_lt_inertiaIndex E,
      (M.ramifiedConjugateCentersInBoundary_of_keller) E⟩

end PolynomialKellerCollisionModel

end

end CollisionIdeals
