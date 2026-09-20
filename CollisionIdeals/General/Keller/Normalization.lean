import CollisionIdeals.General.Keller.GenericFiniteness
import CollisionIdeals.General.Normalization.Finiteness
import CollisionIdeals.General.Normalization.OpenImmersion
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Finite normalization rings from the Keller condition

The finite separable function-field extension, its marked normal closure,
and both finite integral closures are derived from `IsKeller`. Quasi-finiteness
and algebraic Zariski's main theorem supply the open immersion, completing
the finite normalized cover. Étaleness is proved separately in
`General.Keller.Etale`; the divisorial ramification comparisons needed by
the later collision model remain separate.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- The abstract target coordinate map of a Keller map is injective. -/
theorem coordinateAlgHom_injective_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    Function.Injective (coordinateAlgHom F) := by
  letI := polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  exact coordinateAlgHom_injective_of_finiteDimensional F

/-- The intermediate normalization is finite for every Keller map. -/
theorem polynomialIntermediateNormalization_finite_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    IsPolynomialIntermediateNormalizationFinite F := by
  letI := polynomialSourceFunctionField_finiteDimensional_of_isKeller F hKeller
  letI := polynomialSourceFunctionField_isSeparable_of_isKeller F hKeller
  exact polynomialIntermediateNormalization_finite F

/-- The canonical normal-closure normalization is finite for every Keller map. -/
theorem polynomialCanonicalNormalClosureNormalization_finite_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    IsPolynomialFiniteNormalizationInExtension
      (F := F) (N := PolynomialCanonicalNormalClosure F) := by
  letI := polynomialCanonicalNormalClosure_isSeparable F hKeller
  exact polynomialNormalClosureNormalization_finite
    (polynomialCanonicalNormalClosureData F hKeller)

/-- Formal unramifiedness makes a Keller coordinate algebra quasi-finite. -/
theorem polynomialSource_quasiFinite_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    Algebra.QuasiFinite (PolynomialImageAlgebra F) (SourceRing k (Fin n)) := by
  letI := polynomialSource_finiteType_overImage F
  letI := polynomialSource_formallyUnramified_of_isKeller F hKeller
  infer_instance

/-- A Keller source is open in its intermediate normalization, by the
quasi-finite form of Zariski's main theorem. -/
theorem polynomialSourceToIntermediateNormalization_isOpenImmersion_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    IsPolynomialSourceToIntermediateNormalizationOpenImmersion F := by
  letI := polynomialSource_finiteType_overImage F
  letI := polynomialSource_quasiFinite_of_isKeller F hKeller
  exact intermediateToNormalization_isOpenImmersion
    (PolynomialImageAlgebra F) (SourceRing k (Fin n)) (PolynomialMapSourceFunctionField F)

/-- The canonical finite normalized cover is constructed directly from
the Keller condition. This does not yet supply the divisorial data of a
normalization diagram or a full Keller collision model. -/
def polynomialNormalizedCoverOfIsKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    PolynomialNormalizedCover (F := F) (N := PolynomialCanonicalNormalClosure F) where
  normalClosure := polynomialCanonicalNormalClosureData F hKeller
  finiteIntermediateModel := polynomialIntermediateNormalization_finite_of_isKeller F hKeller
  finiteNormalClosureModel :=
    polynomialCanonicalNormalClosureNormalization_finite_of_isKeller F hKeller
  intermediateOpen :=
    polynomialSourceToIntermediateNormalization_isOpenImmersion_of_isKeller F hKeller

end

end CollisionIdeals
