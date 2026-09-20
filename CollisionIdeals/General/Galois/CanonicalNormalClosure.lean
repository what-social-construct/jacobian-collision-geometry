import CollisionIdeals.General.Galois.NormalClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SeparableClosure

/-!
# A finite normal closure constructed in an algebraic closure

Every finite extension admits marked normal-closure data.  This realizes
the data in the normal closure inside the algebraic closure of the base;
it does not assume a separate existence input.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- The normal closure of `L/K` inside the algebraic closure of `K`. -/
abbrev CanonicalNormalClosure :=
  IntermediateField.normalClosure K L (AlgebraicClosure K)

/-- A finite field extension supplies its own marked finite normal closure. -/
def canonicalNormalClosureData [FiniteDimensional K L] :
    NormalClosureData K L (CanonicalNormalClosure K L) := by
  let φ : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  letI : Nonempty (L →ₐ[K] AlgebraicClosure K) := ⟨φ⟩
  exact
    { embedding := φ.codRestrict _ fun x =>
        φ.fieldRange_le_normalClosure ⟨x, rfl⟩
      normalClosure := inferInstance
      finiteIntermediate := inferInstance
      finiteNormal := inferInstance }

/-- The canonical normal closure of a separable extension remains separable. -/
theorem canonicalNormalClosure_isSeparable [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K (CanonicalNormalClosure K L) := by
  apply (le_separableClosure_iff K (AlgebraicClosure K) _).mp
  apply normalClosure_le_iff.mpr
  intro f
  letI : Algebra.IsSeparable K f.fieldRange :=
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
  exact le_separableClosure K (AlgebraicClosure K) f.fieldRange

/-- A finite separable extension has a canonical finite Galois closure. -/
theorem canonicalNormalClosure_isGalois [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : IsGalois K (CanonicalNormalClosure K L) := by
  letI := canonicalNormalClosure_isSeparable K L
  letI := (canonicalNormalClosureData K L).normal
  exact IsGalois.mk

end

end CollisionIdeals
