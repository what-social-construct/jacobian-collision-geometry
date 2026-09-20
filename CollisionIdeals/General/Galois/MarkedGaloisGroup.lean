import CollisionIdeals.General.Galois.NormalClosure
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
# The Galois action over a marked intermediate field

The subgroup fixing the marked copy of the intermediate field really is
the Galois group of the upper extension. This supplies the upper action
needed by the ramification tower formula; it is not an extra hypothesis
on a normal-closure witness.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/-- Conjugating the marked embedding conjugates its fixing subgroup. -/
theorem fixingSubgroup_conjugate_embedding
    {K L N : Type*} [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra K N]
    (ι : L →ₐ[K] N) (g : N ≃ₐ[K] N) :
    (g.toAlgHom.comp ι).fieldRange.fixingSubgroup =
      ι.fieldRange.fixingSubgroup.map (MulAut.conj g).toMonoidHom := by
  rw [← AlgHom.map_fieldRange]
  exact IsGalois.map_fixingSubgroup ι.fieldRange g

/-- The fixing subgroup of an embedded intermediate field is a Galois
group for the scalar structure defined by that embedding. -/
theorem fixingSubgroup_isGaloisGroup_of_embedding
    {K L N : Type*} [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
    (ι : L →ₐ[K] N) :
    letI : Algebra L N := ι.toRingHom.toAlgebra
    IsGaloisGroup ι.fieldRange.fixingSubgroup L N := by
  letI : Algebra L N := ι.toRingHom.toAlgebra
  refine ⟨inferInstance, ⟨?_⟩, ⟨?_⟩⟩
  · intro g l x
    change (g : N ≃ₐ[K] N) (ι l * x) = ι l * (g : N ≃ₐ[K] N) x
    rw [map_mul, (IntermediateField.mem_fixingSubgroup_iff
      ι.fieldRange g).mp g.property (ι l) ⟨l, rfl⟩]
  · intro x hx
    have hfixed : x ∈ IntermediateField.fixedField ι.fieldRange.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact hx ⟨g, hg⟩
    rw [IsGalois.fixedField_fixingSubgroup] at hfixed
    exact hfixed

namespace NormalClosureData

/-- The marked normal closure supplies its upper Galois action. -/
theorem intermediateFixingSubgroup_isGaloisGroup
    {K L N : Type*} [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra K N] [Algebra.IsSeparable K N]
    (D : NormalClosureData K L N) :
    letI : Algebra L N := D.embedding.toRingHom.toAlgebra
    IsGaloisGroup D.intermediateFixingSubgroup L N := by
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : IsGalois K N := IsGalois.mk
  exact fixingSubgroup_isGaloisGroup_of_embedding D.embedding

end NormalClosureData

end

end CollisionIdeals
