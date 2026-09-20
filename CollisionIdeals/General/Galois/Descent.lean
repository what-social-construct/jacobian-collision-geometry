import CollisionIdeals.General.Galois.NormalClosure

/-!
# Descent of conjugates to the marked field

The marked extension is normal precisely when every automorphism of its
normal closure sends the marked field into itself. In a genuine normal
closure this containment also makes the marked embedding surjective.

These equivalences specify the descent condition; they do not prove that
conjugate polynomial coordinates satisfy it. No separability or perfectness
assumption is needed for these normality statements.

Over a perfect base field, an element outside the marked field has a
witness in its fixing subgroup that moves it. This witness is not asserted
to be inertia at any valuation or to give a common local center.
-/

set_option autoImplicit false

namespace CollisionIdeals.NormalClosureData

noncomputable section

universe u v w

variable {K : Type u} {L : Type v} {N : Type w}
  [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]

/-- Any intermediate field containing every conjugate of the marked
extension contains the whole supplied normal closure. -/
theorem eq_top_of_conjugate_mem
    (D : NormalClosureData K L N)
    (T : IntermediateField K N)
    (hConjugate : ∀ (g : D.galoisGroup) (x : L),
      g (D.embedding x) ∈ T) :
    T = ⊤ := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : Algebra L N := D.embedding.toRingHom.toAlgebra
  letI : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq fun x => (D.embedding.commutes x).symm
  have hClosure : IntermediateField.normalClosure K L N = ⊤ := by
    letI : IsNormalClosure K L N := D.normalClosure
    exact (Algebra.IsAlgebraic.isNormalClosure_iff
      (F := K) (K := L) (L := N)).mp inferInstance |>.2
  have hle : IntermediateField.normalClosure K L N ≤ T := by
    rw [normalClosure_le_iff]
    intro f y hy
    obtain ⟨x, rfl⟩ := hy
    let g : N ≃ₐ[K] N := AlgEquiv.ofBijective (f.liftNormal N)
      (Algebra.IsAlgebraic.algHom_bijective (f.liftNormal N))
    have hg : g (D.embedding x) = f x := by
      change (f.liftNormal N) (algebraMap L N x) = f x
      exact f.liftNormal_commutes N x
    change f x ∈ T
    rw [← hg]
    exact hConjugate g x
  apply top_unique
  rw [← hClosure]
  exact hle

/-- If every conjugate of every marked element remains in the marked
field, that field already fills the supplied normal closure. -/
theorem embedding_surjective_of_conjugate_mem
    (D : NormalClosureData K L N)
    (hConjugate : ∀ (g : D.galoisGroup) (x : L),
      g (D.embedding x) ∈ D.intermediateField) :
    Function.Surjective D.embedding := by
  have hTop := D.eq_top_of_conjugate_mem D.intermediateField hConjugate
  intro y
  rw [← AlgHom.mem_fieldRange]
  change y ∈ D.intermediateField
  rw [hTop]
  trivial

/-- Descent of all marked conjugates makes the original extension normal. -/
theorem normal_of_conjugate_mem
    (D : NormalClosureData K L N)
    (hConjugate : ∀ (g : D.galoisGroup) (x : L),
      g (D.embedding x) ∈ D.intermediateField) :
    Normal K L := by
  let e : L ≃ₐ[K] N := AlgEquiv.ofBijective D.embedding
    ⟨D.embedding.injective, D.embedding_surjective_of_conjugate_mem hConjugate⟩
  exact e.transfer_normal.mpr D.normal

/-- Normality of the original extension is exactly stability of the marked
field under every normal-closure automorphism, stated elementwise. -/
theorem normal_iff_conjugate_mem
    (D : NormalClosureData K L N) :
    Normal K L ↔ ∀ (g : D.galoisGroup) (x : L),
      g (D.embedding x) ∈ D.intermediateField := by
  constructor
  · intro hNormal g x
    letI : Normal K N := D.normal
    let e : L ≃ₐ[K] D.intermediateField := AlgEquiv.ofInjectiveField D.embedding
    have hMarked : Normal K D.intermediateField := e.transfer_normal.mp hNormal
    exact (IntermediateField.normal_iff_forall_map_le'.mp hMarked g)
      ⟨D.embedding x, ⟨x, rfl⟩, rfl⟩
  · exact D.normal_of_conjugate_mem

/-- An element outside the marked field is moved by an automorphism fixing
that field pointwise. This is a field-theoretic witness, not an inertia
or residue-agreement statement. -/
theorem exists_fixingSubgroup_move_of_not_mem
    [PerfectField K] (D : NormalClosureData K L N) {z : N}
    (hz : z ∉ D.intermediateField) :
    ∃ h : D.intermediateFixingSubgroup, (h : D.galoisGroup) z ≠ z := by
  classical
  by_contra h
  apply hz
  rw [← D.fixedField_intermediateFixingSubgroup]
  rw [IntermediateField.mem_fixedField_iff]
  intro g hg
  by_contra hMoved
  exact h ⟨⟨g, hg⟩, hMoved⟩

end

end CollisionIdeals.NormalClosureData
