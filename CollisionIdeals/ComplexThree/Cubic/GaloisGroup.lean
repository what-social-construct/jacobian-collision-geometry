module

public import CollisionIdeals.General.Galois.Sheets
public import CollisionIdeals.General.Galois.NormalClosure
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.GroupTheory.IndexNormal

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u v w

variable {G : Type u} [Group G] [Finite G]

/--
A nontrivial core-free subgroup of index three realizes its ambient finite
group as `S₃` through the action on its three cosets.
-/
noncomputable def Subgroup.mulEquivPermFinThreeOfCoreFreeIndexThree
    (H : Subgroup G)
    (hcore : H.normalCore = ⊥)
    (hindex : H.index = 3)
    (hne : H ≠ ⊥) :
    G ≃* Equiv.Perm (Fin 3) := by
  classical
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite H
  letI := Fintype.ofFinite (G ⧸ H)
  let sheetsEquiv : (G ⧸ H) ≃ Fin 3 :=
    Fintype.equivFinOfCardEq <| by
      rw [← Nat.card_eq_fintype_card, ← H.index_eq_card, hindex]
  let action : G →* Equiv.Perm (Fin 3) :=
    sheetsEquiv.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom G (G ⧸ H))
  have hActionInj :
      Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← H.normalCore_eq_ker]
    exact hcore
  apply MulEquiv.ofBijective action
  refine (Fintype.bijective_iff_injective_and_card action).2 ⟨?_, ?_⟩
  · exact sheetsEquiv.permCongrHom.injective.comp hActionInj
  · have hHcard : 2 ≤ Fintype.card H := by
      haveI : Nontrivial H := (H.nontrivial_iff_ne_bot).mpr hne
      exact Fintype.one_lt_card
    have hGge : 6 ≤ Fintype.card G := by
      rw [← Nat.card_eq_fintype_card, ← H.index_mul_card, hindex,
        Nat.card_eq_fintype_card]
      omega
    have hGle :
        Fintype.card G ≤
          Fintype.card (Equiv.Perm (Fin 3)) :=
      Fintype.card_le_of_injective action
        (sheetsEquiv.permCongrHom.injective.comp hActionInj)
    have htarget :
        Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Fintype.card_perm, Fintype.card_fin]
      decide
    omega

variable
    {K : Type u} [Field K]
    {L : Type v} [Field L] [Algebra K L]
    {N : Type w} [Field N] [Algebra K N]
    [FiniteDimensional K L]
    [FiniteDimensional K N]
    [IsGalois K N]

/--
A cubic intermediate field inside a finite Galois normal closure has Galois
group `S₃` when its fixing subgroup is core-free and nontrivial.

The index-three hypothesis is obtained from `[L : K] = 3`; core-freeness is
the normal-closure condition; nontriviality distinguishes the nonnormal cubic
case from a cyclic Galois cubic.
-/
noncomputable def galoisGroupEquivPermFinThree_of_coreFreeCubicEmbedding
    (ι : L →ₐ[K] N)
    (hdegree : Module.finrank K L = 3)
    (hcore : ι.fieldRange.fixingSubgroup.normalCore = ⊥)
    (hnontrivial : ι.fieldRange.fixingSubgroup ≠ ⊥) :
    (N ≃ₐ[K] N) ≃* Equiv.Perm (Fin 3) := by
  apply Subgroup.mulEquivPermFinThreeOfCoreFreeIndexThree
    ι.fieldRange.fixingSubgroup hcore
  · rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact
      (AlgEquiv.ofInjectiveField ι).toLinearEquiv.finrank_eq.symm.trans
      hdegree
  · exact hnontrivial

omit [FiniteDimensional K L] [FiniteDimensional K N] [IsGalois K N] in
/--
An actual marked normal closure of a cubic extension has Galois group
`S₃` as soon as its fixing subgroup is nontrivial.

Core-freeness is supplied by the dimension-independent
`NormalClosureData` API rather than repeated as an independent hypothesis.
-/
noncomputable def NormalClosureData.galoisGroupEquivPermFinThree
    [PerfectField K]
    (D : NormalClosureData K L N)
    (hdegree : Module.finrank K L = 3)
    (hnontrivial : D.intermediateFixingSubgroup ≠ ⊥) :
    D.galoisGroup ≃* Equiv.Perm (Fin 3) := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : Algebra.IsAlgebraic K N :=
    Algebra.IsAlgebraic.of_finite K N
  letI : Algebra.IsSeparable K N :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI : IsGalois K N := IsGalois.mk
  exact
    galoisGroupEquivPermFinThree_of_coreFreeCubicEmbedding
      D.embedding hdegree
      D.intermediateFixingSubgroup_normalCore_eq_bot
      hnontrivial

end

end CollisionIdeals
