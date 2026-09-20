import CollisionIdeals.General.Galois.RamificationIndex

/-!
# The intermediate ramification index

For a finite Galois tower of Dedekind rings, the ramification index in the
intermediate extension is `[I : I ∩ H]`. This is the local tower argument
shared by the cubic and planar normalization constructions.

The rings in this theorem must be Dedekind rings. Applying it to a
higher-dimensional normalization requires localization and comparison with
the geometric local index; that comparison is not an assumption hidden in
the theorem.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

attribute [local instance] Ideal.Quotient.field

/-- Interchanging the two subgroup coordinates preserves intersection order. -/
theorem card_subgroupOf_comm {G : Type*} [Group G] (I H : Subgroup G) :
    Nat.card (I.subgroupOf H) = Nat.card (H.subgroupOf I) := by
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The arithmetic step in the Galois tower formula, isolated from the
ramification-theoretic inputs. -/
theorem eq_inertiaQuotientIndex_of_mul_card
    {G : Type*} [Group G] [Finite G] (I H : Subgroup G) (e : ℕ)
    (he : e * Nat.card (H.subgroupOf I) = Nat.card I) :
    e = inertiaQuotientIndex I H := by
  have hpos : 0 < Nat.card (H.subgroupOf I) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos
    (he.trans (inertiaQuotientIndex_mul_card_intersection I H).symm)

section Tower

variable {R S T G : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [IsDedekindDomain R] [IsDedekindDomain S] [IsDedekindDomain T]
  [Module.Finite R T] [Module.Finite S T]
  [Module.IsTorsionFree R S] [Module.IsTorsionFree R T] [Module.IsTorsionFree S T]
  [Group G] [Finite G] [MulSemiringAction G T] [IsGaloisGroup G R T]

/-- The intermediate ramification index is the index of the intersection
of inertia with the subgroup fixing the intermediate ring. -/
theorem ramificationIdx_eq_inertiaQuotientIndex
    (H : Subgroup G) [IsGaloisGroup H S T]
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    (Q : Ideal T) [Q.IsMaximal] [Q.LiesOver P] [Q.LiesOver p]
    [Algebra.IsSeparable (R ⧸ p) (T ⧸ Q)]
    [Algebra.IsSeparable (S ⧸ P) (T ⧸ Q)] :
    Ideal.ramificationIdx (algebraMap R S) p P =
      inertiaQuotientIndex (Q.inertia G) H := by
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have hupper : Ideal.ramificationIdx (algebraMap S T) P Q =
      Nat.card (H.subgroupOf (Q.inertia G)) := by
    rw [← idealInertia_card_eq_ramificationIdx (G := H) P hP Q]
    exact card_subgroupOf_comm (Q.inertia G) H
  apply eq_inertiaQuotientIndex_of_mul_card
  rw [← hupper, idealInertia_card_eq_ramificationIdx (G := G) p hp Q]
  exact (Ideal.ramificationIdx_algebra_tower
    (Ideal.map_ne_bot_of_ne_bot hP)
    (Ideal.map_ne_bot_of_ne_bot hp)
    (Ideal.map_le_iff_le_comap.mpr (Q.over_def P).le)).symm

end Tower

end

end CollisionIdeals
