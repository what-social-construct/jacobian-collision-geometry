import CollisionIdeals.General.Normalization.VisibleRamification
import CollisionIdeals.General.Galois.RamificationLocalization
import CollisionIdeals.General.Galois.RamificationTower

/-!
# Local indices in a Dedekind Galois tower

The geometric index used by the normalization diagram is computed in the
local ring. Here the Dedekind tower formula is stated for that same index,
rather than introducing a second geometric index or using global ideal
powers in a higher-dimensional ring.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

attribute [local instance] Ideal.Quotient.field

/-- The local geometric index agrees with the usual Dedekind index. -/
theorem localRamificationIndex_eq_ramificationIdx
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S]
    (p : Ideal R) (hp : p ≠ ⊥) (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    localRamificationIndex (R := R) P =
      Ideal.ramificationIdx (algebraMap R S) p P := by
  unfold localRamificationIndex
  rw [← P.over_def p]
  exact ramificationIdx_localizationAtPrime p hp P
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp P)

/-- Localizing the base of the semilocal Dedekind model preserves its
geometric index, too. -/
theorem localRamificationIndex_localizedBase
    {B S : Type u} [CommRing B] [IsDomain B] [CommRing S]
    [IsDedekindDomain S] [Algebra B S]
    (p : Ideal B) [p.IsPrime] (hp : p ≠ ⊥)
    [IsDedekindDomain (Localization.AtPrime p)]
    [Algebra (Localization.AtPrime p) S]
    [IsScalarTower B (Localization.AtPrime p) S]
    [Module.IsTorsionFree (Localization.AtPrime p) S]
    (Q : Ideal S) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime p))] :
    localRamificationIndex (R := B) Q =
      localRamificationIndex (R := Localization.AtPrime p) Q := by
  let R := Localization.AtPrime p
  let A := Localization.AtPrime Q
  let m := IsLocalRing.maximalIdeal R
  have hbase : Q.under B = p := by
    rw [← Ideal.under_under (A := B) (B := R) Q, ← Q.over_def m]
    exact IsLocalization.AtPrime.comap_maximalIdeal R p
  letI : Module.IsTorsionFree R A :=
    Module.IsTorsionFree.trans_faithfulSMul R S A
  letI : (IsLocalRing.maximalIdeal A).LiesOver m :=
    Ideal.LiesOver.trans (IsLocalRing.maximalIdeal A) Q m
  unfold localRamificationIndex
  rw [hbase, ← Q.over_def m]
  exact ramificationIdx_localizedBase p hp (IsLocalRing.maximalIdeal A)

/-- In a finite Dedekind Galois tower, the actual local index on the
intermediate sheet is `[I : I ∩ H]`. The concrete normal-closure application
must still supply its marked intermediate action and localized rings. -/
theorem localRamificationIndex_eq_inertiaQuotientIndex
    {R S T G : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsDedekindDomain R] [IsDedekindDomain S] [IsDedekindDomain T]
    [Module.Finite R T] [Module.Finite S T]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree R T] [Module.IsTorsionFree S T]
    [Group G] [Finite G] [MulSemiringAction G T] [IsGaloisGroup G R T]
    (H : Subgroup G) [IsGaloisGroup H S T]
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    (Q : Ideal T) [Q.IsMaximal] [Q.LiesOver P] [Q.LiesOver p]
    [Algebra.IsSeparable (R ⧸ p) (T ⧸ Q)]
    [Algebra.IsSeparable (S ⧸ P) (T ⧸ Q)] :
    localRamificationIndex (R := R) P =
      inertiaQuotientIndex (Q.inertia G) H := by
  rw [localRamificationIndex_eq_ramificationIdx p hp P]
  exact ramificationIdx_eq_inertiaQuotientIndex H p hp P Q

end

end CollisionIdeals
