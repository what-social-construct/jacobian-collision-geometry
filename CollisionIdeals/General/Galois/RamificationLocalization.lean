import CollisionIdeals.General.Galois.RamificationIndex

/-!
# Ramification indices and prime localization

Localizing the target of a Dedekind extension preserves its ramification
index. This bridges the Dedekind tower formula to an index in the actual
local ring; it is not a statement about global powers in arbitrary normal
higher-dimensional rings.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/-- In a Dedekind extension, passage to the target's local ring preserves
the ramification index. -/
theorem ramificationIdx_localizationAtPrime
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S]
    (p : Ideal R) (hp : p ≠ ⊥) (P : Ideal S) [P.IsPrime] (hP : P ≠ ⊥) :
    Ideal.ramificationIdx (algebraMap R (Localization.AtPrime P)) p
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)) =
      Ideal.ramificationIdx (algebraMap R S) p P := by
  let A := Localization.AtPrime P
  have hmapP : P.map (algebraMap S A) = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P A
  have hPmap : P.map (algebraMap S A) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (IsLocalization.injective A P.primeCompl_le_nonZeroDivisors)).not.mpr hP
  have hpmap : p.map (algebraMap R A) ≠ ⊥ := by
    rw [IsScalarTower.algebraMap_eq R S A, ← Ideal.map_map]
    exact (Ideal.map_eq_bot_iff_of_injective
      (IsLocalization.injective A P.primeCompl_le_nonZeroDivisors)).not.mpr
        (Ideal.map_ne_bot_of_ne_bot hp)
  have he : Ideal.ramificationIdx (algebraMap S A) P
      (IsLocalRing.maximalIdeal A) = 1 := by
    rw [← hmapP]
    exact Ideal.ramificationIdx_map_self_eq_one
      (by rw [hmapP]; exact Ideal.IsPrime.ne_top inferInstance) hPmap
  have ht := Ideal.ramificationIdx_algebra_tower
    (p := p) (P := P) (Q := IsLocalRing.maximalIdeal A)
    hPmap hpmap hmapP.le
  simpa only [he, mul_one] using ht

/-- Localizing the base at the contracted prime does not change the
ramification index in a Dedekind target. -/
theorem ramificationIdx_localizedBase
    {B A : Type*} [CommRing B] [IsDomain B] [CommRing A]
    [IsDedekindDomain A] [Algebra B A]
    (p : Ideal B) [p.IsPrime] (hp : p ≠ ⊥)
    [IsDedekindDomain (Localization.AtPrime p)]
    [Algebra (Localization.AtPrime p) A]
    [IsScalarTower B (Localization.AtPrime p) A]
    [Module.IsTorsionFree (Localization.AtPrime p) A]
    (Q : Ideal A) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime p))] :
    Ideal.ramificationIdx (algebraMap B A) p Q =
      Ideal.ramificationIdx (algebraMap (Localization.AtPrime p) A)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) Q := by
  let R := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal R
  have hmap : p.map (algebraMap B R) = m :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p R
  have hm : m ≠ ⊥ := by
    rw [← hmap]
    exact (Ideal.map_eq_bot_iff_of_injective
      (IsLocalization.injective R p.primeCompl_le_nonZeroDivisors)).not.mpr hp
  have he : Ideal.ramificationIdx (algebraMap B R) p m = 1 := by
    rw [← hmap]
    exact Ideal.ramificationIdx_map_self_eq_one
      (by rw [hmap]; exact Ideal.IsPrime.ne_top inferInstance) (hmap ▸ hm)
  have hpmap : p.map (algebraMap B A) ≠ ⊥ := by
    rw [IsScalarTower.algebraMap_eq B R A, ← Ideal.map_map, hmap]
    exact Ideal.map_ne_bot_of_ne_bot hm
  have ht := Ideal.ramificationIdx_algebra_tower
    (p := p) (P := m) (Q := Q) (Ideal.map_ne_bot_of_ne_bot hm) hpmap
    (Ideal.map_le_iff_le_comap.mpr (Q.over_def m).le)
  simpa only [he, one_mul] using ht

end

end CollisionIdeals
