import CollisionIdeals.General.Normalization.LocalIndex
import CollisionIdeals.General.Normalization.DivisorialRamification

/-!
# Local geometric indices under preliminary localization

Preliminary localization of a normalization ring does not change the
geometric index at a surviving prime: the actual local rings are
canonically equivalent. This comparison makes no Dedekind assumption on
the original higher-dimensional ring.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

/-- Preliminary localization preserves the existing local-index object. -/
theorem localRamificationIndex_under_of_isLocalization
    {B T S : Type u} [CommRing B] [CommRing T] [CommRing S]
    [Algebra B T] [Algebra B S] [Algebra T S] [IsScalarTower B T S]
    (M : Submonoid T) [IsLocalization M S] (Q : Ideal S) [Q.IsPrime] :
    localRamificationIndex (R := B) (Q.under T) =
      localRamificationIndex (R := B) Q := by
  let e := (primeLocalizationEquivOfLocalization M Q).restrictScalars B
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime (Q.under T))).comap
      e = IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    ext x
    change e x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q.under T)) ↔
      x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
  have h := (Q.under B).ramificationIdx_comap_eq e
    (IsLocalRing.maximalIdeal (Localization.AtPrime (Q.under T)))
  rw [hmax] at h
  unfold localRamificationIndex
  rw [Ideal.under_under]
  exact h.symm

end

end CollisionIdeals
