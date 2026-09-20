import CollisionIdeals.General.Normalization.VisibleRamification
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# Index one and unramifiedness in the actual local ring

At a prime whose local ring is a DVR, the existing local ramification index
is one exactly when the extended base prime is the maximal ideal. With a
separable residue-field extension, this is the local unramifiedness criterion.

The result concerns the actual target localization. It needs no Galois action,
inertia comparison, or intermediate conjugate sheet. In the normalization of
a complex polynomial map, integrality supplies an algebraic residue extension
and characteristic zero supplies its separability.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

section DiscreteValuationRing

variable {B A : Type u} [CommRing B] [CommRing A] [IsDomain A]
  [Algebra B A] [IsDiscreteValuationRing A]

/-- In a DVR, index one is equality of the extended base ideal with the
maximal ideal. The second localization in Mathlib's Dedekind criterion is
removed using the fact that the elements outside the maximal ideal are units. -/
theorem ramificationIdx_eq_one_iff_map_eq_maximalIdeal
    (p : Ideal B)
    (hmap : p.map (algebraMap B A) ≤ IsLocalRing.maximalIdeal A) :
    Ideal.ramificationIdx (algebraMap B A) p (IsLocalRing.maximalIdeal A) = 1 ↔
      p.map (algebraMap B A) = IsLocalRing.maximalIdeal A := by
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let Aₘ := Localization.AtPrime m
  have hm : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  constructor
  · intro he
    have hlocal :=
      (Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hm hmap).mp he
    have hunits : m.primeCompl ≤ IsUnit.submonoid A := by
      intro x hx
      exact IsLocalRing.notMem_maximalIdeal.mp hx
    let e : A ≃ₐ[A] Aₘ := IsLocalization.atUnits A m.primeCompl hunits
    have hbij : Function.Bijective (algebraMap A Aₘ) := e.bijective
    have hmaps :
        (p.map (algebraMap B A)).map (algebraMap A Aₘ) =
          m.map (algebraMap A Aₘ) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq B A Aₘ,
        IsLocalization.AtPrime.map_eq_maximalIdeal m Aₘ]
      exact hlocal
    have hcomap := congrArg (Ideal.comap (algebraMap A Aₘ)) hmaps
    simpa only [Ideal.comap_map_of_bijective (algebraMap A Aₘ) hbij] using hcomap
  · intro h
    rw [← h]
    exact Ideal.ramificationIdx_map_self_eq_one
      (by rw [h]; exact Ideal.IsPrime.ne_top inferInstance)
      (by rw [h]; exact hm)

end DiscreteValuationRing

section LocalCriterion

variable {B T : Type u} [CommRing B] [CommRing T] [Algebra B T]
  [Algebra.EssFiniteType B T]

/-- Residue separability makes the actual local index-one condition
equivalent to unramifiedness at a DVR prime. No normality or dimension
hypothesis on the global target ring is needed once its local ring is a DVR. -/
theorem isUnramifiedAt_iff_localRamificationIndex_eq_one_of_residueSeparable
    (q : Ideal T) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)]
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    [Algebra.IsSeparable (q.under B).ResidueField q.ResidueField] :
    Algebra.IsUnramifiedAt B q ↔ localRamificationIndex (R := B) q = 1 := by
  let A := Localization.AtPrime q
  have hmap : (q.under B).map (algebraMap B A) ≤ IsLocalRing.maximalIdeal A := by
    calc
      (q.under B).map (algebraMap B A) =
          ((q.under B).map (algebraMap B T)).map (algebraMap T A) := by
        rw [Ideal.map_map, IsScalarTower.algebraMap_eq B T A]
      _ ≤ q.map (algebraMap T A) := Ideal.map_mono Ideal.map_comap_le
      _ = IsLocalRing.maximalIdeal A := IsLocalization.AtPrime.map_eq_maximalIdeal q A
  have hindex := ramificationIdx_eq_one_iff_map_eq_maximalIdeal (q.under B) hmap
  constructor
  · intro h
    exact hindex.mpr ((Algebra.isUnramifiedAt_iff_map_eq B (q.under B) q).mp h).2
  · intro he
    exact (Algebra.isUnramifiedAt_iff_map_eq B (q.under B) q).mpr
      ⟨inferInstance, hindex.mp he⟩

/-- For an integral extension in residue characteristic zero, the local
index-one criterion needs no separate residue-separability hypothesis. -/
theorem isUnramifiedAt_iff_localRamificationIndex_eq_one_of_residueCharZero
    [Algebra.IsIntegral B T]
    (q : Ideal T) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)]
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    [CharZero (q.under B).ResidueField] :
    Algebra.IsUnramifiedAt B q ↔ localRamificationIndex (R := B) q = 1 := by
  letI : Algebra.IsSeparable (q.under B).ResidueField q.ResidueField := inferInstance
  exact isUnramifiedAt_iff_localRamificationIndex_eq_one_of_residueSeparable q

end LocalCriterion

end

end CollisionIdeals
