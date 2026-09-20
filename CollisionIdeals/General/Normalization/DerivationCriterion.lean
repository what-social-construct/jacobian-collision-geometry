import CollisionIdeals.General.Normalization.LocalUnramified
import CollisionIdeals.General.Normalization.DerivationIdeal

/-!
# Transverse derivations and local ramification index one

A derivation into a ring sends the square of an ideal into that ideal.
Consequently, if a base element in a contracted prime has derivative outside
the target prime, the ramification index is one. The local specialization
uses the existing `localRamificationIndex` and a derivation of the actual
prime localization into itself.

For a Keller frame extended to the normal-closure field, supplying that local
derivation requires proving regularity at the divisor. Field-level extension
and preservation of polynomial sheets do not supply this hypothesis at a
deleted boundary point.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

section Ideal

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k S]

/-- A transverse regular derivation prevents the extended base ideal from
lying in the square of the target ideal, hence forces ramification index one.
No choice of uniformizer or generator of the base ideal is required. -/
theorem ramificationIdx_eq_one_of_transverse_derivation
    (f : R →+* S) (p : Ideal R) (P : Ideal S)
    (d : Derivation k S S) (hmap : p.map f ≤ P)
    (x : R) (hx : x ∈ p) (htransverse : d (f x) ∉ P) :
    Ideal.ramificationIdx f p P = 1 := by
  by_contra hindex
  have hsquare : p.map f ≤ P ^ 2 :=
    (Ideal.ramificationIdx_ne_one_iff hmap).mp hindex
  exact htransverse
    (derivation_mem_ideal_of_mem_sq d P (hsquare (Ideal.mem_map_of_mem f hx)))

end Ideal

section Localization

universe u

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
  [Algebra R S] [Algebra k S]

/-- A derivation regular at the actual target prime, transverse to one base
element in that prime, forces the existing local ramification index to be one.
The regularity premise is the supplied derivation of the local ring itself. -/
theorem localRamificationIndex_eq_one_of_transverse_derivation
    (q : Ideal S) [q.IsPrime]
    (d : Derivation k (Localization.AtPrime q) (Localization.AtPrime q))
    (x : R) (hx : x ∈ q.under R)
    (htransverse : IsUnit (d (algebraMap R (Localization.AtPrime q) x))) :
    localRamificationIndex (R := R) q = 1 := by
  let A := Localization.AtPrime q
  have hmap : (q.under R).map (algebraMap R A) ≤ IsLocalRing.maximalIdeal A := by
    calc
      (q.under R).map (algebraMap R A) =
          ((q.under R).map (algebraMap R S)).map (algebraMap S A) := by
        rw [Ideal.map_map, IsScalarTower.algebraMap_eq R S A]
      _ ≤ q.map (algebraMap S A) := Ideal.map_mono Ideal.map_comap_le
      _ = IsLocalRing.maximalIdeal A := IsLocalization.AtPrime.map_eq_maximalIdeal q A
  exact ramificationIdx_eq_one_of_transverse_derivation
    (algebraMap R A) (q.under R) (IsLocalRing.maximalIdeal A) d hmap x hx
    (IsLocalRing.notMem_maximalIdeal.mpr htransverse)

/-- At a DVR prime with separable residue extension, a regular transverse
derivation supplies the unramifiedness premise used by branch purity. -/
theorem isUnramifiedAt_of_transverse_derivation
    [Algebra.EssFiniteType R S]
    (q : Ideal S) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)]
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    [Algebra.IsSeparable (q.under R).ResidueField q.ResidueField]
    (d : Derivation k (Localization.AtPrime q) (Localization.AtPrime q))
    (x : R) (hx : x ∈ q.under R)
    (htransverse : IsUnit (d (algebraMap R (Localization.AtPrime q) x))) :
    Algebra.IsUnramifiedAt R q :=
  (isUnramifiedAt_iff_localRamificationIndex_eq_one_of_residueSeparable q).mpr
    (localRamificationIndex_eq_one_of_transverse_derivation q d x hx htransverse)

end Localization

end

end CollisionIdeals
