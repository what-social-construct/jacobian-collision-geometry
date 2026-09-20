import CollisionIdeals.General.Galois.ValuationInertia
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Inertia and prime localization

The kernel of the residue-field action is the inertia subgroup of the
maximal ideal. Equivariant localization at a prime does not change inertia.
These comparisons do not require a discrete valuation or a characteristic
assumption; those enter the separate ramification-index calculation.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

section LocalRing

variable {G R : Type*} [Group G] [CommRing R] [IsLocalRing R]
variable [MulSemiringAction G R]

/-- Trivial residue action is precisely pointwise congruence modulo the
maximal ideal. -/
theorem residueActionKernel_eq_inertia :
    (MulSemiringAction.toRingAut G (IsLocalRing.ResidueField R)).ker =
      (IsLocalRing.maximalIdeal R).inertia G := by
  ext g
  change MulSemiringAction.toRingAut G (IsLocalRing.ResidueField R) g = 1 ↔
    ∀ x : R, g • x - x ∈ IsLocalRing.maximalIdeal R
  constructor
  · intro hg x
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub,
      IsLocalRing.ResidueField.residue_smul]
    exact sub_eq_zero.mpr (DFunLike.congr_fun hg (IsLocalRing.residue R x))
  · intro hg
    apply RingEquiv.ext
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    have hr := (IsLocalRing.residue_eq_zero_iff _).mpr (hg r)
    rw [map_sub, IsLocalRing.ResidueField.residue_smul, sub_eq_zero] at hr
    exact hr

end LocalRing

section Localization

variable {G R S : Type*} [Group G] [CommRing R] [CommRing S]
variable [Algebra R S]
variable [MulSemiringAction G R] [MulSemiringAction G S]

/-- Inertia is unchanged by equivariant localization. No primality or
locality is needed: equality of the two maps to the quotient can be
checked on the original ring by the localization universal property. -/
theorem inertia_eq_of_equivariant_localization
    (M : Submonoid R) [IsLocalization M S] (Q : Ideal S)
    (hmap : ∀ (g : G) (r : R), algebraMap R S (g • r) = g • algebraMap R S r) :
    Q.inertia G = (Q.comap (algebraMap R S)).inertia G := by
  ext g
  change (∀ x : S, g • x - x ∈ Q) ↔
    ∀ r : R, algebraMap R S (g • r - r) ∈ Q
  constructor
  · intro hg r
    rw [map_sub, hmap]
    exact hg _
  · intro hg
    have heq : (Ideal.Quotient.mk Q).comp
        (MulSemiringAction.toRingAut G S g).toRingHom = Ideal.Quotient.mk Q := by
      apply IsLocalization.ringHom_ext M
      ext r
      have hr := hg r
      rw [map_sub, hmap] at hr
      have h := (Ideal.Quotient.eq_zero_iff_mem).mpr hr
      simpa only [map_sub, sub_eq_zero] using h
    intro x
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    rw [map_sub]
    exact sub_eq_zero.mpr (DFunLike.congr_fun heq x)

variable (p : Ideal R) [p.IsPrime]
variable [IsLocalization.AtPrime S p] [IsLocalRing S]

/-- Inertia is unchanged by prime localization, provided the group actions
commute with the localization map. -/
theorem inertia_eq_of_equivariant_primeLocalization
    (hmap : ∀ (g : G) (r : R), algebraMap R S (g • r) = g • algebraMap R S r) :
    (IsLocalRing.maximalIdeal S).inertia G = p.inertia G := by
  rw [inertia_eq_of_equivariant_localization p.primeCompl _ hmap,
    IsLocalization.AtPrime.comap_maximalIdeal S p]

end Localization

section Valuation

variable (K : Type*) [Field K] {N : Type*} [Field N] [Algebra K N]

/-- The valuation inertia kernel is the maximal-ideal inertia subgroup for
the decomposition-group action on the valuation ring. -/
theorem valuationInertia_eq_maximalIdealInertia (A : ValuationSubring N) :
    A.inertiaSubgroup K =
      (IsLocalRing.maximalIdeal A).inertia (A.decompositionSubgroup K) :=
  residueActionKernel_eq_inertia

variable {R : Type*} [CommRing R] [Algebra R N]
variable (p : Ideal R) [p.IsPrime] (A : ValuationSubring N)
variable [Algebra R A] [IsScalarTower R A N] [IsLocalization.AtPrime A p]
variable [MulSemiringAction (N ≃ₐ[K] N) R]

private theorem idealInertia_preserves_localValuation
    (hmap : ∀ (g : N ≃ₐ[K] N) (r : R),
      algebraMap R N (g • r) = g (algebraMap R N r))
    (g : N ≃ₐ[K] N) (hg : g ∈ p.inertia (N ≃ₐ[K] N)) (x : A) :
    g (x : N) ∈ A := by
  let f : R →+* A := (algebraMap R A).comp
    (MulSemiringAction.toRingAut (N ≃ₐ[K] N) R g).toRingHom
  have hf : ∀ s : p.primeCompl, IsUnit (f s) := by
    intro s
    apply (IsLocalization.AtPrime.isUnit_to_map_iff A p (g • (s : R))).mpr
    intro hs
    have hd : g • (s : R) - (s : R) ∈ p := hg s
    exact s.property (by simpa only [sub_sub_cancel] using p.sub_mem hs hd)
  let φ : A →+* A := IsLocalization.lift hf
  have ht (r : R) : ((algebraMap R A r : A) : N) = algebraMap R N r :=
    (IsScalarTower.algebraMap_apply R A N r).symm
  have heq : A.subtype.comp φ = g.toRingHom.comp A.subtype := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    change ((IsLocalization.lift hf (algebraMap R A r) : A) : N) =
      g ((algebraMap R A r : A) : N)
    rw [IsLocalization.lift_eq]
    change ((algebraMap R A (g • r) : A) : N) =
      g ((algebraMap R A r : A) : N)
    rw [ht, ht, hmap]
  have hx := DFunLike.congr_fun heq x
  change (φ x : N) = g (x : N) at hx
  rw [← hx]
  exact (φ x).property

open scoped Pointwise in
/-- Ideal inertia stabilizes the associated local valuation ring. This
supplies the containment needed to compare the two ambient subgroups. -/
theorem idealInertia_le_decompositionGroupAt
    (hmap : ∀ (g : N ≃ₐ[K] N) (r : R),
      algebraMap R N (g • r) = g (algebraMap R N r)) :
    p.inertia (N ≃ₐ[K] N) ≤ decompositionGroupAt K A := by
  intro g hg
  change g • A = A
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists g x A).mp hx
    exact idealInertia_preserves_localValuation K p A hmap g hg ⟨y, hy⟩
  · intro x hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    exact idealInertia_preserves_localValuation K p A hmap g⁻¹
      ((p.inertia (N ≃ₐ[K] N)).inv_mem hg) ⟨x, hx⟩

/-- For a valuation ring realized as a prime localization of an equivariant
ring in the field, valuation inertia equals ideal inertia in the full
field-automorphism group. -/
theorem inertiaGroupAt_eq_idealInertia_of_primeLocalization
    (hmap : ∀ (g : N ≃ₐ[K] N) (r : R),
      algebraMap R N (g • r) = g (algebraMap R N r)) :
    inertiaGroupAt K A = p.inertia (N ≃ₐ[K] N) := by
  have hlocal : A.inertiaSubgroup K =
      p.inertia (decompositionGroupAt K A) := by
    rw [valuationInertia_eq_maximalIdealInertia]
    apply inertia_eq_of_equivariant_primeLocalization
    intro g r
    apply Subtype.ext
    change ((algebraMap R A ((g : N ≃ₐ[K] N) • r) : A) : N) =
      (g : N ≃ₐ[K] N) ((algebraMap R A r : A) : N)
    have ht (s : R) : ((algebraMap R A s : A) : N) = algebraMap R N s :=
      (IsScalarTower.algebraMap_apply R A N s).symm
    rw [ht, ht]
    exact hmap g r
  unfold inertiaGroupAt
  rw [hlocal]
  change ((p.inertia (N ≃ₐ[K] N)).subgroupOf
    (decompositionGroupAt K A)).map (decompositionGroupAt K A).subtype = _
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
  exact idealInertia_le_decompositionGroupAt K p A hmap

end Valuation

end

end CollisionIdeals
