import Mathlib.RingTheory.Valuation.ValuationSubring
import CollisionIdeals.General.Normalization.DivisorialWeights
import CollisionIdeals.General.Normalization.WeightedDegreeBounds

/-!
# Initial residue cancellation for an actual valuation

If a finite sum is regular but some terms have a larger maximal value,
the sum of all maximal-value terms has strictly smaller value. Dividing
that top part by a term of maximal value produces an element of the
actual valuation ring with zero residue.

This is cancellation after evaluation. It does not assert a polynomial
identity between weighted leading forms, monomiality of the valuation,
or regularity of the original coordinate generators.
-/

set_option autoImplicit false

namespace CollisionIdeals

variable {R Γ₀ ι : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]

/-- The top-valued part of a finite sum has strictly smaller value if
the entire sum does. The filter collects every term at the bound, not
only a chosen pair of equal-value terms. -/
theorem valuation_sum_maximal_terms_lt
    (v : Valuation R Γ₀) (s : Finset ι) (f : ι → R) (γ : Γ₀)
    (hγ : γ ≠ 0) (hsum : v (∑ i ∈ s, f i) < γ)
    (hbound : ∀ i ∈ s, v (f i) ≤ γ) :
    v (∑ i ∈ s with v (f i) = γ, f i) < γ := by
  classical
  have hlower : v (∑ i ∈ s with ¬v (f i) = γ, f i) < γ := by
    apply v.map_sum_lt hγ
    intro i hi
    obtain ⟨his, hine⟩ := Finset.mem_filter.mp hi
    exact lt_of_le_of_ne (hbound i his) hine
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => v (f i) = γ) f
  have htop :
      (∑ i ∈ s with v (f i) = γ, f i) =
        (∑ i ∈ s, f i) - (∑ i ∈ s with ¬v (f i) = γ, f i) := by
    rw [← hsplit]
    exact (add_sub_cancel_right _ _).symm
  rw [htop]
  exact v.map_sub_lt hsum hlower

variable {N : Type*} [Field N]

/-- A regular finite sum with a polar maximal term yields an actual
valuation-ring element: divide the whole maximal-value part by a term
of that value. The quotient lies in the maximal ideal, hence has zero
residue. Neither a uniformizer nor a residue-field lift is required. -/
theorem exists_normalized_maximal_sum_residue_zero
    (V : ValuationSubring N) (s : Finset ι) (f : ι → N) (t : N)
    (hsum : V.valuation (∑ i ∈ s, f i) ≤ 1)
    (hpolar : 1 < V.valuation t)
    (hbound : ∀ i ∈ s, V.valuation (f i) ≤ V.valuation t) :
    ∃ z : V,
      (z : N) = (∑ i ∈ s with V.valuation (f i) = V.valuation t, f i) / t ∧
      IsLocalRing.residue V z = 0 := by
  classical
  have htpos : 0 < V.valuation t := lt_trans zero_lt_one hpolar
  have htop := valuation_sum_maximal_terms_lt V.valuation s f (V.valuation t)
    (ne_of_gt htpos) (lt_of_le_of_lt hsum hpolar) hbound
  have hquot :
      V.valuation ((∑ i ∈ s with V.valuation (f i) = V.valuation t, f i) / t) < 1 := by
    rw [V.valuation.map_div]
    exact (div_lt_one₀ htpos).mpr htop
  let z : V :=
    ⟨(∑ i ∈ s with V.valuation (f i) = V.valuation t, f i) / t,
      (V.valuation_le_one_iff _).mp hquot.le⟩
  refine ⟨z, rfl, ?_⟩
  apply (IsLocalRing.residue_eq_zero_iff z).mpr
  exact (V.valuation_lt_one_iff z).mpr hquot

section WeightedComponent

open MvPolynomial
open scoped WithZero

variable {k σ : Type*} [Field k] [Algebra k N]

/-- For the actual coordinate weights of an integer-valued valuation,
the top weighted component of a regular polynomial loses value after
evaluation whenever its sharp weighted degree is positive. This is a
strict valuation inequality, not vanishing of that component in the
source polynomial ring. -/
theorem valuation_weightedHomogeneousComponent_lt_exp_degree
    (v : Valuation N ℤᵐ⁰) (φ : MvPolynomial σ k →ₐ[k] N)
    (hφ : Function.Injective φ)
    (hScalar : ∀ c : k, c ≠ 0 → v (algebraMap k N c) = 1)
    (P : MvPolynomial σ k) (m : ℤ)
    (hdeg : weightedTotalDegree' (valuationCoordinateWeights v φ) P =
      (m : WithBot ℤ))
    (hm : 0 < m) (hRegular : v (φ P) ≤ 1) :
    v (φ (weightedHomogeneousComponent (valuationCoordinateWeights v φ) m P)) <
      WithZero.exp m := by
  classical
  have hpolar : (1 : ℤᵐ⁰) < WithZero.exp m := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr hm
  have hsum : v (∑ a ∈ P.support, φ (monomial a (coeff a P))) < WithZero.exp m := by
    rw [← map_sum, support_sum_monomial_coeff]
    exact lt_of_le_of_lt hRegular hpolar
  have hbound : ∀ a ∈ P.support,
      v (φ (monomial a (coeff a P))) ≤ WithZero.exp m := by
    intro a ha
    rw [valuation_monomial_eq_exp_weight v φ hφ hScalar a (coeff a P)
      (mem_support_iff.mp ha)]
    exact WithZero.exp_le_exp.mpr
      (weight_le_of_weightedTotalDegree'_eq_int (valuationCoordinateWeights v φ) P hdeg ha)
  have htop := valuation_sum_maximal_terms_lt v P.support
    (fun a => φ (monomial a (coeff a P))) (WithZero.exp m)
    WithZero.exp_ne_zero hsum hbound
  have hfilter :
      P.support.filter (fun a => v (φ (monomial a (coeff a P))) = WithZero.exp m) =
        P.support.filter (fun a => Finsupp.weight (valuationCoordinateWeights v φ) a = m) := by
    apply Finset.filter_congr
    intro a ha
    rw [valuation_monomial_eq_exp_weight v φ hφ hScalar a (coeff a P)
      (mem_support_iff.mp ha), WithZero.exp_inj]
  rw [hfilter] at htop
  rw [weightedHomogeneousComponent_apply, map_sum]
  exact htop

/-- The weighted top-part inequality produces a zero residue in the
same DVR subring. A denominator of top value normalizes the evaluated
component; no source-coordinate regularity is required. -/
theorem exists_normalized_weightedComponent_residue_zero
    (V : ValuationSubring N) [IsDiscreteValuationRing V]
    (φ : MvPolynomial σ k →ₐ[k] N) (hφ : Function.Injective φ)
    (hScalar : ∀ c : k, c ≠ 0 →
      discreteValuationOfSubring V (algebraMap k N c) = 1)
    (P : MvPolynomial σ k) (m : ℤ)
    (hdeg : weightedTotalDegree'
      (valuationCoordinateWeights (discreteValuationOfSubring V) φ) P =
        (m : WithBot ℤ))
    (hm : 0 < m) (hRegular : discreteValuationOfSubring V (φ P) ≤ 1)
    (t : N) (ht : discreteValuationOfSubring V t = WithZero.exp m) :
    ∃ z : V,
      (z : N) = φ (weightedHomogeneousComponent
        (valuationCoordinateWeights (discreteValuationOfSubring V) φ) m P) / t ∧
      IsLocalRing.residue V z = 0 := by
  have htop := valuation_weightedHomogeneousComponent_lt_exp_degree
    (discreteValuationOfSubring V) φ hφ hScalar P m hdeg hm hRegular
  have hquot : discreteValuationOfSubring V
      (φ (weightedHomogeneousComponent
        (valuationCoordinateWeights (discreteValuationOfSubring V) φ) m P) / t) < 1 := by
    rw [Valuation.map_div, ht]
    exact (div_lt_one₀ WithZero.exp_pos).mpr htop
  have hquotV := (discreteValuationOfSubring_lt_one_iff V _).mp hquot
  let z : V :=
    ⟨φ (weightedHomogeneousComponent
      (valuationCoordinateWeights (discreteValuationOfSubring V) φ) m P) / t,
      (V.valuation_le_one_iff _).mp hquotV.le⟩
  refine ⟨z, rfl, ?_⟩
  exact (IsLocalRing.residue_eq_zero_iff z).mpr
    ((V.valuation_lt_one_iff z).mpr hquotV)

end WeightedComponent

end CollisionIdeals
