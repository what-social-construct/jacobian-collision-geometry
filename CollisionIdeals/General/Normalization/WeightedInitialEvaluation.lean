import CollisionIdeals.General.Normalization.ValuationInitialResidue

/-!
# Evaluating weighted initial forms at a divisorial residue tuple

Signed weighted homogeneity identifies evaluation at the normalized
coordinates with multiplication by the matching power of a uniformizer.
Reduction takes place in the residue field of the same DVR subring.
Consequently the positive-degree initial form of a regular output
vanishes at its actual nonzero initial-coordinate tuple.

This is an evaluated residue equation, not a polynomial identity between
two initial forms and not an existence theorem for a target shear.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open MvPolynomial
open scoped WithZero

variable {k N σ : Type*} [Field k] [Field N] [Algebra k N]

private theorem prod_zpow_eq_zpow_sum
    (π : N) (hπ : π ≠ 0) (s : Finset σ) (f : σ → ℤ) :
    (∏ i ∈ s, π ^ f i) = π ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ hπ]

private theorem aeval_scaled_monomial_int
    (w : σ → ℤ) (x : σ → N) (π : N) (hπ : π ≠ 0)
    (a : σ →₀ ℕ) (c : k) :
    aeval (fun i => x i * π ^ w i) (monomial a c) =
      aeval x (monomial a c) * π ^ Finsupp.weight w a := by
  classical
  have hprod : (∏ i ∈ a.support, (π ^ w i) ^ a i) =
      π ^ Finsupp.weight w a := by
    calc
      _ = ∏ i ∈ a.support, π ^ ((a i : ℤ) * w i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [← zpow_natCast, ← zpow_mul, Int.mul_comm]
      _ = π ^ (∑ i ∈ a.support, (a i : ℤ) * w i) :=
        prod_zpow_eq_zpow_sum π hπ a.support _
      _ = _ := by
        simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  rw [hprod]
  exact (mul_assoc _ _ _).symm

/-- Scaling by signed powers of a nonzero element evaluates a weighted
homogeneous polynomial by the power prescribed by its exact weight. -/
theorem aeval_weighted_scale_int
    (w : σ → ℤ) (x : σ → N) (π : N) (hπ : π ≠ 0)
    (P : MvPolynomial σ k) (m : ℤ) (hP : P.IsWeightedHomogeneous w m) :
    aeval (fun i => x i * π ^ w i) P = aeval x P * π ^ m := by
  classical
  calc
    _ = ∑ a ∈ P.support,
        aeval (fun i => x i * π ^ w i) (monomial a (coeff a P)) := by
      rw [← map_sum, support_sum_monomial_coeff]
    _ = ∑ a ∈ P.support, aeval x (monomial a (coeff a P)) * π ^ m := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [aeval_scaled_monomial_int w x π hπ a (coeff a P),
        hP (mem_support_iff.mp ha)]
    _ = _ := by
      rw [← Finset.sum_mul, ← map_sum, support_sum_monomial_coeff]

section DivisorialEvaluation

variable (V : ValuationSubring N) [IsDiscreteValuationRing V]
variable [Algebra k V] [IsScalarTower k V N]

/-- Homogeneous evaluation in the same DVR agrees, after inclusion in
the fraction field, with the actual source value times a signed power. -/
theorem divisorialNormalizedCoordinates_aeval_coe
    (φ : MvPolynomial σ k →ₐ[k] N) (hφ : Function.Injective φ)
    (π : N) (hπ : discreteValuationOfSubring V π = WithZero.exp (-1 : ℤ))
    (P : MvPolynomial σ k) (m : ℤ)
    (hP : P.IsWeightedHomogeneous
      (valuationCoordinateWeights (discreteValuationOfSubring V) φ) m) :
    ((aeval (divisorialNormalizedCoordinates V φ hφ π hπ) P : V) : N) =
      φ P * π ^ m := by
  have hπne : π ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hmap := MvPolynomial.comp_aeval_apply
    (divisorialNormalizedCoordinates V φ hφ π hπ)
    (IsScalarTower.toAlgHom k V N) P
  have hφeval : aeval (fun i => φ (X i)) P = φ P := by
    conv_rhs => rw [MvPolynomial.aeval_unique φ]
    rfl
  calc
    _ = aeval (fun i => φ (X i) *
        π ^ valuationCoordinateWeights (discreteValuationOfSubring V) φ i) P := by
      simpa only [IsScalarTower.toAlgHom_apply,
        divisorialNormalizedCoordinates_coe] using hmap
    _ = aeval (fun i => φ (X i)) P * π ^ m :=
      aeval_weighted_scale_int _ _ π hπne P m hP
    _ = _ := by rw [hφeval]

omit [IsScalarTower k V N] in
/-- Evaluation at the initial tuple is exactly reduction of evaluation
at the normalized tuple; the polynomial and coefficient field are unchanged. -/
theorem divisorialInitialCoordinates_aeval
    (φ : MvPolynomial σ k →ₐ[k] N) (hφ : Function.Injective φ)
    (π : N) (hπ : discreteValuationOfSubring V π = WithZero.exp (-1 : ℤ))
    (P : MvPolynomial σ k) :
    aeval (divisorialInitialCoordinates V φ hφ π hπ) P =
      IsLocalRing.residue V
        (aeval (divisorialNormalizedCoordinates V φ hφ π hπ) P) := by
  have hmap := MvPolynomial.comp_aeval_apply
    (divisorialNormalizedCoordinates V φ hφ π hπ)
    (IsScalarTower.toAlgHom k V (IsLocalRing.ResidueField V)) P
  simpa only [IsScalarTower.toAlgHom_apply,
    IsLocalRing.ResidueField.algebraMap_eq, divisorialInitialCoordinates] using hmap.symm

/-- The actual nonzero divisorial initial-coordinate tuple is a zero
of a regular output's positive-degree weighted initial form.

The strict valuation loss is proved from the original polynomial support;
it is not assumed as a monomial-valuation equality for the whole output. -/
theorem divisorialInitialCoordinates_weightedComponent_eq_zero
    (φ : MvPolynomial σ k →ₐ[k] N) (hφ : Function.Injective φ)
    (hScalar : ∀ c : k, c ≠ 0 →
      discreteValuationOfSubring V (algebraMap k N c) = 1)
    (π : N) (hπ : discreteValuationOfSubring V π = WithZero.exp (-1 : ℤ))
    (P : MvPolynomial σ k) (m : ℤ)
    (hdeg : weightedTotalDegree'
      (valuationCoordinateWeights (discreteValuationOfSubring V) φ) P =
        (m : WithBot ℤ))
    (hm : 0 < m) (hRegular : discreteValuationOfSubring V (φ P) ≤ 1) :
    aeval (divisorialInitialCoordinates V φ hφ π hπ)
      (weightedHomogeneousComponent
        (valuationCoordinateWeights (discreteValuationOfSubring V) φ) m P) = 0 := by
  let w := valuationCoordinateWeights (discreteValuationOfSubring V) φ
  let C := weightedHomogeneousComponent w m P
  let u := divisorialNormalizedCoordinates V φ hφ π hπ
  have htop := valuation_weightedHomogeneousComponent_lt_exp_degree
    (discreteValuationOfSubring V) φ hφ hScalar P m hdeg hm hRegular
  have hC : C.IsWeightedHomogeneous w m :=
    weightedHomogeneousComponent_isWeightedHomogeneous m P
  have heval : ((aeval u C : V) : N) = φ C * π ^ m :=
    divisorialNormalizedCoordinates_aeval_coe V φ hφ π hπ C m hC
  have hsmall : discreteValuationOfSubring V ((aeval u C : V) : N) < 1 := by
    rw [heval, map_mul, map_zpow₀, hπ]
    have hpow : WithZero.exp (-1 : ℤ) ^ m = WithZero.exp (-m) := by
      rw [← WithZero.exp_zsmul]
      simp
    rw [hpow]
    have hmul := mul_lt_mul_of_pos_right htop (WithZero.exp_pos (a := -m))
    simpa only [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero] using hmul
  rw [divisorialInitialCoordinates_aeval]
  apply (IsLocalRing.residue_eq_zero_iff _).mpr
  exact (discreteValuationOfSubring_coe_lt_one_iff V (aeval u C)).mp hsmall

end DivisorialEvaluation

end

end CollisionIdeals
