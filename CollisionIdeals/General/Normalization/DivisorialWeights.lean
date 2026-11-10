import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Integer weights at the same divisorial valuation ring

A DVR valuation subring of a field has its canonical integer-valued
valuation. This changes the value group, not the valuation ring or its
maximal ideal. Source-coordinate weights are the signed logarithms of
the actual coordinate values. An evaluated nonzero monomial has exactly
the exponential of its exponent weight when constants have value one.

No source-coordinate regularity, monomiality of the valuation on general
polynomials, or existence of a polynomial target reduction is assumed.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open MvPolynomial
open scoped WithZero

section DiscreteSubring

variable {N : Type*} [Field N]

/-- The normalized integer-valued valuation of the same DVR subring. -/
def discreteValuationOfSubring (V : ValuationSubring N)
    [IsDiscreteValuationRing V] : Valuation N ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal V).valuation N

/-- Normalizing the value group preserves the actual valuation ring. -/
theorem discreteValuationOfSubring_le_one_iff
    (V : ValuationSubring N) [IsDiscreteValuationRing V] (x : N) :
    discreteValuationOfSubring V x ≤ 1 ↔ x ∈ V := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one
      (A := V) (K := N) hx
    rw [← ha]
    exact a.property
  · intro hx
    exact (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one ⟨x, hx⟩

/-- The normalized valuation detects the same maximal ideal. -/
theorem discreteValuationOfSubring_coe_lt_one_iff
    (V : ValuationSubring N) [IsDiscreteValuationRing V] (x : V) :
    discreteValuationOfSubring V (x : N) < 1 ↔
      x ∈ IsLocalRing.maximalIdeal V := by
  exact (IsDiscreteValuationRing.maximalIdeal V).valuation_lt_one_iff_mem x

/-- Strict smallness agrees with the original valuation of the subring. -/
theorem discreteValuationOfSubring_lt_one_iff
    (V : ValuationSubring N) [IsDiscreteValuationRing V] (x : N) :
    discreteValuationOfSubring V x < 1 ↔ V.valuation x < 1 := by
  constructor
  · intro hx
    let a : V := ⟨x, (discreteValuationOfSubring_le_one_iff V x).mp hx.le⟩
    exact (V.valuation_lt_one_iff a).mp
      ((discreteValuationOfSubring_coe_lt_one_iff V a).mp hx)
  · intro hx
    let a : V := ⟨x, (V.valuation_le_one_iff x).mp hx.le⟩
    exact (discreteValuationOfSubring_coe_lt_one_iff V a).mpr
      ((V.valuation_lt_one_iff a).mpr hx)

/-- A uniformizer exists in the same fraction field with normalized value. -/
theorem exists_discreteValuationOfSubring_uniformizer
    (V : ValuationSubring N) [IsDiscreteValuationRing V] :
    ∃ π : N, discreteValuationOfSubring V π = WithZero.exp (-1 : ℤ) :=
  (IsDiscreteValuationRing.maximalIdeal V).valuation_exists_uniformizer N

end DiscreteSubring

section CoordinateWeights

variable {k N σ : Type*} [Field k] [Field N] [Algebra k N]

/-- Signed coordinate pole weights for an integer-valued valuation.
Nonzero source coordinates recover their exact valuation from these weights. -/
def valuationCoordinateWeights (v : Valuation N ℤᵐ⁰)
    (φ : MvPolynomial σ k →ₐ[k] N) : σ → ℤ :=
  fun i => WithZero.log (v (φ (X i)))

theorem valuationCoordinateWeights_value
    (v : Valuation N ℤᵐ⁰) (φ : MvPolynomial σ k →ₐ[k] N)
    (hφ : Function.Injective φ) (i : σ) :
    v (φ (X i)) = WithZero.exp (valuationCoordinateWeights v φ i) := by
  have hne : φ (X i) ≠ 0 := by
    intro h
    apply (X_ne_zero i : (X i : MvPolynomial σ k) ≠ 0)
    apply hφ
    simpa using h
  exact (WithZero.exp_log ((Valuation.ne_zero_iff v).mpr hne)).symm

/-- A coordinate pole is precisely a positive signed weight. -/
theorem valuationCoordinateWeights_pos_iff
    (v : Valuation N ℤᵐ⁰) (φ : MvPolynomial σ k →ₐ[k] N)
    (hφ : Function.Injective φ) (i : σ) :
    0 < valuationCoordinateWeights v φ i ↔ 1 < v (φ (X i)) := by
  rw [valuationCoordinateWeights_value v φ hφ i, ← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.symm

private theorem prod_exp_eq_exp_sum
    (s : Finset σ) (f : σ → ℤ) :
    (∏ i ∈ s, WithZero.exp (f i)) = WithZero.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, WithZero.exp_add]

/-- The actual value of a nonzero-coefficient monomial is exactly its
weight. Cancellation in sums is deliberately not replaced by equality. -/
theorem valuation_monomial_eq_exp_weight
    (v : Valuation N ℤᵐ⁰) (φ : MvPolynomial σ k →ₐ[k] N)
    (hφ : Function.Injective φ)
    (hScalar : ∀ c : k, c ≠ 0 → v (algebraMap k N c) = 1)
    (a : σ →₀ ℕ) (c : k) (hc : c ≠ 0) :
    v (φ (monomial a c)) =
      WithZero.exp (Finsupp.weight (valuationCoordinateWeights v φ) a) := by
  classical
  have hEval : φ (monomial a c) =
      algebraMap k N c * a.prod (fun i n => φ (X i) ^ n) := by
    conv_lhs => rw [MvPolynomial.aeval_unique φ, MvPolynomial.aeval_monomial]
    rfl
  rw [hEval, map_mul, hScalar c hc, one_mul]
  simp only [Finsupp.prod, map_prod, map_pow]
  calc
    (∏ i ∈ a.support, v (φ (X i)) ^ a i) =
        ∏ i ∈ a.support,
          WithZero.exp ((a i) • valuationCoordinateWeights v φ i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [valuationCoordinateWeights_value v φ hφ i, WithZero.exp_nsmul]
    _ = WithZero.exp (Finsupp.weight (valuationCoordinateWeights v φ) a) := by
      rw [prod_exp_eq_exp_sum]
      rfl

/-- Multiplying a coordinate by the appropriate power of a uniformizer
produces value one, including for negative coordinate weights. -/
theorem valuationCoordinateWeights_normalized_value
    (v : Valuation N ℤᵐ⁰) (φ : MvPolynomial σ k →ₐ[k] N)
    (hφ : Function.Injective φ) (π : N)
    (hπ : v π = WithZero.exp (-1 : ℤ)) (i : σ) :
    v (φ (X i) * π ^ valuationCoordinateWeights v φ i) = 1 := by
  rw [map_mul, map_zpow₀, valuationCoordinateWeights_value v φ hφ i, hπ,
    ← WithZero.exp_zsmul, ← WithZero.exp_add]
  simp

/-- The actual normalized coordinate in the original DVR subring, not
merely in an isomorphic valuation ring or in its fraction field. -/
def divisorialNormalizedCoordinates
    (V : ValuationSubring N) [IsDiscreteValuationRing V]
    (φ : MvPolynomial σ k →ₐ[k] N) (hφ : Function.Injective φ)
    (π : N) (hπ : discreteValuationOfSubring V π = WithZero.exp (-1 : ℤ)) :
    σ → V := fun i =>
  ⟨φ (X i) * π ^ valuationCoordinateWeights (discreteValuationOfSubring V) φ i,
    (discreteValuationOfSubring_le_one_iff V _).mp
      (valuationCoordinateWeights_normalized_value
        (discreteValuationOfSubring V) φ hφ π hπ i).le⟩

@[simp]
theorem divisorialNormalizedCoordinates_coe
    (V : ValuationSubring N) [IsDiscreteValuationRing V]
    (φ : MvPolynomial σ k →ₐ[k] N) (hφ : Function.Injective φ)
    (π : N) (hπ : discreteValuationOfSubring V π = WithZero.exp (-1 : ℤ))
    (i : σ) :
    (divisorialNormalizedCoordinates V φ hφ π hπ i : N) =
      φ (X i) * π ^ valuationCoordinateWeights (discreteValuationOfSubring V) φ i := rfl

/-- The initial coordinate tuple in the residue field of that same DVR. -/
def divisorialInitialCoordinates
    (V : ValuationSubring N) [IsDiscreteValuationRing V]
    (φ : MvPolynomial σ k →ₐ[k] N) (hφ : Function.Injective φ)
    (π : N) (hπ : discreteValuationOfSubring V π = WithZero.exp (-1 : ℤ)) :
    σ → IsLocalRing.ResidueField V := fun i =>
  IsLocalRing.residue V (divisorialNormalizedCoordinates V φ hφ π hπ i)

/-- Every normalized coordinate is a unit: its residue is nonzero even
when the original source coordinate has a pole at the supplied divisor. -/
theorem divisorialInitialCoordinates_ne_zero
    (V : ValuationSubring N) [IsDiscreteValuationRing V]
    (φ : MvPolynomial σ k →ₐ[k] N) (hφ : Function.Injective φ)
    (π : N) (hπ : discreteValuationOfSubring V π = WithZero.exp (-1 : ℤ))
    (i : σ) : divisorialInitialCoordinates V φ hφ π hπ i ≠ 0 := by
  intro hzero
  have hmem := (IsLocalRing.residue_eq_zero_iff
    (divisorialNormalizedCoordinates V φ hφ π hπ i)).mp hzero
  have hlt := (discreteValuationOfSubring_coe_lt_one_iff V
    (divisorialNormalizedCoordinates V φ hφ π hπ i)).mpr hmem
  rw [divisorialNormalizedCoordinates_coe,
    valuationCoordinateWeights_normalized_value
      (discreteValuationOfSubring V) φ hφ π hπ i] at hlt
  exact (lt_irrefl (1 : ℤᵐ⁰)) hlt

theorem divisorialNormalizedCoordinates_isUnit
    (V : ValuationSubring N) [IsDiscreteValuationRing V]
    (φ : MvPolynomial σ k →ₐ[k] N) (hφ : Function.Injective φ)
    (π : N) (hπ : discreteValuationOfSubring V π = WithZero.exp (-1 : ℤ))
    (i : σ) : IsUnit (divisorialNormalizedCoordinates V φ hφ π hπ i) :=
  (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    (divisorialInitialCoordinates_ne_zero V φ hφ π hπ i)

end CoordinateWeights

end

end CollisionIdeals
