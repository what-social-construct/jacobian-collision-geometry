import CollisionIdeals.General.Normalization.WeightedDegreeBounds
import CollisionIdeals.Planar.Research.Vanishing.PolynomialSubtraction

/-!
# The weighted budget for a single polynomial cancellation

Given sharp signed weighted degrees and an actual leading-polynomial
power relation, subtraction strictly lowers the virtual power degree.
The existing Keller-frame Jacobian identity bounds that drop by the
original weighted Jacobian defect.

Only exponent-one subtraction is assembled as a Keller-preserving
target-coordinate change. It preserves the same coordinate-image range
and strictly decreases a nonnegative integer defect. No leading relation,
valuation adapter, or generally iterable reduction is assumed to exist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

open MvPolynomial

private theorem weight_le_of_mem_support_pair_jacobian
    (w : Fin 2 → ℤ) (P Q : PlanePolynomial) (m n : ℤ)
    (hP : ∀ a ∈ P.support, Finsupp.weight w a ≤ m)
    (hQ : ∀ a ∈ Q.support, Finsupp.weight w a ≤ n)
    {a : Fin 2 →₀ ℕ}
    (ha : a ∈ (jacobianDet (![P, Q] : PlanarPolynomialMap)).support) :
    Finsupp.weight w a ≤ m + n - w 0 - w 1 := by
  classical
  rw [jacobianDet_fin_two] at ha
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha
  apply weight_le_of_mem_support_sub_int w
    (pderiv 0 P * pderiv 1 Q) (pderiv 1 P * pderiv 0 Q)
    (m + n - w 0 - w 1) ?_ ?_ ha
  · intro b hb
    have h := weight_le_of_mem_support_mul_int w
      (pderiv 0 P) (pderiv 1 Q) (m - w 0) (n - w 1)
      (fun a ha => weight_le_of_mem_support_pderiv_int w P 0 hP ha)
      (fun a ha => weight_le_of_mem_support_pderiv_int w Q 1 hQ ha) hb
    omega
  · intro b hb
    have h := weight_le_of_mem_support_mul_int w
      (pderiv 1 P) (pderiv 0 Q) (m - w 1) (n - w 0)
      (fun a ha => weight_le_of_mem_support_pderiv_int w P 1 hP ha)
      (fun a ha => weight_le_of_mem_support_pderiv_int w Q 0 hQ ha) hb
    omega

/-- An actual leading-polynomial relation yields a nonzero residual and
a finite sharp residual degree. Its drop from the virtual degree is
positive and bounded by the original weighted Jacobian defect.

The leading relation and exponent-degree balance are explicit inputs;
neither follows merely from a common residue zero. The result permits
negative coordinate weights and negative residual degree. -/
theorem exists_weighted_power_subtraction_budget
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c)
    (w : Fin 2 → ℤ) (m n : ℤ)
    (hPdeg : weightedTotalDegree' w (F 0) = (m : WithBot ℤ))
    (hQdeg : weightedTotalDegree' w (F 1) = (n : WithBot ℤ))
    (ell : ℂ) (r s : ℕ) (hr : 1 ≤ r)
    (hBalance : (r : ℤ) * n = (s : ℤ) * m)
    (hLeading : (weightedHomogeneousComponent w n (F 1)) ^ r =
      C ell * (weightedHomogeneousComponent w m (F 0)) ^ s) :
    let R : PlanePolynomial := (F 1) ^ r - C ell * (F 0) ^ s
    ∃ k : ℤ, weightedTotalDegree' w R = (k : WithBot ℤ) ∧
      0 < (r : ℤ) * n - k ∧
      (r : ℤ) * n - k ≤ m + n - w 0 - w 1 := by
  let R : PlanePolynomial := (F 1) ^ r - C ell * (F 0) ^ s
  have hPb : ∀ a ∈ (F 0).support, Finsupp.weight w a ≤ m :=
    fun a ha => weight_le_of_weightedTotalDegree'_eq_int w (F 0) hPdeg ha
  have hQb : ∀ a ∈ (F 1).support, Finsupp.weight w a ≤ n :=
    fun a ha => weight_le_of_weightedTotalDegree'_eq_int w (F 1) hQdeg ha
  have hQne := ne_zero_of_weightedTotalDegree'_eq_int w (F 1) hQdeg
  have hr0 : r ≠ 0 := by omega
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  have hJac :
      jacobianDet (![F 0, R] : PlanarPolynomialMap) =
        C (r : ℂ) * (F 1) ^ (r - 1) * C c :=
    jacobianDet_power_subtraction F c hc hJ ell r s
  have hRne : R ≠ 0 := by
    intro hzero
    have hNonzero :
        C (r : ℂ) * (F 1) ^ (r - 1) * C c ≠ (0 : PlanePolynomial) :=
      mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hrC) (pow_ne_zero _ hQne))
        (C_ne_zero.mpr hc)
    apply hNonzero
    rw [← hJac, hzero]
    simp [jacobianDet_fin_two]
  have hRbound : ∀ a ∈ R.support, Finsupp.weight w a ≤ (r : ℤ) * n := by
    intro a ha
    apply weight_le_of_mem_support_sub_int w
      ((F 1) ^ r) (C ell * (F 0) ^ s) ((r : ℤ) * n) ?_ ?_ ha
    · intro b hb
      exact weight_le_of_mem_support_pow_int w (F 1) n r hQb hb
    · intro b hb
      have h := weight_le_of_mem_support_C_mul_int w ell ((F 0) ^ s) ((s : ℤ) * m)
        (fun a ha => weight_le_of_mem_support_pow_int w (F 0) m s hPb ha) hb
      rwa [← hBalance] at h
  have hQtop :
      weightedHomogeneousComponent w ((r : ℤ) * n) ((F 1) ^ r) =
        (weightedHomogeneousComponent w n (F 1)) ^ r :=
    weightedHomogeneousComponent_pow_top_int w (F 1) n r hQb
  have hPtop :
      weightedHomogeneousComponent w ((r : ℤ) * n) (C ell * (F 0) ^ s) =
        C ell * (weightedHomogeneousComponent w m (F 0)) ^ s := by
    rw [hBalance, weightedHomogeneousComponent_C_mul,
      weightedHomogeneousComponent_pow_top_int w (F 0) m s hPb]
  have hRtop : weightedHomogeneousComponent w ((r : ℤ) * n) R = 0 := by
    change weightedHomogeneousComponent w ((r : ℤ) * n)
      ((F 1) ^ r - C ell * (F 0) ^ s) = 0
    rw [map_sub, hQtop, hPtop, hLeading, sub_self]
  have hRbot : weightedTotalDegree' w R ≠ ⊥ := by
    intro h
    exact hRne ((weightedTotalDegree'_eq_bot_iff w R).mp h)
  obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.mp hRbot
  have hRdeg : weightedTotalDegree' w R = (k : WithBot ℤ) := hk.symm
  have hDrop := weightedTotalDegree'_lt_coe_int_of_component_eq_zero
    w R ((r : ℤ) * n) hRbound hRtop
  rw [hRdeg] at hDrop
  have hklt : k < (r : ℤ) * n := WithBot.coe_lt_coe.mp hDrop
  have hRsharp : ∀ a ∈ R.support, Finsupp.weight w a ≤ k :=
    fun a ha => weight_le_of_weightedTotalDegree'_eq_int w R hRdeg ha
  have hJacBound :
      weightedTotalDegree' w (jacobianDet (![F 0, R] : PlanarPolynomialMap)) ≤
        ((m + k - w 0 - w 1 : ℤ) : WithBot ℤ) :=
    (weightedTotalDegree'_le_coe_int_iff w _ _).mpr
      (fun a ha => weight_le_of_mem_support_pair_jacobian w (F 0) R m k hPb hRsharp ha)
  have hJacDegree :
      weightedTotalDegree' w (jacobianDet (![F 0, R] : PlanarPolynomialMap)) =
        ((((r - 1 : ℕ) : ℤ) * n : ℤ) : WithBot ℤ) := by
    rw [hJac]
    have hFactor :
        C (r : ℂ) * (F 1) ^ (r - 1) * C c =
          C ((r : ℂ) * c) * (F 1) ^ (r - 1) := by
      rw [map_mul]
      ring
    rw [hFactor]
    exact weightedTotalDegree'_C_mul_int w ((r : ℂ) * c)
      (mul_ne_zero hrC hc) ((F 1) ^ (r - 1)) (((r - 1 : ℕ) : ℤ) * n)
      (weightedTotalDegree'_pow_int w (F 1) n (r - 1) hQdeg)
  rw [hJacDegree] at hJacBound
  have hNumerical : ((r - 1 : ℕ) : ℤ) * n ≤ m + k - w 0 - w 1 :=
    WithBot.coe_le_coe.mp hJacBound
  have hrCast : (r : ℤ) = ((r - 1 : ℕ) : ℤ) + 1 := by omega
  have hMul : (r : ℤ) * n = ((r - 1 : ℕ) : ℤ) * n + n := by rw [hrCast]; ring
  exact ⟨k, hRdeg, sub_pos.mpr hklt, by omega⟩

/-- A genuine target shear preserves Keller and the same image algebra.
Its new weighted defect is nonnegative and strictly smaller. This is
one proved step, not an assertion that such a step is always available. -/
theorem exists_weighted_targetSubtract_descent
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c)
    (w : Fin 2 → ℤ) (m n : ℤ)
    (hPdeg : weightedTotalDegree' w (F 0) = (m : WithBot ℤ))
    (hQdeg : weightedTotalDegree' w (F 1) = (n : WithBot ℤ))
    (ell : ℂ) (s : ℕ) (hBalance : n = (s : ℤ) * m)
    (hLeading : weightedHomogeneousComponent w n (F 1) =
      C ell * (weightedHomogeneousComponent w m (F 0)) ^ s) :
    IsPlanarKeller (targetSubtract F ell s) ∧
      (coordinateAlgHom (targetSubtract F ell s)).range = (coordinateAlgHom F).range ∧
      ∃ k : ℤ,
        weightedTotalDegree' w ((targetSubtract F ell s) 1) = (k : WithBot ℤ) ∧
        0 ≤ m + k - w 0 - w 1 ∧
        m + k - w 0 - w 1 < m + n - w 0 - w 1 := by
  refine ⟨targetSubtract_isKeller F ⟨c, hc, hJ⟩ ell s,
    coordinateAlgHom_targetSubtract_range F ell s, ?_⟩
  obtain ⟨k, hk, hPositive, hCap⟩ := exists_weighted_power_subtraction_budget
    F c hc hJ w m n hPdeg hQdeg ell 1 s (by decide)
    (by simpa only [Nat.cast_one, one_mul] using hBalance)
    (by simpa only [pow_one] using hLeading)
  simp only [Nat.cast_one, one_mul] at hPositive hCap
  refine ⟨k, ?_, by omega, by omega⟩
  simpa only [targetSubtract, Matrix.cons_val_one, pow_one] using hk

end

end CollisionIdeals.Planar
