import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative

/-!
# The bivariate divided difference of one polynomial

The variables are `T = X 0` and `U = X 1`. We construct the divided
difference coefficientwise, without dividing in the polynomial ring.
Its restriction to the diagonal is the ordinary formal derivative.
-/

set_option autoImplicit false

namespace CollisionIdeals

open Polynomial

noncomputable section

universe u

variable {R : Type u} [CommRing R]

private abbrev powDD (n : ℕ) : MvPolynomial (Fin 2) R :=
  (Polynomial.powSubPowFactor (MvPolynomial.X (R := R) (0 : Fin 2)) (MvPolynomial.X 1) n).1

/-- The polynomial representing `(p(T) - p(U)) / (T - U)`. -/
def bivariateDividedDifference (p : R[X]) : MvPolynomial (Fin 2) R :=
  p.sum fun n r => MvPolynomial.C r * powDD n

theorem bivariateDividedDifference_mul_sub (p : R[X]) :
    bivariateDividedDifference p * (MvPolynomial.X 0 - MvPolynomial.X 1) =
      Polynomial.aeval (MvPolynomial.X (R := R) (0 : Fin 2)) p -
        Polynomial.aeval (MvPolynomial.X (R := R) (1 : Fin 2)) p := by
  simp only [bivariateDividedDifference, Polynomial.aeval_def, Polynomial.eval₂_eq_sum,
    Polynomial.sum, MvPolynomial.algebraMap_eq, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_assoc, ← (Polynomial.powSubPowFactor
    (MvPolynomial.X (R := R) (0 : Fin 2)) (MvPolynomial.X 1) n).2, mul_sub]

theorem bivariateDividedDifference_sub_mul (p : R[X]) :
    (MvPolynomial.X 0 - MvPolynomial.X 1) * bivariateDividedDifference p =
      Polynomial.aeval (MvPolynomial.X (R := R) (0 : Fin 2)) p -
        Polynomial.aeval (MvPolynomial.X (R := R) (1 : Fin 2)) p := by
  rw [mul_comm, bivariateDividedDifference_mul_sub]

private theorem diagonal_powDD (n : ℕ) :
    MvPolynomial.aeval (fun _ : Fin 2 => (Polynomial.X : R[X])) (powDD (R := R) n) =
      n • (Polynomial.X : R[X]) ^ (n - 1) := by
  induction n with
  | zero => simp [powDD, Polynomial.powSubPowFactor]
  | succ n ih =>
      rcases n with _ | n
      · simp [powDD, Polynomial.powSubPowFactor]
      · change MvPolynomial.aeval (fun _ : Fin 2 => (Polynomial.X : R[X]))
          (powDD (n + 1) * MvPolynomial.X 0 + MvPolynomial.X 1 ^ (n + 1)) = _
        rw [map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X, ih]
        simp only [Nat.add_sub_cancel, pow_succ]
        rw [add_nsmul, add_nsmul]
        ring

/-- On the diagonal, the divided difference is the formal derivative. -/
theorem bivariateDividedDifference_diagonal (p : R[X]) :
    MvPolynomial.aeval (fun _ : Fin 2 => (Polynomial.X : R[X]))
      (bivariateDividedDifference p) = p.derivative := by
  simp only [bivariateDividedDifference, Polynomial.derivative_apply, Polynomial.sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_mul, MvPolynomial.aeval_C, ← Polynomial.C_eq_algebraMap, diagonal_powDD,
    nsmul_eq_mul, ← Polynomial.C_eq_natCast, ← mul_assoc, ← map_mul]

private theorem powDD_totalDegree_le [Nontrivial R] (n : ℕ) :
    (powDD (R := R) n).totalDegree ≤ n - 1 := by
  induction n with
  | zero => simp [powDD, Polynomial.powSubPowFactor]
  | succ n ih =>
      rcases n with _ | n
      · simp [powDD, Polynomial.powSubPowFactor]
      · change (powDD (R := R) (n + 1) * MvPolynomial.X 0 +
          MvPolynomial.X 1 ^ (n + 1)).totalDegree ≤ n + 1
        refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
        · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
          rw [MvPolynomial.totalDegree_X]
          omega
        · rw [MvPolynomial.totalDegree_X_pow]

/-- A divided difference lowers the total-degree bound by one. This
bound uses the truncated natural subtraction, so constants are allowed. -/
theorem bivariateDividedDifference_totalDegree_le [Nontrivial R] (p : R[X]) :
    (bivariateDividedDifference p).totalDegree ≤ p.natDegree - 1 := by
  unfold bivariateDividedDifference Polynomial.sum
  apply MvPolynomial.totalDegree_finsetSum_le
  intro n hn
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (powDD_totalDegree_le (R := R) n).trans
    (Nat.sub_le_sub_right (Polynomial.le_natDegree_of_mem_supp n hn) 1)

end

end CollisionIdeals
