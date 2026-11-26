import CollisionIdeals.General.ResidualCollision.BivariateDividedDifference
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Evaluating the coefficientwise divided difference -/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra B C]

/-- The existing polynomial divided difference evaluated at two elements. -/
def dividedDifferenceValue (H : Polynomial B) (x y : C) : C :=
  MvPolynomial.aeval (![x, y] : Fin 2 → C) (bivariateDividedDifference H)

theorem dividedDifferenceValue_mul_sub (H : Polynomial B) (x y : C) :
    dividedDifferenceValue H x y * (x - y) =
      Polynomial.aeval x H - Polynomial.aeval y H := by
  let φ : MvPolynomial (Fin 2) B →ₐ[B] C :=
    MvPolynomial.aeval (![x, y] : Fin 2 → C)
  have heval (i : Fin 2) :
      φ (Polynomial.aeval (MvPolynomial.X i) H) =
        Polynomial.aeval ((![x, y] : Fin 2 → C) i) H := by
    simpa only [AlgHom.comp_apply, φ, MvPolynomial.aeval_X] using
      (AlgHom.congr_fun (Polynomial.aeval_algHom φ (MvPolynomial.X i)) H).symm
  have h := congrArg φ (bivariateDividedDifference_mul_sub H)
  simpa only [map_mul, map_sub, MvPolynomial.aeval_X, heval,
    Matrix.cons_val_zero, Matrix.cons_val_one, φ, dividedDifferenceValue] using h

@[simp]
theorem dividedDifferenceValue_self (H : Polynomial B) (x : C) :
    dividedDifferenceValue H x x = Polynomial.aeval x H.derivative := by
  have hcomp : (Polynomial.aeval x).comp
      (MvPolynomial.aeval (fun _ : Fin 2 => (Polynomial.X : Polynomial B))) =
      MvPolynomial.aeval (![x, x] : Fin 2 → C) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  rw [dividedDifferenceValue, ← hcomp, AlgHom.comp_apply,
    bivariateDividedDifference_diagonal]

/-- Algebra homomorphisms transport the same evaluated divided difference. -/
theorem map_dividedDifferenceValue {D : Type*} [CommRing D] [Algebra B D]
    (φ : C →ₐ[B] D) (H : Polynomial B) (x y : C) :
    φ (dividedDifferenceValue H x y) = dividedDifferenceValue H (φ x) (φ y) := by
  have hcomp : φ.comp (MvPolynomial.aeval (![x, y] : Fin 2 → C)) =
      MvPolynomial.aeval (![φ x, φ y] : Fin 2 → D) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  exact AlgHom.congr_fun hcomp (bivariateDividedDifference H)

end

end CollisionIdeals
