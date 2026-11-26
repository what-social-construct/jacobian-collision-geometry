import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.PowerBasis

/-!
# A minimal-polynomial derivative test for degree one

In characteristic zero, if the derivative of the minimal polynomial of
an integral element evaluates into the base field, that element already
belongs to the base field. For a primitive element this forces extension
degree one. The proof uses minimality and the strict derivative degree
drop, and does not infer the required descent from separability.

This elementary test isolates the field step behind the localized
one-generator argument in Moskowicz, arXiv:1606.00426v2, Theorem 3.1.
No theorem from that source is assumed. In positive characteristic an
Artin--Schreier polynomial can have constant derivative and degree p,
so characteristic zero is essential.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open Polynomial

universe u v

variable {K : Type u} {L : Type v}
variable [Field K] [CharZero K] [Field L] [Algebra K L]

/-- Descent of the evaluated minimal-polynomial derivative forces an
integral element to have degree one in characteristic zero. -/
theorem minpoly_natDegree_eq_one_of_derivative_aeval_mem_range
    (a : L) (ha : IsIntegral K a)
    (hDerivative : aeval a (minpoly K a).derivative ∈ Set.range (algebraMap K L)) :
    (minpoly K a).natDegree = 1 := by
  obtain ⟨c, hc⟩ := hDerivative
  have hpos := minpoly.natDegree_pos ha
  have hzero : aeval a ((minpoly K a).derivative - C c) = 0 := by
    simp only [map_sub, aeval_C, hc, sub_self]
  have hlt : ((minpoly K a).derivative - C c).natDegree < (minpoly K a).natDegree :=
    (natDegree_sub_le _ _).trans_lt (max_lt
      (natDegree_derivative_lt (Nat.ne_of_gt hpos)) (by simpa using hpos))
  have hpoly : (minpoly K a).derivative = C c :=
    sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt (minpoly.dvd K a hzero) hlt)
  have hdegree : (minpoly K a).derivative.natDegree = (minpoly K a).natDegree - 1 :=
    natDegree_eq_of_degree_eq_some (degree_derivative_eq _ hpos)
  rw [hpoly, natDegree_C] at hdegree
  exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hdegree.symm)
    (Nat.succ_le_of_lt hpos)

/-- The same derivative test descends the element itself. -/
theorem mem_range_of_minpoly_derivative_aeval_mem_range
    (a : L) (ha : IsIntegral K a)
    (hDerivative : aeval a (minpoly K a).derivative ∈ Set.range (algebraMap K L)) :
    a ∈ Set.range (algebraMap K L) :=
  minpoly.natDegree_eq_one_iff.mp
    (minpoly_natDegree_eq_one_of_derivative_aeval_mem_range a ha hDerivative)

/-- For a primitive element, derivative descent forces the entire
extension to have degree one. -/
theorem finrank_eq_one_of_powerBasis_minpoly_derivative_aeval_mem_range
    (pb : PowerBasis K L)
    (hDerivative : aeval pb.gen (minpoly K pb.gen).derivative ∈
      Set.range (algebraMap K L)) :
    Module.finrank K L = 1 := by
  rw [pb.finrank, ← pb.natDegree_minpoly]
  exact minpoly_natDegree_eq_one_of_derivative_aeval_mem_range
    pb.gen pb.isIntegral_gen hDerivative

end

end CollisionIdeals
