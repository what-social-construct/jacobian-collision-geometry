import CollisionIdeals.Planar.Research.MonogenicOrder
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Tate reconstruction for a monogenic order

This file records the finite trace-reduction identity attached to a power
basis.  If `alpha` generates a finite separable field extension and `J` is
the derivative of its minimal polynomial at `alpha`, then every `z` satisfies

`J * z = sum_i h_i(alpha) * Tr(z * alpha ^ i)`,

where the coefficients `h_i(alpha)` are supplied by Mathlib's `minpolyDiv`.
It also packages the resulting membership test for the trace dual of the
monogenic order.

These are unconditional algebraic identities.  They do not assert that an
arbitrary boundary principal part lies in a bounded trace stage, nor do they
construct the missing Keller-specific landing multiplier.
-/

set_option autoImplicit false

open Module Polynomial

namespace CollisionIdeals.Planar

noncomputable section

universe u v

/-- Explicit finite Tate reconstruction in a separable power basis. -/
theorem powerBasis_tate_reconstruction
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) (z : L) :
    aeval pb.gen (derivative (minpoly K pb.gen)) * z =
      ∑ i : Fin pb.dim,
        (minpolyDiv K pb.gen).coeff i *
          algebraMap K L (Algebra.trace K L (z * pb.gen ^ (i : ℕ))) := by
  classical
  let traceForm := Algebra.traceForm K L
  let nondegenerate := traceForm_nondegenerate K L
  let dual := traceForm.dualBasis nondegenerate pb.basis
  have hsum := dual.sum_repr z
  have hrepr : ∀ i : Fin pb.dim,
      dual.repr z i = Algebra.trace K L (z * pb.gen ^ (i : ℕ)) := by
    intro i
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
    simp [traceForm, Algebra.traceForm_apply]
  have hdual : ∀ i : Fin pb.dim,
      dual i = (minpolyDiv K pb.gen).coeff i /
        aeval pb.gen (derivative (minpoly K pb.gen)) := by
    intro i
    exact Module.Basis.traceDual_powerBasis_eq pb i
  have hJ : aeval pb.gen (derivative (minpoly K pb.gen)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable K pb.gen).aeval_derivative_ne_zero
      (minpoly.aeval K pb.gen)
  calc
    _ = aeval pb.gen (derivative (minpoly K pb.gen)) *
          ∑ i : Fin pb.dim, dual.repr z i • dual i := by rw [hsum]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrepr, hdual, Algebra.smul_def]
      field_simp

section IntegralGenerator

variable (B K N : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
variable [Field K] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K N] [Algebra B N] [IsScalarTower B K N]

/-- The order-theoretic Jacobian agrees with the generic minimal-polynomial
derivative after passing from an integrally closed domain to its fraction
field. -/
theorem monogenicOrderJacobian_eq_fieldJacobian
    (alpha : N) (halpha : IsIntegral B alpha) :
    monogenicOrderJacobian B N alpha =
      aeval alpha (derivative (minpoly K alpha)) := by
  rw [monogenicOrderJacobian,
    minpoly.isIntegrallyClosed_eq_field_fractions' K halpha,
    derivative_map, aeval_map_algebraMap]

variable [FiniteDimensional K N] [Algebra.IsSeparable K N]

/-- Membership in the trace dual of a monogenic order is equivalent to the
single bounded denominator condition `f'(alpha) * z ∈ B[alpha]`. -/
theorem traceDual_monogenic_iff_fieldJacobian_mul_mem
    (alpha z : N) (hprimitive : Algebra.adjoin K {alpha} = ⊤)
    (halpha : IsIntegral B alpha) :
    z ∈ Submodule.traceDual B K
        (1 : Submodule (monogenicOrder B N alpha) N) ↔
      aeval alpha (derivative (minpoly K alpha)) * z ∈
        monogenicOrder B N alpha := by
  let R := monogenicOrder B N alpha
  have hdual := traceForm_dualSubmodule_adjoin B K hprimitive halpha
  have hone : (1 : Submodule R N).restrictScalars B =
      Subalgebra.toSubmodule (Algebra.adjoin B {alpha}) := by
    ext x
    simp [R, monogenicOrder]
  change z ∈ (Algebra.traceForm K N).dualSubmodule
      ((1 : Submodule R N).restrictScalars B) ↔ _
  rw [hone, hdual]
  have hJ : aeval alpha (derivative (minpoly K alpha)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable K alpha).aeval_derivative_ne_zero
      (minpoly.aeval K alpha)
  rw [Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hJ)]
  simp only [inv_inv]
  rfl

/-- The same membership criterion stated with the Jacobian element retained
by the monogenic-order API. -/
theorem traceDual_monogenic_iff_jacobian_mul_mem
    (alpha z : N) (hprimitive : Algebra.adjoin K {alpha} = ⊤)
    (halpha : IsIntegral B alpha) :
    z ∈ Submodule.traceDual B K
        (1 : Submodule (monogenicOrder B N alpha) N) ↔
      monogenicOrderJacobian B N alpha * z ∈
        monogenicOrder B N alpha := by
  rw [monogenicOrderJacobian_eq_fieldJacobian B K N alpha halpha]
  exact traceDual_monogenic_iff_fieldJacobian_mul_mem
    B K N alpha z hprimitive halpha

end IntegralGenerator

end

end CollisionIdeals.Planar
