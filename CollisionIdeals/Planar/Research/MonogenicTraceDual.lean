import CollisionIdeals.Planar.Research.MonogenicOrder
import CollisionIdeals.Planar.Research.PrincipalPartsStrategy

/-!
# Monogenic trace dual and conductor comparison

This file packages the monogenic complementary-module formula already available through
Mathlib's `traceForm_dualSubmodule_adjoin` and proves its conductor form for an overorder.
These are unconditional algebraic identities; they do not assert the missing uniform boundary
landing statement.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

open Module
open Polynomial Algebra Pointwise Submodule

universe u v w z

section MonogenicOrder

variable (B K N : Type*) [CommRing B] [Field K] [Field N]
variable [Algebra B K] [Algebra K N] [Algebra B N] [IsScalarTower B K N]
variable [IsDomain B] [IsIntegrallyClosed B] [IsFractionRing B K]
variable [FiniteDimensional K N] [Algebra.IsSeparable K N]

omit [IsDomain B] [IsIntegrallyClosed B] in
private lemma one_restrictScalars_adjoin_eq_toSubmodule (x : N) :
    (1 : Submodule (Algebra.adjoin B {x}) N).restrictScalars B =
      Subalgebra.toSubmodule (Algebra.adjoin B {x}) := by
  ext y
  constructor
  · intro hy
    rw [Submodule.restrictScalars_mem, Submodule.mem_one] at hy
    obtain ⟨r, rfl⟩ := hy
    exact r.property
  · intro hy
    rw [Submodule.restrictScalars_mem, Submodule.mem_one]
    exact ⟨⟨y, hy⟩, rfl⟩

omit [IsDomain B] [IsIntegrallyClosed B] in
private lemma smul_one_restrictScalars_adjoin_eq_smul_toSubmodule
    (x c : N) :
    (c • (1 : Submodule (Algebra.adjoin B {x}) N)).restrictScalars B =
      c • Subalgebra.toSubmodule (Algebra.adjoin B {x}) := by
  ext y
  simp only [Submodule.restrictScalars_mem, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_one, Subalgebra.mem_toSubmodule]
  constructor
  · rintro ⟨z, ⟨r, rfl⟩, rfl⟩
    exact ⟨algebraMap (Algebra.adjoin B {x}) N r, r.property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, ⟨⟨z, hz⟩, rfl⟩, rfl⟩

/-- The trace dual of an integral monogenic order is the inverse-minimal-derivative multiple of
the order. This is the submodule form of the monogenic complementary-module formula
`R† = f'(α)⁻¹ R`.

The proof is a packaging of Mathlib's `traceForm_dualSubmodule_adjoin`, which in turn uses the
explicit trace-dual basis of a power basis. -/
theorem traceIntegralSubmodule_adjoin_eq_inv_derivative_smul
    {x : N} (hgen : Algebra.adjoin K {x} = ⊤) (hint : IsIntegral B x) :
    TraceIntegralSubmodule B K (Algebra.adjoin B {x}) N =
      (aeval x (derivative <| minpoly K x) : N)⁻¹ •
        (1 : Submodule (Algebra.adjoin B {x}) N) := by
  apply Submodule.restrictScalars_injective B
  rw [traceIntegralSubmodule_eq_traceDual]
  rw [Submodule.restrictScalars_traceDual]
  rw [one_restrictScalars_adjoin_eq_toSubmodule]
  rw [smul_one_restrictScalars_adjoin_eq_smul_toSubmodule]
  exact traceForm_dualSubmodule_adjoin B K hgen hint

end MonogenicOrder

section Overorder

variable (B K T N : Type*) [CommRing B] [Field K] [CommRing T] [Field N]
variable [Algebra B K] [Algebra B T] [Algebra B N] [Algebra K N] [Algebra T N]
variable [IsScalarTower B K N] [IsScalarTower B T N]
variable [IsDomain B] [IsIntegrallyClosed B] [IsFractionRing B K]
variable [IsDomain T] [NoZeroSMulDivisors T N]
variable [FiniteDimensional K N] [Algebra.IsSeparable K N]

omit [NoZeroSMulDivisors T N] [FiniteDimensional K N] [Algebra.IsSeparable K N] in
/-- The order-theoretic Jacobian maps to the derivative of the generic minimal polynomial. -/
theorem monogenicOrderJacobian_map_eq_generic
    (alpha : T) (halpha : IsIntegral B alpha) :
    algebraMap T N (monogenicOrderJacobian B T alpha) =
      aeval (algebraMap T N alpha)
        (derivative (minpoly K (algebraMap T N alpha))) := by
  rw [monogenicOrderJacobian, minpoly.isIntegrallyClosed_eq_field_fractions K N halpha,
    derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply]

/-- Generic-derivative form of the conductor--trace-dual identity for an overorder. -/
theorem traceIntegralSubmodule_eq_inv_derivative_smul_conductor
    (alpha : T) (halpha : IsIntegral B alpha)
    (hgen : Algebra.adjoin K {algebraMap T N alpha} = ⊤) :
    TraceIntegralSubmodule B K T N =
      (aeval (algebraMap T N alpha)
        (derivative <| minpoly K (algebraMap T N alpha)) : N)⁻¹ •
        IsLocalization.coeSubmodule N (monogenicOrderConductor B T alpha) := by
  let x : N := algebraMap T N alpha
  let J : N := aeval x (derivative <| minpoly K x)
  have hgen' : Algebra.adjoin K {x} = ⊤ := hgen
  have hxint : IsIntegral B x :=
    halpha.map (IsScalarTower.toAlgHom B T N)
  have hJ : J ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  have hdual := traceForm_dualSubmodule_adjoin B K hgen' hxint
  have hmem (y : N) :
      y ∈ (traceForm K N).dualSubmodule
          (Subalgebra.toSubmodule (Algebra.adjoin B {x})) ↔
        J * y ∈ Algebra.adjoin B {x} := by
    rw [hdual]
    rw [Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hJ)]
    simp only [inv_inv, Subalgebra.mem_toSubmodule]
  have hadjoin_le :
      Algebra.adjoin B {x} ≤ (IsScalarTower.toAlgHom B T N).range := by
    apply Algebra.adjoin_le
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨alpha, rfl⟩
  ext z
  change (∀ t : T, trace K N (z * algebraMap T N t) ∈ Set.range (algebraMap B K)) ↔ _
  rw [Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hJ)]
  simp only [inv_inv]
  rw [mem_coeSubmodule_conductor]
  constructor
  · intro hz t
    rw [mul_assoc]
    rw [← hmem]
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    obtain ⟨t', ht'⟩ := hadjoin_le hy
    rw [← ht']
    simpa [Submodule.mem_one, traceForm_apply, map_mul, mul_assoc] using hz (t * t')
  · intro hz t
    have hzt : J * (z * algebraMap T N t) ∈ Algebra.adjoin B {x} := by
      simpa [x, mul_assoc] using hz t
    have h := (hmem (z * algebraMap T N t)).mpr hzt
    rw [LinearMap.BilinForm.mem_dualSubmodule] at h
    have hone : (1 : N) ∈ Subalgebra.toSubmodule (Algebra.adjoin B {x}) :=
      (Algebra.adjoin B {x}).one_mem
    simpa [traceForm_apply] using h 1 hone

/-- For a finite separable generic extension generated by an integral `alpha`, the trace dual of
an overorder `T` is the inverse monogenic Jacobian times the conductor of `B[alpha]` in `T`:
`T† = J⁻¹ (B[alpha] : T)`.

No Dedekind-domain hypothesis on `T` is needed. The result follows directly from the monogenic
trace-dual formula and the membership characterization of Mathlib's conductor. -/
theorem traceIntegralSubmodule_eq_inv_jacobian_smul_conductor
    (alpha : T) (halpha : IsIntegral B alpha)
    (hgen : Algebra.adjoin K {algebraMap T N alpha} = ⊤) :
    TraceIntegralSubmodule B K T N =
      (algebraMap T N (monogenicOrderJacobian B T alpha))⁻¹ •
        IsLocalization.coeSubmodule N (monogenicOrderConductor B T alpha) := by
  rw [monogenicOrderJacobian_map_eq_generic B K T N alpha halpha]
  exact traceIntegralSubmodule_eq_inv_derivative_smul_conductor
    B K T N alpha halpha hgen

end Overorder

end

end CollisionIdeals.Planar
