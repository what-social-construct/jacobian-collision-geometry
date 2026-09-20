import CollisionIdeals.Planar.Research.Vanishing.ConductorLocalization
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Algebra.Module.Torsion.Free

/-!
# The derivative of an integral generator

Differentiating the defining equation retains the derivatives of its base
coefficients. For the existing monogenic Jacobian `J`, the result is
`J • d alpha = -nu`, where `nu` is the coefficientwise derivative evaluated
at `alpha`. If base derivatives lie in a lattice, so does `nu`; this only
controls `J • d alpha`. Controlling `d alpha` itself requires membership
of `nu` in `J` times that lattice, not just nonvanishing of `J`.

These are algebraic tests for the research route, not a proof of the
Keller-specific divisibility at a boundary prime.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

open scoped Pointwise

variable {k B T N : Type*}
  [CommRing k] [CommRing B] [CommRing T] [AddCommGroup N]
  [Algebra k B] [Algebra k T] [Algebra B T] [IsScalarTower k B T]
  [Module k N] [Module B N] [Module T N] [IsScalarTower B T N]

/-- The coefficientwise derivative term is controlled by base derivatives;
this does not divide by the monogenic Jacobian. -/
theorem eval_coefficient_derivative_mem
    (d : Derivation k T N) (Λ : Submodule T N) (alpha : T)
    (hBase : ∀ b : B, d (algebraMap B T b) ∈ Λ) (f : Polynomial B) :
    PolynomialModule.eval alpha ((d.compAlgebraMap B).mapCoeffs f) ∈ Λ := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    simpa only [map_add] using Λ.add_mem hf hg
  | monomial n b =>
    rw [Derivation.mapCoeffs_monomial]
    change PolynomialModule.eval alpha
      (PolynomialModule.single T n (d (algebraMap B T b))) ∈ Λ
    rw [PolynomialModule.eval_single]
    exact Λ.smul_mem (alpha ^ n) (hBase b)

/-- Differentiate the minimal-polynomial relation, including its varying
base coefficients. The Jacobian is the existing monogenic-order object. -/
theorem monogenicOrderJacobian_smul_derivation
    (d : Derivation k T N) (alpha : T) :
    monogenicOrderJacobian B T alpha • d alpha =
      -PolynomialModule.eval alpha
        ((d.compAlgebraMap B).mapCoeffs (minpoly B alpha)) := by
  have h := d.apply_aeval_eq alpha (minpoly B alpha)
  rw [minpoly.aeval, map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Base regularity clears the generator derivative after multiplying by
the monogenic Jacobian; it does not make this factor invertible locally. -/
theorem monogenicOrderJacobian_smul_derivation_mem
    (d : Derivation k T N) (Λ : Submodule T N) (alpha : T)
    (hBase : ∀ b : B, d (algebraMap B T b) ∈ Λ) :
    monogenicOrderJacobian B T alpha • d alpha ∈ Λ := by
  rw [monogenicOrderJacobian_smul_derivation]
  exact Λ.neg_mem (eval_coefficient_derivative_mem d Λ alpha hBase _)

/-- The exact cancellation test: the generator derivative belongs to the
lattice precisely when the coefficientwise term belongs to its Jacobian
multiple. Nonzero Jacobian permits cancellation, not division inside Λ. -/
theorem derivation_generator_mem_iff_coefficient_derivative_mem
    [IsDomain T] [Module.IsTorsionFree T N]
    (d : Derivation k T N) (Λ : Submodule T N) (alpha : T)
    (hJ : monogenicOrderJacobian B T alpha ≠ 0) :
    d alpha ∈ Λ ↔
      PolynomialModule.eval alpha
          ((d.compAlgebraMap B).mapCoeffs (minpoly B alpha)) ∈
        monogenicOrderJacobian B T alpha • Λ := by
  have h := monogenicOrderJacobian_smul_derivation (B := B) d alpha
  constructor
  · intro hd
    apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    refine ⟨-d alpha, Λ.neg_mem hd, ?_⟩
    rw [smul_neg, h, neg_neg]
  · intro hnu
    obtain ⟨x, hx, heq⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hnu
    have heq' : monogenicOrderJacobian B T alpha • d alpha =
        monogenicOrderJacobian B T alpha • (-x) := by
      rw [smul_neg, heq, h]
    have hd : d alpha = -x := smul_right_injective N hJ heq'
    rw [hd]
    exact Λ.neg_mem hx

/-- At a prime-adapted order, the remaining condition on all derivatives
is exactly divisibility of the coefficientwise term in the chosen local
lattice. The outside-prime conductor is supplied, not inferred from
nonvanishing of the conductor ideal. -/
theorem forall_derivation_mem_iff_coefficient_derivative_mem
    {R : Type*} [CommRing R] [Algebra T R] [Module R N]
    [IsScalarTower T R N] [IsDomain T] [Module.IsTorsionFree T N]
    (q : Ideal T) [q.IsPrime] [IsLocalization.AtPrime R q]
    (d : Derivation k T N) (Λ : Submodule R N) (alpha : T)
    (hBase : ∀ b : B, d (algebraMap B T b) ∈ Λ)
    {c : T} (hc : c ∈ monogenicOrderConductor B T alpha) (hcq : c ∉ q)
    (hJ : monogenicOrderJacobian B T alpha ≠ 0) :
    (∀ t : T, d t ∈ Λ) ↔
      PolynomialModule.eval alpha
          ((d.compAlgebraMap B).mapCoeffs (minpoly B alpha)) ∈
        monogenicOrderJacobian B T alpha • Λ.restrictScalars T := by
  rw [forall_derivation_mem_iff_of_conductor_not_mem q d Λ alpha hBase hc hcq]
  exact derivation_generator_mem_iff_coefficient_derivative_mem
    d (Λ.restrictScalars T) alpha hJ

end

end CollisionIdeals.Planar
