import CollisionIdeals.General.Normalization.PolynomialConormal
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Derivation-compatible modules with nonzero annihilator

An additive operator satisfying the Leibniz rule for a base derivation
makes the module's annihilator stable under that derivation. On an algebra
isomorphic to a characteristic-zero polynomial ring, compatibility with
every coordinate partial therefore forces a module with nonzero
annihilator to vanish.

The main implication needs neither finite generation nor commuting
operators. A finite torsion module supplies its nonzero annihilator by
Mathlib's existing torsion theorem.

These are dimension-independent algebraic lemmas. They construct no
operators on boundary local cohomology or on a normalization quotient,
and assert no Keller-specific preservation or vanishing statement.
-/

set_option autoImplicit false

namespace CollisionIdeals

section General

variable {k B M : Type*} [CommRing k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

/-- A Leibniz operator preserves the module annihilator under its base
derivation. No scalar action of k on M needs to be separately chosen. -/
theorem derivation_mem_annihilator_of_leibniz
    (d : Derivation k B B) (nabla : M →+ M)
    (hLeibniz : ∀ (b : B) (m : M),
      nabla (b • m) = d b • m + b • nabla m)
    {b : B} (hb : b ∈ Module.annihilator B M) :
    d b ∈ Module.annihilator B M := by
  apply Module.mem_annihilator.mpr
  intro m
  have h := hLeibniz b m
  rw [Module.mem_annihilator.mp hb m, map_zero,
    Module.mem_annihilator.mp hb (nabla m), add_zero] at h
  exact h.symm

end General

section Polynomial

variable {σ k B M : Type*} [Field k] [CharZero k] [CommRing B] [Algebra k B]
  [AddCommMonoid M] [Module B M]

/-- Over a characteristic-zero polynomial algebra, compatible operators
for all coordinate partials exclude any nonzero uniform annihilator of a
nonzero module. No finiteness or integrability hypothesis is used. -/
theorem subsingleton_of_annihilator_ne_bot_of_polynomial_leibniz
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (hAnn : Module.annihilator B M ≠ ⊥) :
    Subsingleton M := by
  apply (Module.annihilator_eq_top_iff (R := B) (M := M)).mp
  apply (forall_polynomialEquivPartial_conormalComponent_eq_zero_iff
    e (Module.annihilator B M) hAnn).mp
  intro i
  apply (derivationConormalComponent_eq_zero_iff _ _).mpr
  intro b hb
  exact derivation_mem_annihilator_of_leibniz
    (polynomialEquivPartial e i) (nabla i) (hLeibniz i) hb

/-- Finite generation and torsion supply the uniform annihilator in the
preceding theorem. This is finiteness over B, not generation by differential
operators, and does not assert finiteness of a boundary pole module. -/
theorem subsingleton_of_finite_torsion_of_polynomial_leibniz
    [Module.Finite B M]
    (e : MvPolynomial σ k ≃ₐ[k] B) (nabla : σ → M →+ M)
    (hLeibniz : ∀ (i : σ) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m)
    (hTorsion : Module.IsTorsion B M) :
    Subsingleton M := by
  letI : Nontrivial B := e.symm.toEquiv.nontrivial
  obtain ⟨b, hb, hb0⟩ :=
    Submodule.annihilator_top_inter_nonZeroDivisors hTorsion
  have hbAnn : b ∈ Module.annihilator B M := by
    simpa only [Submodule.annihilator_top] using hb
  apply subsingleton_of_annihilator_ne_bot_of_polynomial_leibniz e nabla hLeibniz
  intro hAnn
  apply nonZeroDivisors.ne_zero hb0
  simpa only [hAnn, Ideal.mem_bot] using hbAnn

end Polynomial

end CollisionIdeals
