import CollisionIdeals.Planar.Research.Vanishing.ConductorComparison
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local generator control after inverting a conductor

If a conductor element for `B[alpha]` becomes a unit in an algebra `R`,
derivative control of `alpha` is equivalent to derivative control of all
of `T` in an `R`-submodule of the ambient module. The base derivatives
must already belong to that submodule.

At a prime localization, it suffices for the conductor element to avoid
the prime. These are conditional algebraic reductions: they do not prove
either conductor avoidance or control of an actual Keller derivative.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

section

variable {k B T R N : Type*}
  [CommRing k] [CommRing B] [CommRing T] [CommRing R] [AddCommGroup N]
  [Algebra k T] [Algebra B T] [Algebra T R]
  [Module k N] [Module T N] [Module R N] [IsScalarTower T R N]

/-- Inverting a conductor element reduces control of every derivative to
control of the monogenic generator. No local-ring assumption is needed
once the conductor element is a unit. -/
theorem forall_derivation_mem_iff_of_isUnit_conductor
    (d : Derivation k T N) (Λ : Submodule R N) (alpha : T)
    (hBase : ∀ b : B, d (algebraMap B T b) ∈ Λ)
    {c : T} (hc : c ∈ monogenicOrderConductor B T alpha)
    (hcunit : IsUnit (algebraMap T R c)) :
    (∀ t : T, d t ∈ Λ) ↔ d alpha ∈ Λ := by
  constructor
  · intro h
    exact h alpha
  · intro hAlpha t
    apply (Λ.smul_mem_iff_of_isUnit hcunit).mp
    rw [IsScalarTower.algebraMap_smul R c]
    exact conductor_smul_derivation_mem_of_generator d (Λ.restrictScalars T)
      alpha hBase hAlpha hc t

/-- At a prime localization, a conductor element outside the prime makes
generator control equivalent to control of every derivative. -/
theorem forall_derivation_mem_iff_of_conductor_not_mem
    (q : Ideal T) [q.IsPrime] [IsLocalization.AtPrime R q]
    (d : Derivation k T N) (Λ : Submodule R N) (alpha : T)
    (hBase : ∀ b : B, d (algebraMap B T b) ∈ Λ)
    {c : T} (hc : c ∈ monogenicOrderConductor B T alpha) (hcq : c ∉ q) :
    (∀ t : T, d t ∈ Λ) ↔ d alpha ∈ Λ := by
  exact forall_derivation_mem_iff_of_isUnit_conductor d Λ alpha hBase hc
    ((IsLocalization.AtPrime.isUnit_to_map_iff R q c).mpr hcq)

end

end CollisionIdeals.Planar
