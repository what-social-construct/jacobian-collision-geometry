import CollisionIdeals.General.Galois.LocalInertia
import CollisionIdeals.General.Normalization.DivisorialValuation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Divisorial inertia on the normal-closure normalization

The constructed divisorial valuation ring is the localization at its defining
prime. Equivariant localization therefore identifies its valuation-theoretic
inertia with the inertia of that prime in the normalization ring.

This comparison does not itself assert that a ramified divisor has nontrivial
inertia; that further assertion uses the local ramification-index theorem.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ} {F : PolynomialSelfMap k n}
  {N : Type u} [Field N] [Algebra (PolynomialMapBaseFunctionField F) N]
  [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

local instance divisorialInertiaBaseAlgebra : Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

local instance divisorialInertiaBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance divisorialInertiaBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  divisorialInertiaBaseFieldAlgebra.toSMul

local instance divisorialInertiaScalarTower :
    IsScalarTower (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- For the actual divisorial valuation, valuation inertia and inertia of the
height-one normalization prime are the same subgroup of the Galois group. -/
theorem polynomialDivisorialValuation_inertiaGroupAt_eq
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1) :
    inertiaGroupAt (PolynomialMapBaseFunctionField F)
        (polynomialDivisorialValuation D p hp).valuationRing =
      Ideal.inertia (α := PolynomialNormalizationInExtensionRing (F := F) (N := N))
        (N ≃ₐ[PolynomialMapBaseFunctionField F] N) p.asIdeal := by
  letI := polynomialDivisorialValuationAlgebra D p hp
  letI := polynomialDivisorialValuation_isLocalizationAtPrime D p hp
  letI := polynomialDivisorialValuation_isScalarTower D p hp
  exact inertiaGroupAt_eq_idealInertia_of_primeLocalization
    (R := PolynomialNormalizationInExtensionRing (F := F) (N := N))
    (PolynomialMapBaseFunctionField F) p.asIdeal
    (polynomialDivisorialValuation D p hp).valuationRing (fun _ _ => rfl)

end

end CollisionIdeals
