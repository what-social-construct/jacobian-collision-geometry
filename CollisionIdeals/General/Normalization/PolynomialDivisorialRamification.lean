import CollisionIdeals.General.Normalization.DivisorialHeight
import CollisionIdeals.General.Normalization.DivisorialRamification

/-!
# Nontrivial inertia at polynomial-normalization divisors

In characteristic zero, the actual ramified height-one points of the
normal-closure normalization have nontrivial inertia for their constructed
divisorial valuations. No inertia certificate is supplied as an input.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

universe u

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} {F : PolynomialSelfMap k n}
  {N : Type u} [Field N] [Algebra (PolynomialMapBaseFunctionField F) N]
  [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

local instance polynomialRamificationBaseAlgebra : Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

local instance polynomialRamificationBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance polynomialRamificationBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  polynomialRamificationBaseFieldAlgebra.toSMul

local instance polynomialRamificationScalarTower :
    IsScalarTower (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Ramification at a normalization divisor forces nontrivial inertia
for the actual divisorial valuation constructed at that divisor. -/
theorem polynomialDivisorialValuation_inertia_ne_bot_of_ramified
    (D : PolynomialNormalClosureData F N)
    (p : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hp : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) p.asIdeal = 1)
    (hRam : ¬ Algebra.IsUnramifiedAt
      (A := PolynomialNormalizationInExtensionRing (F := F) (N := N))
      (PolynomialImageAlgebra F) p.asIdeal) :
    inertiaGroupAt (PolynomialMapBaseFunctionField F)
      (polynomialDivisorialValuation D p hp).valuationRing ≠ ⊥ := by
  rw [polynomialDivisorialValuation_inertiaGroupAt_eq D p hp]
  let B : Type u := PolynomialImageAlgebra F
  let K : Type u := PolynomialMapBaseFunctionField F
  letI := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : IsGalois K N := IsGalois.mk
  letI : IsNoetherianRing B := polynomialImageAlgebra_isNoetherianRing F
  letI : IsIntegrallyClosed B :=
    polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  exact integralClosure_inertia_ne_bot_of_not_isUnramifiedAt k B N p.asIdeal
    (polynomialNormalization_primeHeight_under_eq_one D p hp) hRam

/-- The ramified-point type already supplies the height and ramification
hypotheses needed by the nontrivial-inertia theorem. -/
theorem polynomialRamifiedPoint_inertia_nontrivial
    (D : PolynomialNormalClosureData F N)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    inertiaGroupAt (PolynomialMapBaseFunctionField F)
      (polynomialDivisorialValuation D E.1 E.2.1).valuationRing ≠ ⊥ :=
  polynomialDivisorialValuation_inertia_ne_bot_of_ramified D E.1 E.2.1 E.2.2

end

end CollisionIdeals
