import CollisionIdeals.General.Keller.ConjugateInvariantSections
import CollisionIdeals.General.Keller.ConjugateInvariantBoundary
import CollisionIdeals.General.Normalization.TargetPoleWitness
import CollisionIdeals.General.Normalization.DivisorialValuation

/-!
# An actual target boundary divisor from a nonzero invariant class

A nonzero class in the original module quotient `E^G / B` supplies an
invariant representative outside the base. Its existing embedding in the
target function field gives a reduced fraction and hence a height-one
target prime where its numerator is a unit and its denominator vanishes.

The coefficient identity already holds in the original invariant algebra.
It excludes a point over that prime in the actual target open. No boundary
divisor, pole-bearing coordinate, or nonempty boundary is supplied as a
separate hypothesis. This constructs the contradiction setup, not a bound
on the derivative orbit or planar vanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 10000

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ} {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N] [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance invariantPoleBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance invariantPoleBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance invariantPoleBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toSMul

local instance invariantPoleBaseFieldModule :
    Module (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toModule

@[reducible] local instance invariantPoleBaseInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantBaseAlgebra D)

local instance invariantPoleBaseInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) :=
  Algebra.toSMul

local instance invariantPoleBaseInvariantModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) :=
  Algebra.toModule

@[reducible] local instance invariantPoleInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

local instance invariantPoleInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Algebra.toSMul

local instance invariantPoleInvariantModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Algebra.toModule

local notation "B₀" => PolynomialImageAlgebra F

private theorem not_mem_invariantTargetOpen_of_pole_certificate
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (z : polynomialConjugateInvariantAlgebra D) (p : PrimeSpectrum B₀) (a b : B₀)
    (ha : a ∉ p.asIdeal) (hb : b ∈ p.asIdeal)
    (hab : algebraMap B₀ (polynomialConjugateInvariantAlgebra D) a =
      algebraMap B₀ (polynomialConjugateInvariantAlgebra D) b * z) :
    p ∉ polynomialConjugateInvariantTargetOpen D hKeller := by
  let C := polynomialConjugateInvariantAlgebra D
  letI := polynomialConjugateInvariantAlgebra_isOpenImmersion_of_isKeller D hKeller
  change ¬ ∃ P : PrimeSpectrum C,
    PrimeSpectrum.comap (algebraMap B₀ C) P = p
  rintro ⟨P, hP⟩
  have hContract : P.asIdeal.comap (algebraMap B₀ C) = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hP
  have hbP : algebraMap B₀ C b ∈ P.asIdeal := by
    change b ∈ P.asIdeal.comap (algebraMap B₀ C)
    rw [hContract]
    exact hb
  have haP : algebraMap B₀ C a ∈ P.asIdeal := by
    rw [hab]
    exact P.asIdeal.mul_mem_right z hbP
  have haBase : a ∈ P.asIdeal.comap (algebraMap B₀ C) := haP
  rw [hContract] at haBase
  exact ha haBase

/-- A nonzero class constructs an actual height-one target boundary point
and a representative with a local pole certificate at that same point.
The quotient is the original standard module quotient, not `Obs(F)`. -/
theorem polynomialConjugateInvariantQuotient_exists_heightOne_boundary_pole
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap B₀ (polynomialConjugateInvariantAlgebra D))) (hq : q ≠ 0) :
    ∃ (z : polynomialConjugateInvariantAlgebra D) (p : PrimeSpectrum B₀) (a b : B₀),
      Submodule.Quotient.mk z = q ∧ p.asIdeal.primeHeight = 1 ∧
      p ∉ polynomialConjugateInvariantTargetOpen D hKeller ∧
      a ∉ p.asIdeal ∧ b ∈ p.asIdeal ∧ b ≠ 0 ∧
      algebraMap B₀ (polynomialConjugateInvariantAlgebra D) a =
        algebraMap B₀ (polynomialConjugateInvariantAlgebra D) b * z := by
  classical
  let C := polynomialConjugateInvariantAlgebra D
  let K := PolynomialMapBaseFunctionField F
  let e := polynomialConjugateInvariantBaseEquiv D
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  let r : K := (e.symm z : polynomialConjugateInvariantBaseAlgebra D)
  have hr : r ∉ Set.range (algebraMap B₀ K) := by
    rintro ⟨b, hb⟩
    apply hq
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨b, ?_⟩
    apply e.symm.injective
    change e.symm (algebraMap B₀ C b) = e.symm z
    rw [e.symm.commutes]
    apply Subtype.ext
    exact hb
  letI := D.finiteIntermediate
  letI : IsNoetherianRing B₀ := polynomialImageAlgebra_isNoetherianRing F
  let eB := (AlgEquiv.ofInjective (coordinateAlgHom F)
    (coordinateAlgHom_injective_of_finiteDimensional F)).toMulEquiv
  letI : UniqueFactorizationMonoid B₀ :=
    MulEquiv.uniqueFactorizationMonoid eB inferInstance
  obtain ⟨p, a, b, hHeight, ha, hb, hb0, hab⟩ :=
    exists_heightOne_pole_certificate (B := B₀) r hr
  have hC : algebraMap B₀ C a = algebraMap B₀ C b * z := by
    apply e.symm.injective
    rw [map_mul, e.symm.commutes, e.symm.commutes]
    apply Subtype.ext
    exact hab
  exact ⟨z, p, a, b, rfl, hHeight,
    not_mem_invariantTargetOpen_of_pole_certificate D hKeller z p a b ha hb hC,
    ha, hb, hb0, hC⟩

/-- The same construction gives an actual target DVR and a pole in its
embedded local ring. Neither the prime nor the polar representative is
supplied independently of the nonzero original quotient class. -/
theorem polynomialConjugateInvariantQuotient_exists_targetDVR_pole
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap B₀ (polynomialConjugateInvariantAlgebra D))) (hq : q ≠ 0) :
    ∃ (z : polynomialConjugateInvariantAlgebra D) (p : PrimeSpectrum B₀),
      Submodule.Quotient.mk z = q ∧ p.asIdeal.primeHeight = 1 ∧
      p ∉ polynomialConjugateInvariantTargetOpen D hKeller ∧
      IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) ∧
      ((polynomialConjugateInvariantBaseEquiv D).symm z : PolynomialMapBaseFunctionField F) ∉
        Localization.subalgebra.ofField (PolynomialMapBaseFunctionField F)
          p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors := by
  obtain ⟨z, p, a, b, hRep, hHeight, hOutside, ha, hb, _, hC⟩ :=
    polynomialConjugateInvariantQuotient_exists_heightOne_boundary_pole D hKeller q hq
  letI := D.finiteIntermediate
  letI : IsNoetherianRing B₀ := polynomialImageAlgebra_isNoetherianRing F
  letI : IsIntegrallyClosed B₀ :=
    polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  refine ⟨z, p, hRep, hHeight, hOutside, heightOne_isDiscreteValuationRing p hHeight, ?_⟩
  apply not_mem_localization_of_pole_certificate p _ a b ha hb
  have h := congrArg (polynomialConjugateInvariantBaseEquiv D).symm hC
  rw [map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at h
  exact congrArg Subtype.val h

end

end CollisionIdeals
