import CollisionIdeals.General.Keller.ConjugateInvariantPole
import CollisionIdeals.General.Keller.DivisorVisibility

/-!
# The selected invariant pole on a visible source divisor

The existing nonzero invariant-class construction supplies the original
target prime and a coefficient identity with unit numerator there. Keller
source-divisor visibility gives a height-one source prime over that same
target prime. Contraction keeps the numerator a unit and the denominator
in the maximal ideal of its source localization.

The coefficient identity transports through the original inclusion K → L,
so the selected invariant representative is not regular at that visible
source divisor. No local faithful-flatness adapter, extension valuation,
new boundary model, or regularity premise is used. This constructs the
source-side contradiction setup; it does not supply the missing
mixed-sheet cancellation or prove vanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 20000

namespace CollisionIdeals

open AlgebraicGeometry

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ} {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance visibleSourcePoleBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance visibleSourcePoleBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toSMul

local instance visibleSourcePoleBaseFieldModule :
    Module (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toModule

@[reducible] local instance visibleSourcePolePullbackAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantBaseAlgebra D)

local instance visibleSourcePolePullbackSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) :=
  Algebra.toSMul

local instance visibleSourcePolePullbackModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) :=
  Algebra.toModule

@[reducible] local instance visibleSourcePoleInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

local instance visibleSourcePoleInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Algebra.toSMul

local instance visibleSourcePoleInvariantModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Algebra.toModule

local notation "B₀" => PolynomialImageAlgebra F
local notation "A₀" => SourceRing k (Fin n)
local notation "K₀" => PolynomialMapBaseFunctionField F
local notation "L₀" => PolynomialMapSourceFunctionField F

/-- The same polar invariant class remains polar on a constructed visible
source divisor over its target prime. Both local coefficient conditions
and source-field nonmembership are conclusions, not supplied regularity
or valuation hypotheses. -/
theorem polynomialConjugateInvariantQuotient_exists_visible_source_pole
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap B₀ (polynomialConjugateInvariantAlgebra D))) (hq : q ≠ 0) :
    ∃ (z : polynomialConjugateInvariantAlgebra D) (p : PrimeSpectrum B₀)
      (Q : PrimeSpectrum A₀) (a b : B₀),
      Submodule.Quotient.mk z = q ∧ p.asIdeal.primeHeight = 1 ∧
      p ∉ polynomialConjugateInvariantTargetOpen D hKeller ∧
      Q.asIdeal.primeHeight = 1 ∧ Q.asIdeal.under B₀ = p.asIdeal ∧
      Algebra.IsUnramifiedAt B₀ Q.asIdeal ∧
      (a : A₀) ∉ Q.asIdeal ∧ (b : A₀) ∈ Q.asIdeal ∧ b ≠ 0 ∧
      IsUnit (algebraMap A₀ (Localization.AtPrime Q.asIdeal) (a : A₀)) ∧
      algebraMap A₀ (Localization.AtPrime Q.asIdeal) (b : A₀) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal) ∧
      algebraMap A₀ L₀ (a : A₀) = algebraMap A₀ L₀ (b : A₀) *
        algebraMap K₀ L₀ ((polynomialConjugateInvariantBaseEquiv D).symm z : K₀) ∧
      algebraMap K₀ L₀ ((polynomialConjugateInvariantBaseEquiv D).symm z : K₀) ∉
        Localization.subalgebra.ofField L₀ Q.asIdeal.primeCompl
          Q.asIdeal.primeCompl_le_nonZeroDivisors := by
  obtain ⟨z, p, a, b, hRep, hHeight, hOutside, ha, hb, hb0, hC⟩ :=
    polynomialConjugateInvariantQuotient_exists_heightOne_boundary_pole D hKeller q hq
  obtain ⟨Q, hQHeight, hContract, hUnramified⟩ :=
    exists_visible_source_divisor_over_heightOne_of_isKeller F hKeller p hHeight
  have haQ : (a : A₀) ∉ Q.asIdeal := by
    change a ∉ Q.asIdeal.under B₀
    rw [hContract]
    exact ha
  have hbQ : (b : A₀) ∈ Q.asIdeal := by
    change b ∈ Q.asIdeal.under B₀
    rw [hContract]
    exact hb
  have hTarget : algebraMap B₀ K₀ a = algebraMap B₀ K₀ b *
      ((polynomialConjugateInvariantBaseEquiv D).symm z : K₀) := by
    have h := congrArg (polynomialConjugateInvariantBaseEquiv D).symm hC
    rw [map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at h
    exact congrArg Subtype.val h
  have hMap (t : B₀) : algebraMap K₀ L₀ (algebraMap B₀ K₀ t) =
      algebraMap A₀ L₀ (t : A₀) := by
    rw [← IsScalarTower.algebraMap_apply B₀ K₀ L₀,
      IsScalarTower.algebraMap_apply B₀ A₀ L₀]
    rfl
  have hSource : algebraMap A₀ L₀ (a : A₀) = algebraMap A₀ L₀ (b : A₀) *
      algebraMap K₀ L₀ ((polynomialConjugateInvariantBaseEquiv D).symm z : K₀) := by
    simpa only [map_mul, hMap] using congrArg (algebraMap K₀ L₀) hTarget
  refine ⟨z, p, Q, a, b, hRep, hHeight, hOutside, hQHeight, hContract,
    hUnramified, haQ, hbQ, hb0, ?_, ?_, hSource, ?_⟩
  · exact (IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime Q.asIdeal) Q.asIdeal (a : A₀)).mpr haQ
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime Q.asIdeal) Q.asIdeal (b : A₀)).mpr hbQ
  · exact not_mem_localization_of_pole_certificate Q _ (a : A₀) (b : A₀) haQ hbQ hSource

end

end CollisionIdeals
