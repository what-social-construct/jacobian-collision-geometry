import CollisionIdeals.General.Keller.ConjugateInvariantPole
import CollisionIdeals.General.Keller.ConjugateInvariantConormal
import CollisionIdeals.General.Normalization.LocalizedPoleTower
import CollisionIdeals.Planar.Basic
import CollisionIdeals.Planar.Research.Vanishing.TargetFrameCompatibility

/-!
# The transverse pole calculation at the constructed target divisor

A hypothetical nonzero class in the original invariant quotient constructs
a target boundary DVR. A target-coordinate partial is transverse there;
its localization is regular, and the polar representative has a derived
unit numerator over a positive power of the transverse parameter.

The existing iterated numerator calculation therefore applies at this
actual divisor. No divisor, transverse derivative, numerator, or pole
tower is supplied separately. This gives growing target-field poles, not
a bound on the Keller orbit or vanishing of the invariant quotient.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 20000

namespace CollisionIdeals

open AlgebraicGeometry

noncomputable section

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance targetTowerBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance targetTowerBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance targetTowerBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toSMul

local instance targetTowerBaseFieldModule :
    Module (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toModule

@[reducible] local instance targetTowerBaseInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantBaseAlgebra D)

local instance targetTowerBaseInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) :=
  Algebra.toSMul

local instance targetTowerBaseInvariantModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateInvariantBaseAlgebra D) :=
  Algebra.toModule

@[reducible] local instance targetTowerLocalBaseAlgebra
    (p : PrimeSpectrum (PolynomialImageAlgebra F)) :
    Algebra (PolynomialImageAlgebra F) (Localization.AtPrime p.asIdeal) :=
  OreLocalization.instAlgebra

local instance targetTowerLocalBaseSMul (p : PrimeSpectrum (PolynomialImageAlgebra F)) :
    SMul (PolynomialImageAlgebra F) (Localization.AtPrime p.asIdeal) := Algebra.toSMul

local instance targetTowerLocalBaseModule (p : PrimeSpectrum (PolynomialImageAlgebra F)) :
    Module (PolynomialImageAlgebra F) (Localization.AtPrime p.asIdeal) := Algebra.toModule

@[reducible] local instance targetTowerInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

local instance targetTowerInvariantSMul (D : PolynomialNormalClosureData F N) :
    SMul (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) := Algebra.toSMul

local instance targetTowerInvariantModule (D : PolynomialNormalClosureData F N) :
    Module (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) := Algebra.toModule

local notation "B₀" => PolynomialImageAlgebra F
local notation "K₀" => PolynomialMapBaseFunctionField F

/-- The canonical fraction-field target partial computes each iterate of
the already constructed invariant Keller frame, under the original
target-field embedding. No new frame action is supplied. -/
theorem planarKellerInvariantFrame_targetPartial_iterate
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c) (i : Fin 2)
    (z : polynomialConjugateInvariantAlgebra D) (order : ℕ) :
    letI := D.finiteIntermediate
    ((localizationDerivation (nonZeroDivisors B₀) K₀
        (polynomialImageCoordinatePartial F i) : K₀ → K₀)^[order])
      ((polynomialConjugateInvariantBaseEquiv D).symm z : K₀) =
    ((polynomialConjugateInvariantBaseEquiv D).symm
      (((planarKellerInvariantFrame D c hc hJ i :
        polynomialConjugateInvariantAlgebra D → polynomialConjugateInvariantAlgebra D)^[order])
          z) : K₀) := by
  letI := D.finiteIntermediate
  induction order with
  | zero => rfl
  | succ order ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact planarKellerInvariantFrame_baseField_compatible D c hc hJ i _
        (fun b => localizationDerivation_algebraMap (nonZeroDivisors B₀) K₀ _ b) _

/-- At the target divisor derived from the nonzero class, one actual
target partial has iterates with unit numerators and successive denominator
powers. The prime and all local data are conclusions, not inputs. -/
theorem planarKellerInvariantQuotient_exists_transverse_target_pole_tower
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap B₀ (polynomialConjugateInvariantAlgebra D))) (hq : q ≠ 0) :
    letI := D.finiteIntermediate
    ∃ (z : polynomialConjugateInvariantAlgebra D) (p : PrimeSpectrum B₀)
      (i : Fin 2) (b : B₀) (m : ℕ),
      Submodule.Quotient.mk z = q ∧ p.asIdeal.primeHeight = 1 ∧
      p ∉ polynomialConjugateInvariantTargetOpen D hKeller ∧
      b ∈ p.asIdeal ∧ polynomialImageCoordinatePartial F i b ∉ p.asIdeal ∧ 0 < m ∧
      let R := Localization.AtPrime p.asIdeal
      letI : Algebra R K₀ := IsLocalization.localizationAlgebraOfSubmonoidLe
        R K₀ p.asIdeal.primeCompl (nonZeroDivisors B₀)
          p.asIdeal.primeCompl_le_nonZeroDivisors
      ∀ order : ℕ, ∃ u : R, IsUnit u ∧
        ((localizationDerivation (nonZeroDivisors B₀) K₀
            (polynomialImageCoordinatePartial F i) : K₀ → K₀)^[order])
          ((polynomialConjugateInvariantBaseEquiv D).symm z : K₀) =
        algebraMap R K₀ u / algebraMap B₀ K₀ b ^ (m + order) ∧
        ((localizationDerivation (nonZeroDivisors B₀) K₀
            (polynomialImageCoordinatePartial F i) : K₀ → K₀)^[order])
          ((polynomialConjugateInvariantBaseEquiv D).symm z : K₀) ∉
          Localization.subalgebra.ofField K₀ p.asIdeal.primeCompl
            p.asIdeal.primeCompl_le_nonZeroDivisors := by
  letI := D.finiteIntermediate
  obtain ⟨z, p, hRep, hHeight, hOutside, hDVR, hPole⟩ :=
    polynomialConjugateInvariantQuotient_exists_targetDVR_pole D hKeller q hq
  have hp : p.asIdeal ≠ ⊥ := by
    intro h
    have hzero : p.asIdeal.primeHeight = 0 := by
      rw [← Ideal.height_eq_primeHeight, h, Ideal.height_bot]
    rw [hHeight] at hzero
    exact one_ne_zero hzero
  let e := AlgEquiv.ofInjective (coordinateAlgHom F)
    (coordinateAlgHom_injective_of_finiteDimensional F)
  obtain ⟨i, b, hb, hdb, _hLocalizedUnit⟩ :=
    exists_polynomialEquivPartialAtPrime_transverse e p hp
  obtain ⟨m, hm, hTower⟩ := exists_localized_unit_pole_tower
    (k := ℂ) (B := B₀) (K := K₀) (polynomialImageCoordinatePartial F i)
    p hDVR b hb hdb
    ((polynomialConjugateInvariantBaseEquiv D).symm z : K₀) hPole
  exact ⟨z, p, i, b, m, hRep, hHeight, hOutside, hb, hdb, hm, hTower⟩

/-- The poles belong to the actual invariant Keller-frame orbit. The
same target divisor works at every order; no boundary regularity or
uniform orbit bound is supplied as a premise. -/
theorem planarKellerInvariantQuotient_exists_frame_target_poles
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap B₀ (polynomialConjugateInvariantAlgebra D))) (hq : q ≠ 0) :
    ∃ (z : polynomialConjugateInvariantAlgebra D) (p : PrimeSpectrum B₀) (i : Fin 2),
      Submodule.Quotient.mk z = q ∧ p.asIdeal.primeHeight = 1 ∧
      p ∉ polynomialConjugateInvariantTargetOpen D ⟨c, hc, hJ⟩ ∧
      ∀ order : ℕ,
        ((polynomialConjugateInvariantBaseEquiv D).symm
          (((planarKellerInvariantFrame D c hc hJ i :
            polynomialConjugateInvariantAlgebra D → polynomialConjugateInvariantAlgebra D)^[order])
              z) : K₀) ∉
          Localization.subalgebra.ofField K₀ p.asIdeal.primeCompl
            p.asIdeal.primeCompl_le_nonZeroDivisors := by
  letI := D.finiteIntermediate
  obtain ⟨z, p, i, _b, _m, hRep, hHeight, hOutside, _hb, _hdb, _hm, hTower⟩ :=
    planarKellerInvariantQuotient_exists_transverse_target_pole_tower D ⟨c, hc, hJ⟩ q hq
  refine ⟨z, p, i, hRep, hHeight, hOutside, ?_⟩
  intro order
  obtain ⟨_u, _hu, _hCalc, hPole⟩ := hTower order
  rw [← planarKellerInvariantFrame_targetPartial_iterate D c hc hJ i z order]
  exact hPole

end

end CollisionIdeals
