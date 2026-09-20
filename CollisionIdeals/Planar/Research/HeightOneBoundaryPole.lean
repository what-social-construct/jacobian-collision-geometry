import CollisionIdeals.Planar.Research.BoundarySectionLocalization
import CollisionIdeals.Planar.Research.LocalizationDenominator
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.Finiteness

/-!
# A genuine section with a pole along a removed divisor

At a height-one prime containing a nonzero ideal `J`, a power of `J`
locally clears the denominator of a nonzero `f ∈ J`. Finite generation
clears this localized containment by a single element outside the prime.
The resulting fraction is an actual section off `V(J)`, but is not in the
base ring. No Keller, inertia, or landing hypothesis is used.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

section Algebra

variable {T : Type*} [CommRing T] [IsDomain T] [IsNoetherianRing T]

/-- A height-one prime containing `J` gives an ideal-power denominator
whose numerator is outside that prime. -/
theorem exists_heightOne_boundary_denominator
    (J : Ideal T) (hJ : J ≠ ⊥) (p : PrimeSpectrum T)
    (hp : p.asIdeal.primeHeight = 1) (hJp : J ≤ p.asIdeal) :
    ∃ (f t : T) (n : ℕ), f ∈ J ∧ f ≠ 0 ∧ t ∉ p.asIdeal ∧
      ∀ x ∈ J ^ n, t * x ∈ Ideal.span {f} := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  let A := Localization.AtPrime p.asIdeal
  have hdim : ringKrullDim A = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A,
      Ideal.height_eq_primeHeight, hp]
    simp
  have hfA : algebraMap T A f ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective T A).ne hf0
  have hrad :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hdim).2
      (algebraMap T A f) hfA
  have hlocal : J.map (algebraMap T A) ≤
      (Ideal.span {algebraMap T A f}).radical := by
    apply le_trans (Ideal.map_mono hJp)
    rwa [IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal A]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hlocal
    (IsNoetherian.noetherian _)
  have hmap : (J ^ n).map (algebraMap T A) ≤
      (Ideal.span {f}).map (algebraMap T A) := by
    rw [Ideal.map_pow (algebraMap T A) J n, Ideal.map_span, Set.image_singleton]
    exact hn
  obtain ⟨t, ht, hclear⟩ := exists_denominator_mul_mem_of_map_le
    (S := A) p.asIdeal.primeCompl (J ^ n) (Ideal.span {f})
    (IsNoetherian.noetherian _) hmap
  exact ⟨f, t, n, hf, hf0, ht, hclear⟩

end Algebra

open AlgebraicGeometry CategoryTheory

variable {T N : Type} [CommRing T] [IsDomain T] [IsNoetherianRing T]
variable [Field N] [Algebra T N] [IsFractionRing T N]

/-- Removing a height-one prime allows a genuine rational section outside
the base ring. Here the open can be any nonempty subset of `D(J)`. -/
theorem affineSections_range_ne_bot_of_heightOne
    (U : (Spec (.of T)).Opens) [Nonempty U]
    (J : Ideal T) (hJ : J ≠ ⊥)
    (hU : ∀ x : U, ¬ J ≤ x.1.asIdeal)
    (p : PrimeSpectrum T) (hp : p.asIdeal.primeHeight = 1)
    (hJp : J ≤ p.asIdeal) :
    (affineSectionsToFractionField (N := N) U).range ≠ ⊥ := by
  obtain ⟨f, t, n, hf, hf0, htp, hclear⟩ :=
    exists_heightOne_boundary_denominator J hJ p hp hJp
  let z : N := algebraMap T N t / algebraMap T N f
  have hfN : algebraMap T N f ≠ 0 := by
    simpa using (IsFractionRing.injective T N).ne hf0
  have hz : z ∈ (affineSectionsToFractionField (N := N) U).range := by
    apply mem_affineSectionsToFractionField_range_of_ideal_pow_mul U J n z hU
    intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (hclear x hx)
    refine ⟨a, ?_⟩
    change algebraMap T N x * (algebraMap T N t / algebraMap T N f) = _
    field_simp [hfN]
    simpa only [map_mul, mul_comm] using congrArg (algebraMap T N) ha
  intro hbot
  rw [hbot, Algebra.mem_bot] at hz
  obtain ⟨a, ha⟩ := hz
  have htf : t = a * f := by
    apply IsFractionRing.injective T N
    rw [map_mul]
    exact (div_eq_iff hfN).mp ha.symm
  apply htp
  rw [htf]
  exact p.asIdeal.mul_mem_left a (hJp hf)

end

end CollisionIdeals.Planar
