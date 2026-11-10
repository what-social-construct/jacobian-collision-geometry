import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Unit-numerator presentations of poles over a DVR

An element of the fraction field outside a DVR has a positive pole order
with a unit numerator, for any chosen uniformizer. A parameter in the
maximal ideal with a unit derivative is irreducible, so the same
presentation applies to a transverse local parameter.
-/

set_option autoImplicit false

namespace CollisionIdeals

section Local

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
  [IsLocalRing R]

/-- A local parameter with a unit derivative cannot be a product of two
nonunits. This criterion does not require a domain or a DVR. -/
theorem irreducible_of_mem_maximalIdeal_of_isUnit_derivation
    (d : Derivation k R R) {f : R}
    (hf : f ∈ IsLocalRing.maximalIdeal R) (hdf : IsUnit (d f)) :
    Irreducible f := by
  refine ⟨?_, ?_⟩
  · exact fun hfUnit => (IsLocalRing.notMem_maximalIdeal.mpr hfUnit) hf
  · intro a b hab
    by_contra h
    push_neg at h
    have ha : a ∈ IsLocalRing.maximalIdeal R := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h.1
    have hb : b ∈ IsLocalRing.maximalIdeal R := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h.2
    have hdfMem : d f ∈ IsLocalRing.maximalIdeal R := by
      rw [hab, d.leibniz]
      simpa only [smul_eq_mul] using
        (IsLocalRing.maximalIdeal R).add_mem
          ((IsLocalRing.maximalIdeal R).mul_mem_right (d b) ha)
          ((IsLocalRing.maximalIdeal R).mul_mem_right (d a) hb)
    exact (IsLocalRing.notMem_maximalIdeal.mpr hdf) hdfMem

end Local

section LocalFractionField

variable {R K : Type*} [CommRing R] [IsLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A positive-order fraction with unit numerator at a nonzero local
parameter is outside the local ring. No discrete valuation is required
for this converse certificate. -/
theorem unit_pole_not_mem_range
    {f u : R} (hf : f ∈ IsLocalRing.maximalIdeal R)
    (hfK : algebraMap R K f ≠ 0) (hu : IsUnit u)
    (m : ℕ) (hm : 0 < m) :
    algebraMap R K u / (algebraMap R K f) ^ m ∉
      Set.range (algebraMap R K) := by
  rintro ⟨a, ha⟩
  have hProduct : a * f ^ m = u := by
    apply IsFractionRing.injective R K
    simpa only [map_mul, map_pow] using
      (eq_div_iff (pow_ne_zero m hfK)).mp ha
  have huMem : u ∈ IsLocalRing.maximalIdeal R := by
    rw [← hProduct]
    exact (IsLocalRing.maximalIdeal R).mul_mem_left a
      ((IsLocalRing.maximalIdeal R).pow_mem_of_mem hf m hm)
  exact (IsLocalRing.notMem_maximalIdeal.mpr hu) huMem

end LocalFractionField

section FractionField

variable {R K : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- Every element outside a DVR has a positive-order pole with unit
numerator, using the specified irreducible element as uniformizer. -/
theorem exists_unit_pole_presentation_of_not_mem_range
    (f : R) (hf : Irreducible f) (r : K)
    (hr : r ∉ Set.range (algebraMap R K)) :
    ∃ (m : ℕ) (u : R), 0 < m ∧ IsUnit u ∧
      r = algebraMap R K u / (algebraMap R K f) ^ m := by
  have hr0 : r ≠ 0 := by
    intro h
    exact hr ⟨0, by simpa only [map_zero] using h.symm⟩
  obtain hInteger | hInverseInteger := ValuationRing.isInteger_or_isInteger R r
  · exact (hr hInteger).elim
  · obtain ⟨a, ha⟩ := hInverseInteger
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha
      exact (inv_ne_zero hr0) ha.symm
    obtain ⟨m, w, hw⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hf
    have hrEq : r =
        algebraMap R K (↑(w⁻¹ : Rˣ) : R) / (algebraMap R K f) ^ m := by
      have hInv : r⁻¹ = algebraMap R K (↑w : R) * (algebraMap R K f) ^ m := by
        rw [← ha, hw, map_mul, map_pow]
      have hW : algebraMap R K (↑(w⁻¹ : Rˣ) : R) =
          (algebraMap R K (↑w : R))⁻¹ := by
        exact map_units_inv (algebraMap R K) w
      rw [hW, div_eq_mul_inv, ← mul_inv, ← hInv, inv_inv]
    have hm : 0 < m := by
      by_contra h
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
      apply hr
      exact ⟨↑(w⁻¹ : Rˣ), by simpa only [hm0, pow_zero, div_one] using hrEq.symm⟩
    exact ⟨m, ↑(w⁻¹ : Rˣ), hm, (w⁻¹).isUnit, hrEq⟩

/-- A pole over a DVR admits a uniformizer and a unit numerator with a
strictly positive exponent. -/
theorem exists_uniformizer_unit_pole_presentation_of_not_mem_range
    (r : K) (hr : r ∉ Set.range (algebraMap R K)) :
    ∃ (f u : R) (m : ℕ), Irreducible f ∧ 0 < m ∧ IsUnit u ∧
      r = algebraMap R K u / (algebraMap R K f) ^ m := by
  obtain ⟨f, hf⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, hm, hu, hrEq⟩ :=
    exists_unit_pole_presentation_of_not_mem_range f hf r hr
  exact ⟨f, u, m, hf, hm, hu, hrEq⟩

variable {k : Type*} [CommRing k] [Algebra k R]

/-- A transverse local parameter gives the actual denominator of a
unit-numerator pole presentation; no numerator is supplied as input. -/
theorem exists_unit_pole_presentation_of_isUnit_derivation
    (d : Derivation k R R) {f : R}
    (hf : f ∈ IsLocalRing.maximalIdeal R) (hdf : IsUnit (d f))
    (r : K) (hr : r ∉ Set.range (algebraMap R K)) :
    ∃ (m : ℕ) (u : R), 0 < m ∧ IsUnit u ∧
      r = algebraMap R K u / (algebraMap R K f) ^ m :=
  exists_unit_pole_presentation_of_not_mem_range f
    (irreducible_of_mem_maximalIdeal_of_isUnit_derivation d hf hdf) r hr

end FractionField

end CollisionIdeals
