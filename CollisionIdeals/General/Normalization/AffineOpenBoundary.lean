import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The reduced complement of an open in an affine spectrum

The vanishing ideal of the closed complement of `U ⊆ Spec R` is its
canonical reduced boundary ideal. This uses the existing prime-spectrum
vanishing ideal and makes no principal-presentation choice.

An empty boundary corresponds to the unit ideal, not the zero ideal. For
a nonempty open the boundary ideal is nonzero, even if the complement is
empty. None of these statements proves that a particular open is the
whole target.
-/

set_option autoImplicit false

namespace CollisionIdeals

universe u

variable {R : Type u} [CommRing R]

/-- The canonical reduced ideal of the closed complement of an open in
`Spec R`. No generator or principal presentation is selected. -/
def affineOpenBoundaryIdeal (U : TopologicalSpace.Opens (PrimeSpectrum R)) : Ideal R :=
  PrimeSpectrum.vanishingIdeal (U : Set (PrimeSpectrum R))ᶜ

/-- The complement ideal is radical by its vanishing-ideal construction. -/
theorem affineOpenBoundaryIdeal_isRadical
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    (affineOpenBoundaryIdeal U).IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal _

/-- The reduced boundary has exactly the closed complement as its support. -/
theorem affineOpenBoundaryIdeal_zeroLocus
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    PrimeSpectrum.zeroLocus (affineOpenBoundaryIdeal U : Set R) =
      (U : Set (PrimeSpectrum R))ᶜ := by
  rw [affineOpenBoundaryIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact U.isOpen.isClosed_compl.closure_eq

/-- The reduced boundary is empty exactly when the open is the whole
spectrum; the defining ideal is then the unit ideal. -/
theorem affineOpenBoundaryIdeal_eq_top_iff
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    affineOpenBoundaryIdeal U = ⊤ ↔ U = ⊤ := by
  rw [affineOpenBoundaryIdeal, PrimeSpectrum.vanishingIdeal_eq_top_iff,
    Set.compl_empty_iff, TopologicalSpace.Opens.coe_eq_univ]

/-- A nonempty open has a nonzero complement ideal. This is distinct from
the unit-ideal condition asserting that the complement is empty, and does
not require the ambient ring to be a domain. -/
theorem affineOpenBoundaryIdeal_ne_bot_of_nonempty
    (U : TopologicalSpace.Opens (PrimeSpectrum R))
    (hU : (U : Set (PrimeSpectrum R)).Nonempty) :
    affineOpenBoundaryIdeal U ≠ ⊥ := by
  intro hzero
  obtain ⟨x, hx⟩ := hU
  have hcompl : x ∈ (U : Set (PrimeSpectrum R))ᶜ := by
    rw [← affineOpenBoundaryIdeal_zeroLocus U, hzero, PrimeSpectrum.zeroLocus_bot]
    trivial
  exact hcompl hx

end CollisionIdeals
