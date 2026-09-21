import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Quasi-finiteness below an integral extension

For a tower `B → I → E`, an integral injective map `I → E` is surjective
on prime spectra. Thus every fiber of `Spec I → Spec B` is the image of
the corresponding fiber for `E`. If `E/B` is quasi-finite and `I/B` is of
finite type, this proves that `I/B` is quasi-finite.

No Noetherian, domain, or normality hypothesis is needed for this descent.
-/

set_option autoImplicit false

namespace CollisionIdeals

/-- Quasi-finiteness descends through an integral injective extension when
the intermediate algebra is of finite type over the base. -/
theorem quasiFinite_of_integral_injective_extension
    (B I E : Type*) [CommRing B] [CommRing I] [CommRing E]
    [Algebra B I] [Algebra B E] [Algebra I E] [IsScalarTower B I E]
    [Algebra.FiniteType B I] [Algebra.QuasiFinite B E]
    [Algebra.IsIntegral I E]
    (hinj : Function.Injective (algebraMap I E)) :
    Algebra.QuasiFinite B I := by
  apply Algebra.QuasiFinite.iff_finite_comap_preimage_singleton.mpr
  intro p
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap I E)) :=
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral I E)).comap_surjective hinj
  apply ((Algebra.QuasiFinite.finite_comap_preimage_singleton (R := B) (S := E) p).image
    (PrimeSpectrum.comap (algebraMap I E))).subset
  intro q hq
  obtain ⟨r, rfl⟩ := hsurj q
  refine ⟨r, ?_, rfl⟩
  change PrimeSpectrum.comap (algebraMap B I)
    (PrimeSpectrum.comap (algebraMap I E) r) = p at hq
  change PrimeSpectrum.comap (algebraMap B E) r = p
  rwa [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq B I E] at hq

end CollisionIdeals
