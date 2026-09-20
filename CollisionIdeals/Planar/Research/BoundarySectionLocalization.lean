import CollisionIdeals.Planar.Research.BoundarySections

/-!
# Rational functions regular away from the boundary

This file constructs genuine structure-sheaf sections from local fraction
presentations.  In particular, an ideal-power denominator condition produces
a section on the complement of the ideal's zero locus.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

open AlgebraicGeometry CategoryTheory

variable {T N : Type} [CommRing T] [IsDomain T] [Field N]
variable [Algebra T N] [IsFractionRing T N]

/-- A rational function which admits an integral local fraction at every point
of an open is the image of an actual structure-sheaf section on that open. -/
theorem mem_affineSectionsToFractionField_range_of_localFractions
    (U : (Spec (.of T)).Opens) [Nonempty U] (z : N)
    (h : ∀ x : U, ∃ a b : T, b ∉ x.1.asIdeal ∧
      algebraMap T N b * z = algebraMap T N a) :
    z ∈ (affineSectionsToFractionField (N := N) U).range := by
  classical
  choose a b hb he using h
  have hcross (x y : U) : b y * a x = b x * a y := by
    apply IsFractionRing.injective T N
    simp only [map_mul, ← he]
    ring
  let s : Γ(Spec (.of T), U) := ⟨fun x =>
    LocalizedModule.mk (a x) ⟨b x, hb x⟩, fun x => by
      refine ⟨U ⊓ PrimeSpectrum.basicOpen (b x), ⟨x.2, hb x⟩,
        (show U ⊓ PrimeSpectrum.basicOpen (b x) ≤ U from inf_le_left).hom,
        a x, b x, ?_⟩
      intro y
      refine ⟨y.2.2, LocalizedModule.mk_eq.mpr ⟨1, ?_⟩⟩
      simpa only [Submonoid.smul_def, one_smul, smul_eq_mul] using
        (hcross x ⟨y.1, y.2.1⟩).symm⟩
  let x : U := Classical.choice (by assumption)
  have hs : b x • s = algebraMap T Γ(Spec (.of T), U) (a x) := by
    apply Subtype.ext
    funext y
    change b x • LocalizedModule.mk (a y) ⟨b y, hb y⟩ =
      LocalizedModule.mk (a x) ⟨1, _⟩
    rw [LocalizedModule.smul'_mk]
    apply LocalizedModule.mk_eq.mpr
    refine ⟨1, ?_⟩
    simpa only [Submonoid.smul_def, one_smul, smul_eq_mul, one_mul] using
      (hcross x y).symm
  refine ⟨s, ?_⟩
  have hb0 : algebraMap T N (b x) ≠ 0 := by
    intro h0
    have hb0 : b x = 0 := (IsFractionRing.injective T N) (by simpa using h0)
    exact hb x (hb0 ▸ x.1.asIdeal.zero_mem)
  apply mul_left_cancel₀ hb0
  calc
    algebraMap T N (b x) * affineSectionsToFractionField U s =
        affineSectionsToFractionField U (b x • s) := by
      simp only [Algebra.smul_def, map_mul, AlgHom.commutes]
    _ = algebraMap T N (a x) := by rw [hs]; exact AlgHom.commutes _ _
    _ = algebraMap T N (b x) * z := (he x).symm

/-- An ideal-power denominator condition guarantees regularity on every open
avoiding the ideal's zero locus.  This produces a genuine section, not an
additional assumed element of the section ring. -/
theorem mem_affineSectionsToFractionField_range_of_ideal_pow_mul
    (U : (Spec (.of T)).Opens) [Nonempty U] (J : Ideal T) (n : ℕ) (z : N)
    (hU : ∀ x : U, ¬ J ≤ x.1.asIdeal)
    (hz : ∀ t ∈ J ^ n, ∃ a : T, algebraMap T N t * z = algebraMap T N a) :
    z ∈ (affineSectionsToFractionField (N := N) U).range := by
  apply mem_affineSectionsToFractionField_range_of_localFractions U z
  intro x
  obtain ⟨f, hfJ, hfp⟩ := Set.not_subset.mp (hU x)
  obtain ⟨a, ha⟩ := hz (f ^ n) (Ideal.pow_mem_pow hfJ n)
  exact ⟨a, f ^ n, fun h => hfp (x.1.isPrime.mem_of_pow_mem n h), ha⟩

end

end CollisionIdeals.Planar
