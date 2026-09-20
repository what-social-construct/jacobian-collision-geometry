import CollisionIdeals.General.Galois.InertiaQuotient
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# Ramification and inertia over a Dedekind base

These are the shared local facts used in the earlier manuscript: residue
separability identifies unramifiedness with index one, and the inertia
cardinality identifies that condition with trivial inertia.

The Dedekind hypotheses belong to the rings obtained after localizing the
normalization construction. They do not justify using global ideal powers
in a higher-dimensional normalization ring. Comparing these ideal inertia
groups with the chosen valuation inertia is a separate step.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

attribute [local instance] Ideal.Quotient.field

section Unramified

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDedekindDomain S] [Algebra.EssFiniteType R S]

/-- The Dedekind unramifiedness criterion with its actual residue-field
hypothesis, rather than a number-ring hypothesis used to derive it. -/
theorem isUnramifiedAt_iff_ramificationIdx_eq_one_of_residueSeparable
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    [Algebra.IsSeparable p.ResidueField P.ResidueField] (hP : P ≠ ⊥) :
    Algebra.IsUnramifiedAt R P ↔
      Ideal.ramificationIdx (algebraMap R S) p P = 1 := by
  have hpP : p.map (algebraMap R S) ≤ P :=
    Ideal.map_le_iff_le_comap.mpr (P.over_def p).le
  rw [Algebra.isUnramifiedAt_iff_map_eq R p P]
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hP hpP
  exact ⟨fun h => he.mpr h.2, fun h => ⟨inferInstance, he.mp h⟩⟩

/-- In residue characteristic zero, an integral Dedekind extension needs
no separately supplied residue-separability certificate. -/
theorem isUnramifiedAt_iff_ramificationIdx_eq_one_of_residueCharZero
    [Algebra.IsIntegral R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    [CharZero p.ResidueField] (hP : P ≠ ⊥) :
    Algebra.IsUnramifiedAt R P ↔
      Ideal.ramificationIdx (algebraMap R S) p P = 1 := by
  letI : Algebra.IsSeparable p.ResidueField P.ResidueField := inferInstance
  exact isUnramifiedAt_iff_ramificationIdx_eq_one_of_residueSeparable p P hP

end Unramified

section Galois

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDedekindDomain R] [IsDedekindDomain S]
  [Module.Finite R S] [Module.IsTorsionFree R S]
  [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]

/-- Inertia cardinality equals the ramification index at the specified
prime, not just the common index of all primes above the base prime. -/
theorem idealInertia_card_eq_ramificationIdx
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (P.inertia G) = Ideal.ramificationIdx (algebraMap R S) p P := by
  exact (Ideal.card_inertia_eq_ramificationIdxIn (G := G) p hp P).trans
    (Ideal.ramificationIdxIn_eq_ramificationIdx p P G)

/-- An unramified prime of a finite Galois Dedekind extension has trivial
inertia, and conversely, when its residue extension is separable. -/
theorem isUnramifiedAt_iff_idealInertia_eq_bot
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Algebra.IsUnramifiedAt R P ↔ P.inertia G = ⊥ := by
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  rw [isUnramifiedAt_iff_ramificationIdx_eq_one_of_residueSeparable p P hP,
    ← idealInertia_card_eq_ramificationIdx (G := G) p hp P, Subgroup.card_eq_one]

/-- Ramification forces nontrivial inertia in the finite Dedekind model. -/
theorem idealInertia_ne_bot_of_not_isUnramifiedAt
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)]
    (hRam : ¬ Algebra.IsUnramifiedAt R P) : P.inertia G ≠ ⊥ :=
  mt (isUnramifiedAt_iff_idealInertia_eq_bot (G := G) p hp P).mpr hRam

/-- The preceding equivalence needs no separability input in residue
characteristic zero. -/
theorem isUnramifiedAt_iff_idealInertia_eq_bot_of_residueCharZero
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [CharZero p.ResidueField] :
    Algebra.IsUnramifiedAt R P ↔ P.inertia G = ⊥ := by
  letI : Algebra.IsSeparable p.ResidueField P.ResidueField := inferInstance
  letI : Algebra.IsSeparable (R ⧸ p) (S ⧸ P) := inferInstance
  exact isUnramifiedAt_iff_idealInertia_eq_bot (G := G) p hp P

end Galois

end

end CollisionIdeals
