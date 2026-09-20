import CollisionIdeals.Planar.Boundary.Separation
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Prime-order reduction for planar boundary separation

The fixed--moving ideal grows with its subgroup.  Cauchy's theorem therefore
reduces separation for every nontrivial subgroup to the prime-order case
used by the manuscript's secant--frame landing statement.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

local instance : Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

/-- Enlarging the subgroup can only add moved sheets. -/
theorem movingBoundaryIdeal_mono
    {D : NormalizationDiagram (F := F) (N := N)}
    (boundaryIdeal : NormalizationGaloisGroup D →
      Ideal (GaloisNormalizationRing (F := F) (N := N)))
    {C C' : Subgroup (NormalizationGaloisGroup D)} (h : C ≤ C') :
    movingBoundaryIdeal boundaryIdeal C ≤ movingBoundaryIdeal boundaryIdeal C' := by
  rw [movingBoundaryIdeal_le_iff]
  intro g hg
  exact le_iSup_of_le g (le_iSup_of_le (fun h' => hg (h.trans h')) le_rfl)

/-- Both the fixed-locus and moving-boundary summands grow with the subgroup. -/
theorem fixedMovingBoundaryIdeal_mono
    {D : NormalizationDiagram (F := F) (N := N)}
    {C C' : Subgroup (NormalizationGaloisGroup D)} (h : C ≤ C') :
    fixedMovingBoundaryIdeal D C ≤ fixedMovingBoundaryIdeal D C' :=
  sup_le_sup (fixedLocusIdeal_mono h)
    (movingBoundaryIdeal_mono (pulledBackConjugateBoundaryIdeal D) h)

/-- Every nontrivial subgroup of the finite normalization Galois group
contains a subgroup of prime order. -/
theorem exists_primeOrder_subgroup
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) (hC : C ≠ ⊥) :
    ∃ C' : Subgroup (NormalizationGaloisGroup D),
      C' ≤ C ∧ C' ≠ ⊥ ∧ (Nat.card C').Prime := by
  letI : Finite (NormalizationGaloisGroup D) := D.cover.normalClosure.finiteGaloisGroup
  have hcard : 1 < Nat.card C := C.one_lt_card_iff_ne_bot.mpr hC
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hcard)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := C) p hpdvd
  let C' : Subgroup (NormalizationGaloisGroup D) := Subgroup.zpowers (g : NormalizationGaloisGroup D)
  have hC'card : Nat.card C' = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg]
  refine ⟨C', Subgroup.zpowers_le.mpr g.property, ?_, ?_⟩
  · apply C'.one_lt_card_iff_ne_bot.mp
    rw [hC'card]
    exact hp.one_lt
  · simpa only [hC'card] using hp

/-- Prime-order separation is enough for the all-subgroup boundary
condition consumed by the planar purity endgame. -/
theorem boundarySeparation_of_primeOrder
    (D : NormalizationDiagram (F := F) (N := N))
    (hPrimeSep :
      ∀ (C : Subgroup (NormalizationGaloisGroup D)), C ≠ ⊥ →
        (Nat.card C).Prime →
        ∀ p : PrimeSpectrum (GaloisNormalizationRing (F := F) (N := N)),
          p.asIdeal.primeHeight = 1 →
          ¬ fixedMovingBoundaryIdeal D C ≤ p.asIdeal) :
    PlanarBoundarySeparation D := by
  intro C hC p hp hJ
  obtain ⟨C', hsub, hC', hprime⟩ := exists_primeOrder_subgroup D C hC
  exact hPrimeSep C' hC' hprime p hp ((fixedMovingBoundaryIdeal_mono hsub).trans hJ)

end

end CollisionIdeals.Planar
