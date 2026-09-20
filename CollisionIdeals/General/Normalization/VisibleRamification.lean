import CollisionIdeals.General.Normalization.Diagram
import CollisionIdeals.General.Normalization.Finiteness
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# Visible ramification on conjugate polynomial sheets

The results in this file are dimension-independent.  They turn the
scheme-theoretic étaleness of the marked affine-space sheet into the
statement that every conjugate center with nontrivial inertia lies in the
deleted normalization boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k]
variable {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

/--
Formal unramifiedness survives passage from a ring map to the induced map
between local rings at a prime.
-/
lemma ringHom_formallyUnramified_localRingHom
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FormallyUnramified)
    (J : Ideal S) [J.IsPrime] :
    (Localization.localRingHom (J.comap f) J f rfl).FormallyUnramified := by
  algebraize [f, Localization.localRingHom (J.comap f) J f rfl]
  haveI : Algebra.FormallyUnramified R S := hf
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime J) :=
    inferInstance
  haveI : IsScalarTower R
      (Localization.AtPrime (J.comap (algebraMap R S)))
      (Localization.AtPrime J) :=
    .of_algebraMap_eq fun x ↦
      (Localization.localRingHom_to_map _ _ _ rfl x).symm
  change Algebra.FormallyUnramified
    (Localization.AtPrime (J.comap f)) (Localization.AtPrime J)
  exact Algebra.FormallyUnramified.of_restrictScalars R
    (Localization.AtPrime (J.comap (algebraMap R S)))
    (Localization.AtPrime J)

/--
Let `j : U ⟶ X` be an open immersion between affine schemes.  If the
composite `U ⟶ X ⟶ Spec R` is formally unramified, then `X` is unramified
over `R` at every point represented by `U`.
-/
lemma isUnramifiedAt_of_openImmersion_comp_formallyUnramified
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C] [Algebra R C]
    (j : Spec (.of A) ⟶ Spec (.of C)) [IsOpenImmersion j]
    [AlgebraicGeometry.FormallyUnramified
      (j ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)))]
    (x : Spec (.of A)) :
    Algebra.IsUnramifiedAt R (j.base x).asIdeal := by
  let q := j.base x
  let p := Spec.map (CommRingCat.ofHom (algebraMap R C))
  have hcomp :
      RingHom.FormallyUnramified ((j ≫ p).stalkMap x).hom :=
    HasRingHomProperty.stalkMap
      (P := @AlgebraicGeometry.FormallyUnramified)
      ringHom_formallyUnramified_localRingHom
      (inferInstance :
        AlgebraicGeometry.FormallyUnramified (j ≫ p)) x
  have hpstalk :
      RingHom.FormallyUnramified (p.stalkMap q).hom := by
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.FormallyUnramified.respectsIso.cancel_right_isIso] at hcomp
    exact hcomp
  have hlocal :
      RingHom.FormallyUnramified
        (Localization.localRingHom
          (q.asIdeal.comap (algebraMap R C)) q.asIdeal
          (algebraMap R C) rfl) :=
    (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso
        (CommRingCat.ofHom (algebraMap R C)) q)).mp hpstalk
  have hbase :
      RingHom.FormallyUnramified
        (algebraMap R
          (Localization.AtPrime
            (q.asIdeal.comap (algebraMap R C)))) := by
    rw [RingHom.formallyUnramified_algebraMap]
    exact Algebra.FormallyUnramified.of_isLocalization
      (q.asIdeal.comap (algebraMap R C)).primeCompl
  have htotal :
      RingHom.FormallyUnramified
        ((Localization.localRingHom
          (q.asIdeal.comap (algebraMap R C)) q.asIdeal
          (algebraMap R C) rfl).comp
            (algebraMap R
              (Localization.AtPrime
                (q.asIdeal.comap (algebraMap R C))))) :=
    RingHom.FormallyUnramified.stableUnderComposition
      (algebraMap R
        (Localization.AtPrime
          (q.asIdeal.comap (algebraMap R C))))
      (Localization.localRingHom
        (q.asIdeal.comap (algebraMap R C)) q.asIdeal
        (algebraMap R C) rfl)
      hbase hlocal
  rw [show
      (Localization.localRingHom
        (q.asIdeal.comap (algebraMap R C)) q.asIdeal
        (algebraMap R C) rfl).comp
          (algebraMap R
            (Localization.AtPrime
              (q.asIdeal.comap (algebraMap R C)))) =
        algebraMap R (Localization.AtPrime q.asIdeal) by
      ext y
      exact Localization.localRingHom_to_map _ _ _ rfl y] at htotal
  change Algebra.FormallyUnramified R
    (Localization.AtPrime q.asIdeal)
  exact RingHom.formallyUnramified_algebraMap.mp htotal

/-- The ramification index at a prime, computed after localizing the
target at that prime. -/
noncomputable def localRamificationIndex
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] : ℕ :=
  Ideal.ramificationIdx (algebraMap R (Localization.AtPrime P))
    (P.under R) (IsLocalRing.maximalIdeal (Localization.AtPrime P))

/-- At a nonzero unramified prime, the ramification index computed in the
actual local ring is one. In higher dimensions this local index must not
be replaced by an index computed using global ordinary ideal powers. -/
theorem localRamificationIndex_eq_one_of_isUnramifiedAt
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [IsNoetherianRing S] [Algebra.EssFiniteType R S]
    (P : Ideal S) [P.IsPrime] [Algebra.IsUnramifiedAt R P]
    (hP : P ≠ ⊥) :
    localRamificationIndex (R := R) P = 1 := by
  let A := Localization.AtPrime P
  change Ideal.ramificationIdx (algebraMap R A)
    (P.under R) (IsLocalRing.maximalIdeal A) = 1
  have hmap : (P.under R).map (algebraMap R A) = IsLocalRing.maximalIdeal A :=
    ((Algebra.isUnramifiedAt_iff_map_eq R (P.under R) P).mp inferInstance).2
  refine Ideal.ramificationIdx_spec ?_ ?_
  · rw [pow_one]
    exact le_of_eq hmap
  intro h
  rw [hmap, show 1 + 1 = 2 from rfl, pow_two] at h
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
    (IsNoetherian.noetherian _) h (IsLocalRing.maximalIdeal_le_jacobson _)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P A,
    Ideal.map_eq_bot_iff_of_injective] at hbot
  · exact hP hbot
  · exact IsLocalization.injective A P.primeCompl_le_nonZeroDivisors

/-- The local-index-one theorem specialized to an arbitrary prime of the
finite intermediate normalization, before choosing any conjugate center. -/
theorem polynomialIntermediateNormalization_localRamificationIndex_eq_one
    (hFinite : IsPolynomialIntermediateNormalizationFinite F)
    (P : Ideal (PolynomialIntermediateNormalizationRing F)) [P.IsPrime]
    (hUnram : Algebra.IsUnramifiedAt (A := PolynomialIntermediateNormalizationRing F)
      (PolynomialImageAlgebra F) P)
    (hP : P ≠ ⊥) :
    localRamificationIndex (R := PolynomialImageAlgebra F)
      (S := PolynomialIntermediateNormalizationRing F) P = 1 := by
  letI : Module.Finite (PolynomialImageAlgebra F)
      (PolynomialIntermediateNormalizationRing F) := hFinite
  letI : IsNoetherianRing (PolynomialImageAlgebra F) :=
    polynomialImageAlgebra_isNoetherianRing F
  letI : IsNoetherianRing (PolynomialIntermediateNormalizationRing F) :=
    IsNoetherianRing.of_finite (PolynomialImageAlgebra F)
      (PolynomialIntermediateNormalizationRing F)
  letI : Algebra.IsUnramifiedAt (A := PolynomialIntermediateNormalizationRing F)
      (PolynomialImageAlgebra F) P := hUnram
  with_reducible
    exact localRamificationIndex_eq_one_of_isUnramifiedAt
      (R := PolynomialImageAlgebra F) (S := PolynomialIntermediateNormalizationRing F) P hP

namespace PolynomialNormalizationDiagram

variable
    (D : PolynomialNormalizationDiagram (F := F) (N := N))

/-- The actual prime of `X̄` realizing one double-coset sheet class. -/
def centerPrime
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) :
    Ideal (PolynomialIntermediateNormalizationRing F) :=
  (D.centerAtClass E q).asIdeal

instance centerPrime_isPrime
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) :
    (D.centerPrime E q).IsPrime :=
  (D.centerAtClass E q).isPrime

/-- A conjugate center over a ramified divisor is nonzero. This follows
from integrality and the common base center; it is not an extra
ramification hypothesis. -/
theorem centerPrime_ne_bot
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) : D.centerPrime E q ≠ ⊥ := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  have hE : E.1.asIdeal ≠ ⊥ := by
    intro hzero
    have hheight : Ideal.height
        (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) E.1.asIdeal = 1 := by
      rw [Ideal.height_eq_primeHeight, E.2.1]
    simp [hzero] at hheight
  have hbase := Ideal.under_ne_bot (PolynomialImageAlgebra F)
    (B := PolynomialNormalizationInExtensionRing (F := F) (N := N))
    (P := E.1.asIdeal) hE
  have hover :
      (D.centerPrime E q).under (PolynomialImageAlgebra F) =
        E.1.asIdeal.under (PolynomialImageAlgebra F) :=
    congrArg PrimeSpectrum.asIdeal (D.centerAtClass_mapsToBase E q)
  intro hzero
  rw [hzero, Ideal.under_bot (PolynomialImageAlgebra F)
    (PolynomialIntermediateNormalizationRing F)] at hover
  exact hbase hover.symm

/--
The geometric ramification index of the prime on `X̄` selected by a
double-coset class, computed in the local ring at that prime. Localizing
the target is essential: global ordinary prime-ideal powers need not
compute divisorial order in dimension greater than one.
-/
noncomputable def geometricRamificationIndex
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) : ℕ :=
  localRamificationIndex
    (R := PolynomialImageAlgebra F) (S := PolynomialIntermediateNormalizationRing F)
    (D.centerPrime E q)

/--
The valuation-theoretic realization of the selected double-coset centers.

It records nonzero selected centers and identifies their local
ramification indices with the standard group indices.
-/
structure ConjugateRamificationRealization : Prop where
  center_ne_bot :
    ∀ E q, D.centerPrime E q ≠ ⊥
  inertiaIndex_eq_geometricRamificationIndex :
    ∀ E q,
      D.inertiaIndex E q =
        D.geometricRamificationIndex E q

/-- Only the inertia/local-index comparison remains to build the
ramification realization: nonzero centers follow from the diagram. -/
theorem ConjugateRamificationRealization.ofIndexEquality
    (hindex : ∀ E q, D.inertiaIndex E q = D.geometricRamificationIndex E q) :
    D.ConjugateRamificationRealization :=
  ⟨D.centerPrime_ne_bot, hindex⟩

/--
An actual conjugate center that remains in the affine-space open sheet is
unramified over the base.
-/
theorem centerPrime_isUnramifiedAt_of_visible
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E)
    (hEtale : Etale (polynomialSourceToImageBase F))
    (hVisible : D.ConjugateCenterVisible E q) :
    Algebra.IsUnramifiedAt
      (A := PolynomialIntermediateNormalizationRing F)
      (PolynomialImageAlgebra F) (D.centerPrime E q) := by
  letI :
      IsOpenImmersion
        (polynomialSourceToIntermediateNormalization F) :=
    D.cover.intermediateOpen
  letI : Etale (polynomialSourceToImageBase F) := hEtale
  haveI : AlgebraicGeometry.FormallyUnramified
      (polynomialSourceToIntermediateNormalization F ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap
            (PolynomialImageAlgebra F)
            (PolynomialIntermediateNormalizationRing F)))) := by
    change AlgebraicGeometry.FormallyUnramified
      (polynomialSourceToIntermediateNormalization F ≫
        polynomialIntermediateNormalizationToBase F)
    rw [polynomialSourceToIntermediateNormalization_comp_toBase]
    infer_instance
  rcases hVisible with ⟨x, hx⟩
  change Algebra.IsUnramifiedAt
    (PolynomialImageAlgebra F) (D.centerAtClass E q).asIdeal
  rw [← hx]
  exact
    isUnramifiedAt_of_openImmersion_comp_formallyUnramified
      (polynomialSourceToIntermediateNormalization F) x

/-- An unramified conjugate center has local geometric index one. -/
theorem geometricRamificationIndex_eq_one_of_isUnramifiedAt
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E)
    (hUnram : Algebra.IsUnramifiedAt (A := PolynomialIntermediateNormalizationRing F)
      (PolynomialImageAlgebra F) (D.centerPrime E q)) :
    D.geometricRamificationIndex E q = 1 := by
  unfold geometricRamificationIndex
  with_reducible
    exact polynomialIntermediateNormalization_localRamificationIndex_eq_one
      (F := F) D.cover.finiteIntermediateModel (D.centerPrime E q) hUnram
      (D.centerPrime_ne_bot E q)

/-- At a visible conjugate center, étaleness forces local geometric
ramification index one. -/
theorem geometricRamificationIndex_eq_one_of_visible
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E)
    (hEtale : Etale (polynomialSourceToImageBase F))
    (hVisible : D.ConjugateCenterVisible E q) :
    D.geometricRamificationIndex E q = 1 :=
  D.geometricRamificationIndex_eq_one_of_isUnramifiedAt E q
    (D.centerPrime_isUnramifiedAt_of_visible E q hEtale hVisible)

/--
Étaleness sends a conjugate center with nontrivial relative inertia into
the deleted boundary.
-/
theorem ramifiedCenter_mem_boundary
    (R : D.ConjugateRamificationRealization)
    (hEtale : Etale (polynomialSourceToImageBase F))
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E)
    (hq : D.inertiaIndex E q ≠ 1) :
    D.centerAtClass E q ∈
      polynomialIntermediateNormalizationBoundary F := by
  change
    D.centerAtClass E q ∉
      Set.range (polynomialSourceToIntermediateNormalization F).base
  intro hVisible
  apply hq
  rw [R.inertiaIndex_eq_geometricRamificationIndex]
  exact
    D.geometricRamificationIndex_eq_one_of_visible
      E q hEtale hVisible

/--
The ramification realization and étaleness place every positive-index
conjugate center in the deleted boundary.
-/
theorem ramifiedConjugateCentersInBoundary
    (R : D.ConjugateRamificationRealization)
    (hEtale : Etale (polynomialSourceToImageBase F)) :
    D.RamifiedConjugateCentersInBoundary := by
  intro E q hq
  exact D.ramifiedCenter_mem_boundary R hEtale E q hq

end PolynomialNormalizationDiagram

end

end CollisionIdeals
