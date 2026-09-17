import CollisionIdeals.General.Normalization.Diagram
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

/--
The geometric ramification index of the prime on `X̄` selected by a
double-coset class.
-/
noncomputable def geometricRamificationIndex
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) : ℕ :=
  Ideal.ramificationIdx
    (R := PolynomialImageAlgebra F)
    (S := PolynomialIntermediateNormalizationRing F)
    ((algebraMap
      (PolynomialImageAlgebra F)
      (PolynomialIntermediateNormalizationRing F)) :
        PolynomialImageAlgebra F →+*
          PolynomialIntermediateNormalizationRing F)
    (Ideal.under
      (B := PolynomialIntermediateNormalizationRing F)
      (PolynomialImageAlgebra F) (D.centerPrime E q))
    (D.centerPrime E q)

/--
The valuation-theoretic realization of the selected double-coset centers.

It records that the selected centers are divisorial and that their
geometric ramification indices are the standard group indices.
-/
structure ConjugateRamificationRealization : Prop where
  center_ne_bot :
    ∀ E q, D.centerPrime E q ≠ ⊥
  inertiaIndex_eq_geometricRamificationIndex :
    ∀ E q,
      D.inertiaIndex E q =
        D.geometricRamificationIndex E q

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

/--
At a visible conjugate center, scheme-theoretic étaleness forces the
geometric ramification index to be one.
-/
theorem geometricRamificationIndex_eq_one_of_visible
    (R : D.ConjugateRamificationRealization)
    (E :
      PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E)
    (hEtale : Etale (polynomialSourceToImageBase F))
    (hVisible : D.ConjugateCenterVisible E q) :
    D.geometricRamificationIndex E q = 1 := by
  letI : Module.Finite
      (PolynomialImageAlgebra F)
      (PolynomialIntermediateNormalizationRing F) :=
    D.cover.finiteIntermediateModel
  letI : IsNoetherianRing (PolynomialImageAlgebra F) := by
    unfold PolynomialImageAlgebra polynomialMapImageAlgebra
    infer_instance
  letI :
      IsNoetherianRing (PolynomialIntermediateNormalizationRing F) :=
    IsNoetherianRing.of_finite
      (PolynomialImageAlgebra F)
      (PolynomialIntermediateNormalizationRing F)
  letI : Algebra.IsUnramifiedAt
      (A := PolynomialIntermediateNormalizationRing F)
      (PolynomialImageAlgebra F) (D.centerPrime E q) :=
    D.centerPrime_isUnramifiedAt_of_visible E q hEtale hVisible
  exact
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      (R.center_ne_bot E q)

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
      R E q hEtale hVisible

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
