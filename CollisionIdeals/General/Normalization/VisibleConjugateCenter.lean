import CollisionIdeals.General.Keller.DivisorVisibility
import CollisionIdeals.General.Normalization.ConjugateCenters
import CollisionIdeals.General.Normalization.VisibleRamification
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Invariant.Basic

/-!
# A visible conjugate center above every normalization divisor

Lying-over and Galois transitivity realize every intermediate normalization
prime over a fixed base prime as a conjugate center of a chosen full
normalization prime. The Keller source-divisor theorem then supplies at
least one visible conjugate center above every normalization divisor.

The conclusion is existential. It does not make all conjugate centers
visible and does not prove that the full normalization is unramified.
For a supplied normalization diagram and ramification realization, the
visible center gives a sheet fixed by inertia, not triviality of inertia.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open scoped Pointwise

universe u

section IntegralClosure

variable {B K L N : Type u}
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
  [Field K] [Field L] [Field N]
  [Algebra B K] [IsFractionRing B K]
  [Algebra K L] [Algebra K N] [Algebra B L] [Algebra B N]
  [IsScalarTower B K L] [IsScalarTower B K N]
  [FiniteDimensional K N] [IsGalois K N]

/-- Every intermediate normalization prime above the same base prime is
the contraction along some conjugate of the marked field embedding.
Surjectivity is proved by lying-over and Galois transitivity, not assumed. -/
theorem exists_conjugate_integralClosure_prime_comap
    (ι : L →ₐ[K] N)
    (q : Ideal (integralClosure B N)) [q.IsPrime]
    (p : Ideal (integralClosure B L)) [p.IsPrime]
    (hpq : p.under B = q.under B) :
    ∃ g : N ≃ₐ[K] N,
      q.comap (((g.toAlgHom.comp ι).restrictScalars B).mapIntegralClosure).toRingHom = p := by
  let S : Type u := integralClosure B L
  let T : Type u := integralClosure B N
  let G : Type u := N ≃ₐ[K] N
  let f : S →ₐ[B] T := (ι.restrictScalars B).mapIntegralClosure
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower B S T :=
    IsScalarTower.of_algebraMap_eq (fun b => (f.commutes b).symm)
  letI : Algebra.IsIntegral S T := Algebra.IsIntegral.tower_top B
  have hf : Function.Injective (algebraMap S T) := by
    intro x y hxy
    apply Subtype.ext
    apply ι.injective
    exact congrArg Subtype.val hxy
  obtain ⟨Q, hQ, hQp⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := T) p
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hf]; exact bot_le)
  letI : Q.IsPrime := hQ
  have hQbase : Q.under B = p.under B := by
    change Q.comap (algebraMap B T) = p.comap (algebraMap B S)
    rw [IsScalarTower.algebraMap_eq B S T, ← Ideal.comap_comap, hQp]
  letI : SMulCommClass G B N := ⟨fun g b x => by
    simpa only [IsScalarTower.algebraMap_smul] using
      (smul_comm g (algebraMap B K b) x)⟩
  letI : IsFractionRing T N := integralClosure.isFractionRing_of_finite_extension K N
  letI : IsGaloisGroup G B T := IsGaloisGroup.of_isFractionRing G B T K N
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B T G Q q
    (hQbase.trans hpq)
  refine ⟨g, ?_⟩
  ext x
  change g • f x ∈ q ↔ x ∈ p
  rw [hg, Ideal.smul_mem_pointwise_smul_iff]
  exact Iff.of_eq (congrArg (fun I : Ideal S => x ∈ I) hQp)

end IntegralClosure

section Polynomial

variable {k : Type u} [Field k] {n : ℕ} {F : PolynomialSelfMap k n}
  {N : Type u} [Field N] [Algebra (PolynomialMapBaseFunctionField F) N]
  [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

local instance visibleIntermediateBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialIntermediateNormalizationRing F) :=
  (PolynomialIntermediateNormalizationRing F).algebra

/-- The constructed conjugate centers exhaust the intermediate primes over
the selected base prime. No double-coset bijection is needed for existence. -/
theorem exists_polynomialConjugateCenter_eq_of_under_eq
    (D : PolynomialNormalClosureData F N)
    (q : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (p : PrimeSpectrum (PolynomialIntermediateNormalizationRing F))
    (hpq : Ideal.under (PolynomialImageAlgebra F)
        (B := PolynomialIntermediateNormalizationRing F) p.asIdeal =
      Ideal.under (PolynomialImageAlgebra F)
        (B := PolynomialNormalizationInExtensionRing (F := F) (N := N)) q.asIdeal) :
    ∃ g : D.galoisGroup, polynomialConjugateCenter D q g = p := by
  let B : Type u := PolynomialImageAlgebra F
  let K : Type u := PolynomialMapBaseFunctionField F
  letI algebraBK : Algebra B K := OreLocalization.instAlgebra
  letI : SMul B K := algebraBK.toSMul
  letI : Algebra B N := polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : FiniteDimensional K (PolynomialMapSourceFunctionField F) := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : IsGalois K N := IsGalois.mk
  letI : IsIntegrallyClosed B :=
    polynomialImageAlgebra_isIntegrallyClosed_of_finiteDimensional F
  letI : IsScalarTower B K N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨g, hg⟩ := exists_conjugate_integralClosure_prime_comap D.embedding
    q.asIdeal p.asIdeal hpq
  refine ⟨g, PrimeSpectrum.ext ?_⟩
  exact hg

/-- Every height-one full-normalization prime has at least one conjugate
center on the actual polynomial source. Other centers may still be hidden. -/
theorem exists_visible_polynomialConjugateCenter_of_isKeller
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (q : PrimeSpectrum (PolynomialNormalizationInExtensionRing (F := F) (N := N)))
    (hq : Ideal.primeHeight
      (R := PolynomialNormalizationInExtensionRing (F := F) (N := N)) q.asIdeal = 1) :
    ∃ g : D.galoisGroup,
      polynomialConjugateCenter D q g ∈
        Set.range (polynomialSourceToIntermediateNormalization F).base := by
  let p : PrimeSpectrum (PolynomialImageAlgebra F) :=
    ⟨q.asIdeal.under (PolynomialImageAlgebra F), inferInstance⟩
  have hp : p.asIdeal.primeHeight = 1 :=
    polynomialNormalization_primeHeight_under_eq_one D q hq
  obtain ⟨r, _, hr, _⟩ :=
    exists_visible_source_divisor_over_heightOne_of_isKeller F hKeller p hp
  let s : PrimeSpectrum (PolynomialIntermediateNormalizationRing F) :=
    (polynomialSourceToIntermediateNormalization F).base r
  have hs : s.asIdeal.under (PolynomialImageAlgebra F) =
      q.asIdeal.under (PolynomialImageAlgebra F) := by
    have htriangle := congrArg (fun f => f.base r)
      (polynomialSourceToIntermediateNormalization_comp_toBase F)
    have hideals := congrArg PrimeSpectrum.asIdeal htriangle
    change s.asIdeal.under (PolynomialImageAlgebra F) =
      r.asIdeal.under (PolynomialImageAlgebra F) at hideals
    exact hideals.trans hr
  obtain ⟨g, hg⟩ := exists_polynomialConjugateCenter_eq_of_under_eq D q s hs
  exact ⟨g, r, hg.symm⟩

/-- A visible source center supplies one inertia-fixed sheet. The local
ramification realization is explicitly supplied; this theorem does not
construct it or force inertia to fix every sheet. -/
theorem PolynomialNormalizationDiagram.exists_inertiaFixedSheet_of_isKeller
    (D : PolynomialNormalizationDiagram (F := F) (N := N))
    (R : D.ConjugateRamificationRealization) (hKeller : IsKeller F)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    ∃ s : GaloisSheets D.cover.normalClosure.intermediateFixingSubgroup,
      InertiaInvisibleAt
        (inertiaGroupAt (PolynomialMapBaseFunctionField F)
          (D.valuationAt E).valuationRing)
        D.cover.normalClosure.intermediateFixingSubgroup s := by
  obtain ⟨g, hg⟩ := exists_visible_polynomialConjugateCenter_of_isKeller
    D.cover.normalClosure hKeller E.1 E.2.1
  let c : D.sheetClasses E :=
    DoubleCoset.mk
      (decompositionGroupAt (PolynomialMapBaseFunctionField F)
        (D.valuationAt E).valuationRing)
      D.cover.normalClosure.intermediateFixingSubgroup g
  have hc : D.ConjugateCenterVisible E c := by
    change D.centerAtClass E c ∈
      Set.range (polynomialSourceToIntermediateNormalization F).base
    rw [D.centerAtRepresentative]
    exact hg
  have hindex : D.inertiaIndex E c = 1 :=
    (R.inertiaIndex_eq_geometricRamificationIndex E c).trans
      (D.geometricRamificationIndex_eq_one_of_visible E c
        (kellerEtaleBridge F hKeller) hc)
  refine ⟨g • ((1 : D.cover.normalClosure.galoisGroup) :
    GaloisSheets D.cover.normalClosure.intermediateFixingSubgroup), ?_⟩
  exact (inertiaIndexAtRepresentative_eq_one_iff
    (inertiaWithinDecomposition (PolynomialMapBaseFunctionField F)
      (D.valuationAt E).valuationRing)
    D.cover.normalClosure.intermediateFixingSubgroup g).mp hindex

end Polynomial

end

end CollisionIdeals
