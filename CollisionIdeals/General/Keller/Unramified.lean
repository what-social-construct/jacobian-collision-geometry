import CollisionIdeals.General.Keller.Basic
import CollisionIdeals.General.GenericFiber.FunctionField
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Unramified.Basic

/-!
The unramified part of the Jacobian criterion for a Keller map, over its
actual coordinate-image algebra.  This proves a consequence of the Keller
condition; it does not assume the scheme-theoretic étaleness bridge.
-/

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

noncomputable section

universe u v

private theorem derivation_sum_apply
    {K : Type u} [Field K] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module K M]
    [Module (SourceRing K (Fin n)) M]
    {ι : Type*} (s : Finset ι)
    (f : ι → Derivation K (SourceRing K (Fin n)) M)
    (p : SourceRing K (Fin n)) :
    (∑ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
    congrFun (map_sum Derivation.coeFnAddMonoidHom f s) p

private theorem derivation_eq_sum_pderiv
    {K : Type u} [Field K] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module K M]
    [Module (SourceRing K (Fin n)) M]
    [IsScalarTower K (SourceRing K (Fin n)) M]
    (D : Derivation K (SourceRing K (Fin n)) M)
    (p : SourceRing K (Fin n)) :
    D p = ∑ i, pderiv i p • D (X i) := by
  classical
  have hD : D = ∑ i,
      (LinearMap.toSpanSingleton (SourceRing K (Fin n)) M (D (X i))).compDer
        (pderiv i) := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [derivation_sum_apply, LinearMap.compDer, Pi.single_apply,
      LinearMap.toSpanSingleton_apply]
  simpa [derivation_sum_apply, LinearMap.compDer,
    LinearMap.toSpanSingleton_apply] using DFunLike.congr_fun hD p

/-- A derivation annihilating the coordinates of a Keller map is zero.
The argument works in every ambient dimension and for arbitrary module values. -/
theorem derivation_eq_zero_of_isKeller
    {K : Type u} [Field K] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module K M]
    [Module (SourceRing K (Fin n)) M]
    [IsScalarTower K (SourceRing K (Fin n)) M]
    (F : PolynomialSelfMap K n) (hKeller : IsKeller F)
    (D : Derivation K (SourceRing K (Fin n)) M)
    (hF : ∀ j, D (F j) = 0) : D = 0 := by
  classical
  obtain ⟨c, hc, hJ⟩ := hKeller
  have hFexpand (j : Fin n) : D (F j) = ∑ k, pderiv k (F j) • D (X k) :=
    derivation_eq_sum_pderiv D (F j)
  have hX (i : Fin n) : D (X i) = 0 := by
    have hsum : ∑ j, (jacobianMatrix F).adjugate i j • D (F j) = 0 := by
      simp [hF]
    simp_rw [hFexpand, Finset.smul_sum, smul_smul] at hsum
    rw [Finset.sum_comm] at hsum
    simp_rw [← Finset.sum_smul] at hsum
    have hcoeff (k : Fin n) :
        (∑ j, (jacobianMatrix F).adjugate i j * pderiv k (F j)) =
          (c • (1 : Matrix (Fin n) (Fin n) (SourceRing K (Fin n)))) i k := by
      change ((jacobianMatrix F).adjugate * jacobianMatrix F) i k = _
      rw [Matrix.adjugate_mul, ← jacobianDet, hJ]
      simp [Matrix.smul_apply, C_mul']
    simp_rw [hcoeff] at hsum
    have hcD : c • D (X i) = 0 := by
      simpa [Matrix.smul_apply, Matrix.one_apply, ite_smul] using hsum
    exact (smul_eq_zero.mp hcD).resolve_left hc
  exact MvPolynomial.derivation_ext (fun i => by simpa using hX i)

/-- The Keller condition makes the source formally unramified over the
coordinate-image algebra. No injectivity claim for the abstract target map
and no supplied étaleness theorem is needed. -/
theorem polynomialSource_formallyUnramified_of_isKeller
    {K : Type u} [Field K] {n : ℕ}
    (F : PolynomialSelfMap K n) (hKeller : IsKeller F) :
    Algebra.FormallyUnramified (polynomialMapImageAlgebra F)
      (SourceRing K (Fin n)) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing K (Fin n)
  let D := KaehlerDifferential.D B A
  have hD : D.restrictScalars K = 0 := by
    apply derivation_eq_zero_of_isKeller F hKeller
    intro j
    exact D.map_algebraMap
      (⟨F j, X j, coordinateAlgHom_X F j⟩ : B)
  constructor
  suffices (⊤ : Submodule A (KaehlerDifferential B A)) ≤ ⊥ from
    (subsingleton_iff_forall_eq 0).mpr fun z => this (by trivial)
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro z ⟨p, rfl⟩
  exact DFunLike.congr_fun hD p

end

end CollisionIdeals
