import CollisionIdeals.General.Normalization.BaseTransversality
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Lean.Elab.Tactic.Omega

/-!
# Finite polynomial-degree stages preserved by affine generator derivatives

The stage is the image of Mathlib's existing `restrictTotalDegree` under
polynomial evaluation. A derivation whose generator values are represented
by affine-linear polynomials preserves every such finite coefficient-field
stage. No independence of the chosen algebra generators is required.

This file does not assert that arbitrary Keller frames have affine-linear
generator values. That degree condition is the explicit application input.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open MvPolynomial

variable {k E σ : Type*} [Field k] [CommRing E] [Algebra k E]

/-- The ordinary coefficient-field image of a bounded polynomial-degree
submodule. The evaluated algebra may have relations among its generators. -/
def evaluationDegreeStage (k : Type*) [Field k] {E σ : Type*}
    [CommRing E] [Algebra k E] (x : σ → E) (m : ℕ) : Submodule k E :=
  (restrictTotalDegree σ k m).map (aeval x).toLinearMap

instance evaluationDegreeStage_finite [Finite σ] (x : σ → E) (m : ℕ) :
    Module.Finite k (evaluationDegreeStage k x m) := by
  dsimp only [evaluationDegreeStage]
  infer_instance

/-- Every evaluated polynomial belongs to the stage of its own total degree. -/
theorem aeval_mem_evaluationDegreeStage (x : σ → E) (P : MvPolynomial σ k) :
    aeval x P ∈ evaluationDegreeStage k x P.totalDegree := by
  exact ⟨P, (mem_restrictTotalDegree σ P.totalDegree P).mpr le_rfl, rfl⟩

theorem evaluationDegreeStage_mono (x : σ → E) {m n : ℕ} (hmn : m ≤ n) :
    evaluationDegreeStage k x m ≤ evaluationDegreeStage k x n := by
  rintro y ⟨P, hP, rfl⟩
  refine ⟨P, ?_, rfl⟩
  exact (mem_restrictTotalDegree σ n P).mpr
    (((mem_restrictTotalDegree σ m P).mp hP).trans hmn)

/-- The polynomial-degree stages cover exactly the existing generated algebra. -/
theorem mem_adjoin_range_iff_exists_evaluationDegreeStage
    (x : σ → E) (z : E) :
    z ∈ Algebra.adjoin k (Set.range x) ↔
      ∃ m : ℕ, z ∈ evaluationDegreeStage k x m := by
  constructor
  · intro hz
    rw [Algebra.adjoin_range_eq_range_aeval] at hz
    obtain ⟨P, rfl⟩ := hz
    exact ⟨P.totalDegree, aeval_mem_evaluationDegreeStage x P⟩
  · rintro ⟨m, P, hP, rfl⟩
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨P, rfl⟩

section AffineLift

variable [Fintype σ]

/-- The polynomial derivation with prescribed polynomial generator values. -/
def polynomialGeneratorDerivation (v : σ → MvPolynomial σ k) :
    Derivation k (MvPolynomial σ k) (MvPolynomial σ k) :=
  ∑ i : σ, v i • pderiv i

omit [Fintype σ] in
private theorem sum_derivations_apply {ι : Type*} (s : Finset ι)
    (D : ι → Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (P : MvPolynomial σ k) :
    (∑ i ∈ s, D i) P = ∑ i ∈ s, D i P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Derivation.zero_apply]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Derivation.add_apply, ih, Finset.sum_insert hi]

theorem polynomialGeneratorDerivation_apply
    (v : σ → MvPolynomial σ k) (P : MvPolynomial σ k) :
    polynomialGeneratorDerivation v P = ∑ i : σ, v i * pderiv i P := by
  rw [polynomialGeneratorDerivation, sum_derivations_apply]
  simp only [Derivation.smul_apply, smul_eq_mul]

@[simp]
theorem polynomialGeneratorDerivation_X
    (v : σ → MvPolynomial σ k) (i : σ) :
    polynomialGeneratorDerivation v (X i) = v i := by
  classical
  rw [polynomialGeneratorDerivation_apply]
  simp [pderiv_X, Pi.single_apply]

/-- Affine-linear generator values do not increase total polynomial degree. -/
theorem polynomialGeneratorDerivation_totalDegree_le
    (v : σ → MvPolynomial σ k) (hv : ∀ i : σ, (v i).totalDegree ≤ 1)
    (P : MvPolynomial σ k) :
    (polynomialGeneratorDerivation v P).totalDegree ≤ P.totalDegree := by
  classical
  rw [polynomialGeneratorDerivation_apply]
  apply totalDegree_finsetSum_le
  intro i hi
  by_cases hzero : pderiv i P = 0
  · simp only [hzero, mul_zero, totalDegree_zero]
    exact Nat.zero_le _
  · have hpartial := totalDegree_pderiv_lt i P hzero
    have hproduct := totalDegree_mul (v i) (pderiv i P)
    have hvi := hv i
    omega

/-- A derivation on an evaluated algebra agrees with the polynomial lift
whenever the stated generator identities hold. -/
theorem derivation_aeval_eq_polynomialGeneratorDerivation
    (x : σ → E) (delta : Derivation k E E)
    (v : σ → MvPolynomial σ k)
    (hGenerator : ∀ i : σ, delta (x i) = aeval x (v i))
    (P : MvPolynomial σ k) :
    delta (aeval x P) = aeval x (polynomialGeneratorDerivation v P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, map_add, aeval_X, Derivation.leibniz, smul_eq_mul,
        polynomialGeneratorDerivation_X, hGenerator, hP]

/-- Evaluation images of bounded degree are preserved by the actual
derivation when its generator values have affine-linear representatives. -/
theorem derivation_mem_evaluationDegreeStage
    (x : σ → E) (delta : Derivation k E E)
    (v : σ → MvPolynomial σ k)
    (hv : ∀ i : σ, (v i).totalDegree ≤ 1)
    (hGenerator : ∀ i : σ, delta (x i) = aeval x (v i))
    (m : ℕ) {z : E} (hz : z ∈ evaluationDegreeStage k x m) :
    delta z ∈ evaluationDegreeStage k x m := by
  obtain ⟨P, hP, rfl⟩ := hz
  change delta (aeval x P) ∈ evaluationDegreeStage k x m
  rw [derivation_aeval_eq_polynomialGeneratorDerivation x delta v hGenerator]
  refine ⟨polynomialGeneratorDerivation v P, ?_, rfl⟩
  apply (mem_restrictTotalDegree σ m _).mpr
  exact (polynomialGeneratorDerivation_totalDegree_le v hv P).trans
    ((mem_restrictTotalDegree σ m P).mp hP)

end AffineLift

end

end CollisionIdeals
