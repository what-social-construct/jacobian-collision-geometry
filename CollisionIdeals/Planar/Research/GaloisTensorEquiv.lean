import CollisionIdeals.Planar.Research.GaloisTensor
import CollisionIdeals.Planar.Research.GaloisTrace

/-!
# The tensor comparison over the actual invariant base

Surjectivity of the canonical tensor map supplies a finite delta frame.
The resulting trace-dual identity reconstructs every tensor from its
graph evaluations, proving injectivity as well. No fraction-field rank
argument, separability input, or boundary-vanishing assumption is used.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar.Research.FiniteGroupCover

open scoped TensorProduct

noncomputable section

variable (R S G : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [Fintype G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- A finite frame reconstructs tensors from their graph evaluations.
The definition is additive and uses no choice of a field basis. -/
def frameReconstruction {n : ℕ} (a b : Fin n → S) :
    (G → S) →+ S ⊗[R] S where
  toFun f := ∑ i, (∑ g : G, (g • b i) * f g) ⊗ₜ[R] a i
  map_zero' := by simp
  map_add' f h := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul]

variable [Algebra.IsInvariant R S G]

/-- The finite trace-dual identity reconstructs each pure tensor. -/
theorem frameReconstruction_canonicalMap_tmul
    [DecidableEq G]
    (hinj : Function.Injective (algebraMap R S)) {n : ℕ} (a b : Fin n → S)
    (hdelta : ∀ g : G, ∑ i, a i * (g • b i) = if g = 1 then 1 else 0)
    (x y : S) :
    frameReconstruction R S G a b (canonicalMap R S G (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] y := by
  classical
  change (∑ i, (∑ g : G, (g • b i) * (x * (g • y))) ⊗ₜ[R] a i) = _
  have hcoeff (i : Fin n) :
      (∑ g : G, (g • b i) * (x * (g • y))) =
        x * algebraMap R S (groupTrace R S G hinj (b i * y)) := by
    rw [algebraMap_groupTrace, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [smul_mul']
    ring
  simp_rw [hcoeff]
  calc
    (∑ i, (x * algebraMap R S (groupTrace R S G hinj (b i * y))) ⊗ₜ[R] a i) =
        ∑ i, x ⊗ₜ[R] (groupTrace R S G hinj (b i * y) • a i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
    _ = x ⊗ₜ[R] (∑ i, groupTrace R S G hinj (b i * y) • a i) := by
      rw [TensorProduct.tmul_sum]
    _ = x ⊗ₜ[R] y := by
      rw [sum_groupTrace_smul_eq R S G hinj a b hdelta y]

/-- Once the scalar ring is the actual invariant base, surjectivity of
the canonical tensor map also forces its injectivity. -/
theorem canonicalMap_injective
    (hinj : Function.Injective (algebraMap R S))
    (hsurj : Function.Surjective (canonicalMap R S G)) :
    Function.Injective (canonicalMap R S G) := by
  classical
  obtain ⟨n, a, b, hdelta⟩ :=
    exists_deltaFrame_of_canonicalMap_surjective R S G hsurj
  have hleft : Function.LeftInverse (frameReconstruction R S G a b)
      (canonicalMap R S G) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        exact frameReconstruction_canonicalMap_tmul R S G hinj a b hdelta x y
    | add t u ht hu => simp only [map_add, ht, hu]
  exact hleft.injective

/-- The canonical Galois tensor equivalence, constructed from its
surjectivity over the actual invariant base. -/
def canonicalEquiv
    (hinj : Function.Injective (algebraMap R S))
    (hsurj : Function.Surjective (canonicalMap R S G)) :
    S ⊗[R] S ≃ₐ[R] (G → S) :=
  AlgEquiv.ofBijective (canonicalMap R S G)
    ⟨canonicalMap_injective R S G hinj hsurj, hsurj⟩

@[simp]
theorem canonicalEquiv_apply
    (hinj : Function.Injective (algebraMap R S))
    (hsurj : Function.Surjective (canonicalMap R S G)) (t : S ⊗[R] S) :
    canonicalEquiv R S G hinj hsurj t = canonicalMap R S G t := rfl

@[simp]
theorem canonicalEquiv_tmul
    (hinj : Function.Injective (algebraMap R S))
    (hsurj : Function.Surjective (canonicalMap R S G)) (a b : S) (g : G) :
    canonicalEquiv R S G hinj hsurj (a ⊗ₜ[R] b) g = a * (g • b) := rfl

end

end CollisionIdeals.Planar.Research.FiniteGroupCover
