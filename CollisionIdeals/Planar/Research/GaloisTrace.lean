import CollisionIdeals.Planar.Research.GaloisTensor
import Mathlib.RingTheory.Invariant.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Finite group trace frames

A finite delta frame for the canonical Galois tensor map supplies a finite
trace-dual frame over the actual invariant ring, hence a split finite-free
presentation and projectivity. No averaging denominator or flatness is
assumed.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar.Research.FiniteGroupCover

noncomputable section

open scoped TensorProduct

variable (R S G : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [Fintype G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- The sum over the finite group action, before descending to the base. -/
def orbitSum : S →ₗ[R] S :=
  ∑ g : G, (MulSemiringAction.toAlgHom R S g).toLinearMap

@[simp]
theorem orbitSum_apply (x : S) : orbitSum R S G x = ∑ g : G, g • x := by
  simp [orbitSum]

theorem smul_orbitSum (g : G) (x : S) : g • orbitSum R S G x = orbitSum R S G x := by
  simp only [orbitSum_apply, Finset.smul_sum, smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

omit [Fintype G] in
/-- A preimage of the identity delta function supplies a finite tensor
frame; it is not assumed as an additional certificate. -/
theorem exists_deltaFrame_of_canonicalMap_surjective
    [DecidableEq G]
    (hsurj : Function.Surjective (canonicalMap R S G)) :
    ∃ (n : ℕ) (a b : Fin n → S),
      ∀ g : G, ∑ i, a i * (g • b i) = if g = 1 then 1 else 0 := by
  classical
  obtain ⟨t, ht⟩ := hsurj (fun g : G => if g = 1 then 1 else 0)
  obtain ⟨n, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq t
  refine ⟨n, a, b, fun g => ?_⟩
  have hg := congrFun ht g
  rw [hab] at hg
  simpa only [map_sum, Finset.sum_apply, canonicalMap_tmul] using hg

variable [Algebra.IsInvariant R S G]

/-- The orbit sum as an element of the invariant base. Injectivity is used
only when packaging its linearity, not when choosing its value. -/
def groupTraceValue (x : S) : R :=
  Classical.choose (Algebra.IsInvariant.isInvariant (orbitSum R S G x)
    (smul_orbitSum R S G · x))

@[simp]
theorem algebraMap_groupTraceValue (x : S) :
    algebraMap R S (groupTraceValue R S G x) = orbitSum R S G x :=
  Classical.choose_spec (Algebra.IsInvariant.isInvariant (orbitSum R S G x)
    (smul_orbitSum R S G · x))

/-- The finite group trace, valued in the actual invariant base. -/
def groupTrace (hinj : Function.Injective (algebraMap R S)) : S →ₗ[R] R where
  toFun := groupTraceValue R S G
  map_add' x y := by
    apply hinj
    simp only [map_add, algebraMap_groupTraceValue]
  map_smul' r x := by
    apply hinj
    change algebraMap R S (groupTraceValue R S G (r • x)) =
      algebraMap R S (r * groupTraceValue R S G x)
    rw [map_mul, algebraMap_groupTraceValue, algebraMap_groupTraceValue]
    simpa only [Algebra.smul_def] using (orbitSum R S G).map_smul r x

@[simp]
theorem algebraMap_groupTrace (hinj : Function.Injective (algebraMap R S)) (x : S) :
    algebraMap R S (groupTrace R S G hinj x) = ∑ g : G, g • x := by
  exact (algebraMap_groupTraceValue R S G x).trans (orbitSum_apply R S G x)

/-- A finite delta frame becomes a trace-dual identity over the invariant
base. The frame need not be a basis. -/
theorem sum_groupTrace_smul_eq
    [DecidableEq G]
    (hinj : Function.Injective (algebraMap R S)) {n : ℕ} (a b : Fin n → S)
    (hdelta : ∀ g : G, ∑ i, a i * (g • b i) = if g = 1 then 1 else 0)
    (x : S) :
    ∑ i, groupTrace R S G hinj (b i * x) • a i = x := by
  classical
  simp only [Algebra.smul_def, algebraMap_groupTrace, smul_mul', Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    ∑ g : G, ∑ i, (g • b i * (g • x)) * a i =
        ∑ g : G, (∑ i, a i * (g • b i)) * (g • x) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = x := by simp [hdelta]

/-- The delta frame makes the algebra a direct summand of a finite free
module over its actual invariant base. -/
theorem projective_of_deltaFrame
    [DecidableEq G]
    (hinj : Function.Injective (algebraMap R S))
    (hdelta : ∃ (n : ℕ) (a b : Fin n → S),
      ∀ g : G, ∑ i, a i * (g • b i) = if g = 1 then 1 else 0) :
    Module.Projective R S := by
  classical
  obtain ⟨n, a, b, hab⟩ := hdelta
  let sectionMap : S →ₗ[R] (Fin n → R) :=
    LinearMap.pi fun i => (groupTrace R S G hinj).comp (LinearMap.mulLeft R (b i))
  let retraction : (Fin n → R) →ₗ[R] S :=
    { toFun := fun v => ∑ i, v i • a i
      map_add' := by
        intro v w
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r v
        simp [smul_smul, Finset.smul_sum] }
  apply Module.Projective.of_split sectionMap retraction
  ext x
  exact sum_groupTrace_smul_eq R S G hinj a b hab x

/-- Surjectivity of the canonical Galois tensor map proves projectivity
over the actual invariant base, without a flatness premise. -/
theorem projective_of_canonicalMap_surjective
    (hinj : Function.Injective (algebraMap R S))
    (hsurj : Function.Surjective (canonicalMap R S G)) :
    Module.Projective R S := by
  classical
  exact projective_of_deltaFrame R S G hinj
    (exists_deltaFrame_of_canonicalMap_surjective R S G hsurj)

end

end CollisionIdeals.Planar.Research.FiniteGroupCover
