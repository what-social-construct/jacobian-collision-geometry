import CollisionIdeals.ComplexThree.Cubic.S3Collision
import Mathlib.FieldTheory.Normal.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open Polynomial

universe u v

variable
    (K : Type u) [Field K]
    (L : Type v) [Field L] [Algebra K L]

/--
The residual factor of a nonnormal separable cubic power-basis extension
is irreducible over the marked-root field.

Indeed, a root in `L` would split the quadratic residual polynomial.  Along
with the marked linear factor, this would split the cubic minimal polynomial
of the generator in `L`; since the generator spans `L`, the extension would
then be normal.
-/
theorem irreducible_minpolyDiv_of_cubic_of_not_normal
    [Algebra.IsSeparable K L]
    (pb : PowerBasis K L)
    (hdegree : pb.dim = 3)
    (hnormal : ¬ Normal K L) :
    Irreducible (minpolyDiv K pb.gen) := by
  letI : Module.Finite K L := pb.finite
  have hqdegree : (minpolyDiv K pb.gen).natDegree = 2 := by
    have h := natDegree_minpolyDiv_succ pb.isIntegral_gen
    rw [pb.natDegree_minpoly, hdegree] at h
    omega
  by_contra hirreducible
  obtain ⟨c₁, c₂, hcoeffZero, hcoeffOne⟩ :=
    ((minpolyDiv_monic pb.isIntegral_gen).not_irreducible_iff_exists_add_mul_eq_coeff
      hqdegree).mp hirreducible
  have hfactor :
      minpolyDiv K pb.gen = (X + C c₁) * (X + C c₂) := by
    rw [(minpolyDiv K pb.gen).as_sum_range_C_mul_X_pow, hqdegree,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      ← hqdegree, (minpolyDiv_monic pb.isIntegral_gen).coeff_natDegree,
      hqdegree, hcoeffZero, hcoeffOne, C_mul, C_add, C_1]
    ring
  apply hnormal
  have hqsplit :
      (minpolyDiv K pb.gen).Splits (RingHom.id L) := by
    rw [hfactor]
    exact Polynomial.splits_mul (RingHom.id L)
      (by simpa [sub_neg_eq_add] using
        Polynomial.splits_X_sub_C (RingHom.id L) (x := -c₁))
      (by simpa [sub_neg_eq_add] using
        Polynomial.splits_X_sub_C (RingHom.id L) (x := -c₂))
  have hmapsplit :
      ((minpoly K pb.gen).map (algebraMap K L)).Splits
        (RingHom.id L) := by
    rw [← minpolyDiv_spec K pb.gen]
    exact Polynomial.splits_mul (RingHom.id L) hqsplit
      (Polynomial.splits_X_sub_C (RingHom.id L) (x := pb.gen))
  have hsplit :
      (minpoly K pb.gen).Splits (algebraMap K L) :=
    (Polynomial.splits_id_iff_splits (algebraMap K L)).mp hmapsplit
  have hadjoin :
      Algebra.adjoin K ((minpoly K pb.gen).rootSet L : Set L) = ⊤ := by
    apply le_antisymm le_top
    rw [← pb.adjoin_gen_eq_top]
    apply Algebra.adjoin_mono
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [Polynomial.mem_rootSet_of_ne (minpoly.ne_zero pb.isIntegral_gen)]
    exact minpoly.aeval K pb.gen
  letI : Polynomial.IsSplittingField K L (minpoly K pb.gen) :=
    { splits' := hsplit
      adjoin_rootSet' := hadjoin }
  exact Normal.of_isSplittingField (minpoly K pb.gen)

/-- The residual cubic factor has rank two over the marked-root field. -/
theorem finrank_cubicResidualAlgebra_of_degree_three
    (pb : PowerBasis K L)
    (hdegree : pb.dim = 3) :
    Module.finrank L (CubicResidualAlgebra K L pb) = 2 := by
  change
    Module.finrank L
      (L[X] ⧸ Ideal.span ({minpolyDiv K pb.gen} : Set L[X])) = 2
  rw [finrank_quotient_span_eq_natDegree]
  have h := natDegree_minpolyDiv_succ pb.isIntegral_gen
  rw [pb.natDegree_minpoly, hdegree] at h
  omega

universe w

variable
    (N : Type w) [Field N]
    [Algebra K N] [Algebra L N] [IsScalarTower K L N]

/--
A second `K`-embedding of the cubic field into a common overfield gives an
`L`-algebra map from the residual factor by sending its root to the second
image of the primitive generator.
-/
def cubicResidualAlgHomOfDistinctEmbedding
    (pb : PowerBasis K L)
    (sigma : L →ₐ[K] N)
    (hdistinct :
      IsScalarTower.toAlgHom K L N pb.gen ≠ sigma pb.gen) :
    CubicResidualAlgebra K L pb →ₐ[L] N := by
  classical
  apply AdjoinRoot.liftHom
  have hroot :=
    eval₂_minpolyDiv_self pb.gen
      (IsScalarTower.toAlgHom K L N) sigma
  rw [if_neg hdistinct] at hroot
  simpa [Polynomial.aeval_def] using hroot

/--
In the nonnormal cubic branch, the residual map associated to a distinct
embedding is injective because the residual quadratic is irreducible.
-/
theorem cubicResidualAlgHomOfDistinctEmbedding_injective
    [Algebra.IsSeparable K L]
    (pb : PowerBasis K L)
    (hdegree : pb.dim = 3)
    (hnormal : ¬ Normal K L)
    (sigma : L →ₐ[K] N)
    (hdistinct :
      IsScalarTower.toAlgHom K L N pb.gen ≠ sigma pb.gen) :
    Function.Injective
      (cubicResidualAlgHomOfDistinctEmbedding
        K L N pb sigma hdistinct) := by
  letI : Fact (Irreducible (minpolyDiv K pb.gen)) :=
    ⟨irreducible_minpolyDiv_of_cubic_of_not_normal
      K L pb hdegree hnormal⟩
  exact
    (cubicResidualAlgHomOfDistinctEmbedding
      K L N pb sigma hdistinct).injective

/--
In the nonnormal separable cubic branch, the residual quadratic algebra is
the normal-closure field equipped with its marked `L`-algebra structure.

The normal-closure action supplies a conjugate embedding distinct from the
marked one.  The resulting residual map is injective.  Nonnormality also
makes the marked fixing subgroup nontrivial, so the normal-closure Galois
group is `S₃`; consequently `[N : K] = 6` and the tower law gives
`[N : L] = 2`.  Equal relative dimensions make the residual map bijective.
The construction chooses a conjugate embedding; no canonicity of the
resulting equivalence is asserted.
-/
noncomputable def cubicResidualEquivNormalClosureOfNotNormal
    [PerfectField K]
    [Algebra.IsSeparable K L]
    (D : NormalClosureData K L N)
    (hmarked :
      D.embedding = IsScalarTower.toAlgHom K L N)
    (pb : PowerBasis K L)
    (hdegree : pb.dim = 3)
    (hNotNormal : ¬ Normal K L) :
    CubicResidualAlgebra K L pb ≃ₐ[L] N := by
  classical
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : FiniteDimensional L N := FiniteDimensional.right K L N
  letI : Normal K N := D.normal
  letI : Algebra.IsAlgebraic K N :=
    Algebra.IsAlgebraic.of_finite K N
  letI : Algebra.IsSeparable K N :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI : IsGalois K N := IsGalois.mk
  have hnontrivial : D.intermediateFixingSubgroup ≠ ⊥ :=
    D.intermediateFixingSubgroup_ne_bot_of_not_normal hNotNormal
  have hfinrankKL : Module.finrank K L = 3 :=
    (PowerBasis.finrank pb).trans hdegree
  let galoisEquiv :
      D.galoisGroup ≃* Equiv.Perm (Fin 3) :=
    D.galoisGroupEquivPermFinThree hfinrankKL hnontrivial
  have hcardGalois : Nat.card D.galoisGroup = 6 := by
    calc
      Nat.card D.galoisGroup =
          Nat.card (Equiv.Perm (Fin 3)) :=
        Nat.card_congr galoisEquiv.toEquiv
      _ = Nat.factorial (Nat.card (Fin 3)) := Nat.card_perm
      _ = 6 := by norm_num [Nat.factorial]
  have hfinrankKN : Module.finrank K N = 6 := by
    rw [← IsGalois.card_aut_eq_finrank K N]
    exact hcardGalois
  have hfinrankLN : Module.finrank L N = 2 := by
    have htower := Module.finrank_mul_finrank K L N
    rw [hfinrankKL, hfinrankKN] at htower
    omega
  have hindex : D.intermediateFixingSubgroup.index = 3 := by
    change D.intermediateField.fixingSubgroup.index = 3
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact
      (AlgEquiv.ofInjectiveField D.embedding).toLinearEquiv.finrank_eq.symm.trans
        hfinrankKL
  have hneTop : D.intermediateFixingSubgroup ≠ ⊤ := by
    intro htop
    have hone : D.intermediateFixingSubgroup.index = 1 :=
      Subgroup.index_eq_one.mpr htop
    omega
  have hlt :
      D.intermediateFixingSubgroup <
        (⊤ : Subgroup D.galoisGroup) :=
    lt_of_le_of_ne le_top hneTop
  let hexists := SetLike.exists_of_lt hlt
  let g : D.galoisGroup := Classical.choose hexists
  have hg : g ∉ D.intermediateFixingSubgroup :=
    (Classical.choose_spec hexists).2
  let sigma : L →ₐ[K] N := g.toAlgHom.comp D.embedding
  have hsigmaMarked : sigma ≠ D.embedding := by
    intro hsigma
    apply hg
    change g ∈ D.intermediateField.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    change g (D.embedding y) = D.embedding y
    exact DFunLike.congr_fun hsigma y
  have hgenDistinct :
      IsScalarTower.toAlgHom K L N pb.gen ≠ sigma pb.gen := by
    rw [← hmarked]
    intro hgen
    apply hsigmaMarked
    exact PowerBasis.algHom_ext pb hgen.symm
  letI : Fact (Irreducible (minpolyDiv K pb.gen)) :=
    ⟨irreducible_minpolyDiv_of_cubic_of_not_normal
      K L pb hdegree hNotNormal⟩
  letI : FiniteDimensional L (CubicResidualAlgebra K L pb) :=
    (minpolyDiv_monic pb.isIntegral_gen).finite_adjoinRoot
  let residualHom : CubicResidualAlgebra K L pb →ₐ[L] N :=
    cubicResidualAlgHomOfDistinctEmbedding
      K L N pb sigma hgenDistinct
  have hinjective : Function.Injective residualHom :=
    residualHom.injective
  have hfinrankResidual :
      Module.finrank L (CubicResidualAlgebra K L pb) =
        Module.finrank L N :=
    (finrank_cubicResidualAlgebra_of_degree_three K L pb hdegree).trans
      hfinrankLN.symm
  have hsurjective : Function.Surjective residualHom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hfinrankResidual (f := residualHom.toLinearMap)).mp hinjective
  exact AlgEquiv.ofBijective residualHom ⟨hinjective, hsurjective⟩

end

end CollisionIdeals
