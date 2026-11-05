module

public import CollisionIdeals.ComplexThree.Cubic.Branch

@[expose] public section

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

/-- In a normal power-basis extension, the remaining-conjugates polynomial splits. -/
theorem splits_minpolyDiv_of_normal
    (pb : PowerBasis K L) (hnormal : Normal K L) :
    (minpolyDiv K pb.gen).Splits := by
  apply (hnormal.splits pb.gen).of_dvd
    (Polynomial.map_ne_zero (minpoly.ne_zero pb.isIntegral_gen))
  exact ⟨X - C pb.gen, (minpolyDiv_spec K pb.gen).symm⟩

/-- The residual polynomial of a separable power-basis extension is separable. -/
theorem separable_minpolyDiv
    [Algebra.IsSeparable K L] (pb : PowerBasis K L) :
    (minpolyDiv K pb.gen).Separable := by
  apply ((Polynomial.separable_map (algebraMap K L)).mpr
    (Algebra.IsSeparable.isSeparable K pb.gen)).of_dvd
  exact ⟨X - C pb.gen, (minpolyDiv_spec K pb.gen).symm⟩

/-- A separable cubic extension is nonnormal exactly when its residual quadratic
is irreducible over the marked-root field. -/
theorem irreducible_minpolyDiv_iff_not_normal
    [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) (hdegree : pb.dim = 3) :
    Irreducible (minpolyDiv K pb.gen) ↔ ¬ Normal K L := by
  constructor
  · intro hirreducible hnormal
    have hle := (splits_minpolyDiv_of_normal K L pb hnormal).natDegree_le_one_of_irreducible
      hirreducible
    have h := natDegree_minpolyDiv_succ pb.isIntegral_gen
    rw [pb.natDegree_minpoly, hdegree] at h
    omega
  · exact irreducible_minpolyDiv_of_cubic_of_not_normal K L pb hdegree

/-- In the normal separable cubic branch, the two residual linear factors are
coprime. The witnesses order the two remaining roots but do not canonically label them. -/
theorem exists_coprime_cubicResidual_factors_of_normal
    [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) (hdegree : pb.dim = 3)
    (hnormal : Normal K L) :
    ∃ b c : L, minpolyDiv K pb.gen = (X - C b) * (X - C c) ∧
      IsCoprime (X - C b) (X - C c) := by
  have hqdegree : (minpolyDiv K pb.gen).natDegree = 2 := by
    have h := natDegree_minpolyDiv_succ pb.isIntegral_gen
    rw [pb.natDegree_minpoly, hdegree] at h
    omega
  have hnot : ¬ Irreducible (minpolyDiv K pb.gen) := by
    rw [irreducible_minpolyDiv_iff_not_normal K L pb hdegree]
    exact not_not_intro hnormal
  obtain ⟨c₁, c₂, hcoeffZero, hcoeffOne⟩ :=
    ((minpolyDiv_monic pb.isIntegral_gen).not_irreducible_iff_exists_add_mul_eq_coeff
      hqdegree).mp hnot
  have hfactor : minpolyDiv K pb.gen = (X + C c₁) * (X + C c₂) := by
    rw [(minpolyDiv K pb.gen).as_sum_range_C_mul_X_pow, hqdegree,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      ← hqdegree, (minpolyDiv_monic pb.isIntegral_gen).coeff_natDegree,
      hqdegree, hcoeffZero, hcoeffOne, C_mul, C_add, C_1]
    ring
  have hfactor' : minpolyDiv K pb.gen = (X - C (-c₁)) * (X - C (-c₂)) := by
    simpa only [map_neg, sub_neg_eq_add] using hfactor
  refine ⟨-c₁, -c₂, hfactor', ?_⟩
  have hsep := separable_minpolyDiv K L pb
  rw [hfactor'] at hsep
  exact hsep.isCoprime

/-- In the normal separable cubic branch, the residual collision algebra is a
product of two copies of the marked-root field. This equivalence chooses an ordering
of the two remaining roots; no canonical ordering is asserted. -/
def cubicResidualEquivProdOfNormal
    [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) (hdegree : pb.dim = 3)
    (hnormal : Normal K L) :
    CubicResidualAlgebra K L pb ≃ₐ[L] L × L := by
  classical
  let h := exists_coprime_cubicResidual_factors_of_normal K L pb hdegree hnormal
  let b : L := Classical.choose h
  let c : L := Classical.choose (Classical.choose_spec h)
  have hfactor : minpolyDiv K pb.gen = (X - C b) * (X - C c) :=
    (Classical.choose_spec (Classical.choose_spec h)).1
  have hcop : IsCoprime (X - C b) (X - C c) :=
    (Classical.choose_spec (Classical.choose_spec h)).2
  let I : Ideal L[X] := Ideal.span ({X - C b} : Set L[X])
  let J : Ideal L[X] := Ideal.span ({X - C c} : Set L[X])
  have hcopIdeal : IsCoprime I J := by
    change IsCoprime (Ideal.span ({X - C b} : Set L[X]))
      (Ideal.span ({X - C c} : Set L[X]))
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hcop
  have hspan : Ideal.span ({minpolyDiv K pb.gen} : Set L[X]) = I * J := by
    dsimp [I, J]
    rw [Ideal.span_singleton_mul_span_singleton, hfactor]
  let e₀ : CubicResidualAlgebra K L pb ≃ₐ[L] L[X] ⧸ I * J :=
    Ideal.quotientEquivAlgOfEq L hspan
  let eCRT₀ : (L[X] ⧸ I * J) ≃+* (L[X] ⧸ I) × (L[X] ⧸ J) :=
    Ideal.quotientMulEquivQuotientProd I J hcopIdeal
  let eCRT : (L[X] ⧸ I * J) ≃ₐ[L] (L[X] ⧸ I) × (L[X] ⧸ J) :=
    AlgEquiv.ofRingEquiv (f := eCRT₀) (by intro x; rfl)
  exact e₀.trans <| eCRT.trans <|
    AlgEquiv.prodCongr
      (Polynomial.quotientSpanXSubCAlgEquiv b)
      (Polynomial.quotientSpanXSubCAlgEquiv c)

/-- The split residual branch occurs exactly for normal separable cubic extensions. -/
theorem nonempty_cubicResidualEquivProd_iff_normal
    [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) (hdegree : pb.dim = 3) :
    Nonempty (CubicResidualAlgebra K L pb ≃ₐ[L] L × L) ↔ Normal K L := by
  constructor
  · rintro ⟨e⟩
    by_contra hnormal
    letI : Fact (Irreducible (minpolyDiv K pb.gen)) :=
      ⟨irreducible_minpolyDiv_of_cubic_of_not_normal K L pb hdegree hnormal⟩
    have hfield : IsField (L × L) :=
      e.symm.toMulEquiv.isField (Field.toIsField (CubicResidualAlgebra K L pb))
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel (a := (1, 0)) (by simp)
    have := congrArg Prod.snd hb
    simp at this
  · intro hnormal
    exact ⟨cubicResidualEquivProdOfNormal K L pb hdegree hnormal⟩

end

end CollisionIdeals
