import CollisionIdeals.Planar.Research.SecantFrameCandidate

/-!
# Removing redundant adjugate coefficients in dimension two

The adjugate of a two-by-two matrix is a signed permutation of its entries.
The same is true after any additive operator, including either Keller
derivation. Thus the adjugate and its first jets do not enlarge the existing
secant-frame lattice or change its denominator ideal.

This removes only the matrix/adjugate flag. It does not remove either
first-derivative family or assert regularity at a normalization divisor.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

section Matrix

variable {R A : Type*} [CommRing R] [CommRing A] [Module R A]

private theorem map_adjugate_fin_two_mem
    (S : Submodule R A) (M : Matrix (Fin 2) (Fin 2) A) (f : A →+ A)
    (h : ∀ i j, f (M i j) ∈ S) (i j : Fin 2) :
    f (M.adjugate i j) ∈ S := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using h 1 1
  · simpa [Matrix.adjugate_fin_two] using S.neg_mem (h 0 1)
  · simpa [Matrix.adjugate_fin_two] using S.neg_mem (h 1 0)
  · simpa [Matrix.adjugate_fin_two] using h 0 0

/-- An additive operator sees the same entry span in a two-by-two matrix
and its adjugate. The operator need not be linear over the span's scalars. -/
theorem span_map_adjugate_fin_two (M : Matrix (Fin 2) (Fin 2) A) (f : A →+ A) :
    Submodule.span R (Set.range (fun ij : Fin 2 × Fin 2 => f (M.adjugate ij.1 ij.2))) =
      Submodule.span R (Set.range (fun ij : Fin 2 × Fin 2 => f (M ij.1 ij.2))) := by
  have hle (M : Matrix (Fin 2) (Fin 2) A) :
      Submodule.span R (Set.range (fun ij : Fin 2 × Fin 2 => f (M.adjugate ij.1 ij.2))) ≤
        Submodule.span R (Set.range (fun ij : Fin 2 × Fin 2 => f (M ij.1 ij.2))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact map_adjugate_fin_two_mem
      (Submodule.span R (Set.range (fun ij : Fin 2 × Fin 2 => f (M ij.1 ij.2)))) M f
      (fun i j => Submodule.subset_span ⟨(i, j), rfl⟩) i j
  apply le_antisymm (hle M)
  simpa [Matrix.adjugate_adjugate'] using hle M.adjugate

end Matrix

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
  [Algebra (PolynomialMapBaseFunctionField F) N]
variable (T : Type) [CommRing T] [Algebra T N]

/-- Keeping only the matrix flag gives exactly the original evaluated
coefficient span, including both first-jet families. -/
theorem evaluatedSecantFrameCoefficient_span_eq_matrix_jets
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N) :
    Submodule.span T (Set.range (evaluatedSecantFrameCoefficient D C dP dQ)) =
      Submodule.span T (Set.range
        (fun i : MovedConjugatePair D C × Fin 2 × Fin 2 × Fin 3 =>
          evaluatedSecantFrameCoefficient D C dP dQ (i.1, 0, i.2))) := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  let S : Submodule T N := Submodule.span T (Set.range
    (fun i : MovedConjugatePair D C × Fin 2 × Fin 2 × Fin 3 =>
      evaluatedSecantFrameCoefficient D C dP dQ (i.1, 0, i.2)))
  have hmatrix (a : MovedConjugatePair D C) (i j : Fin 2) (k : Fin 3) :
      evaluatedSecantFrameCoefficient D C dP dQ (a, 0, i, j, k) ∈ S :=
    Submodule.subset_span ⟨(a, i, j, k), rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, s, i, j, k⟩, rfl⟩
    change evaluatedSecantFrameCoefficient D C dP dQ (a, s, i, j, k) ∈ S
    fin_cases s
    · exact hmatrix a i j k
    · fin_cases k
      · simpa [evaluatedSecantFrameCoefficient, evaluatedSecantAdjugate] using
          map_adjugate_fin_two_mem S
            (evaluatedSecantMatrix D a.val.1 a.val.2) (AddMonoidHom.id N)
            (fun i j => by simpa [evaluatedSecantFrameCoefficient] using hmatrix a i j 0)
            i j
      · simpa [evaluatedSecantFrameCoefficient, evaluatedSecantAdjugate] using
          map_adjugate_fin_two_mem S
            (evaluatedSecantMatrix D a.val.1 a.val.2) dP.toLinearMap.toAddMonoidHom
            (fun i j => by simpa [evaluatedSecantFrameCoefficient] using hmatrix a i j 1)
            i j
      · simpa [evaluatedSecantFrameCoefficient, evaluatedSecantAdjugate] using
          map_adjugate_fin_two_mem S
            (evaluatedSecantMatrix D a.val.1 a.val.2) dQ.toLinearMap.toAddMonoidHom
            (fun i j => by simpa [evaluatedSecantFrameCoefficient] using hmatrix a i j 2)
            i j
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, i, j, k⟩, rfl⟩
    exact Submodule.subset_span ⟨(a, 0, i, j, k), rfl⟩

/-- The existing lattice is unchanged when its adjugate generators and
their first jets are omitted. -/
theorem evaluatedSecantFrameLattice_eq_matrix_jets
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N) :
    evaluatedSecantFrameLattice T D C dP dQ =
      (1 : Submodule T N) ⊔ Submodule.span T (Set.range
        (fun i : MovedConjugatePair D C × Fin 2 × Fin 2 × Fin 3 =>
          evaluatedSecantFrameCoefficient D C dP dQ (i.1, 0, i.2))) := by
  rw [evaluatedSecantFrameLattice_eq_one_sup_span,
    evaluatedSecantFrameCoefficient_span_eq_matrix_jets]

/-- The denominator ideal depends only on the matrix coefficients and
their first jets, not on a separate adjugate coefficient family. -/
theorem evaluatedSecantFrameDenominatorIdeal_eq_matrix_jets
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N) :
    evaluatedSecantFrameDenominatorIdeal T D C dP dQ =
      (1 : Submodule T N).colon
        ((1 : Submodule T N) ⊔ Submodule.span T (Set.range
          (fun i : MovedConjugatePair D C × Fin 2 × Fin 2 × Fin 3 =>
            evaluatedSecantFrameCoefficient D C dP dQ (i.1, 0, i.2))) :
          Submodule T N) := by
  rw [evaluatedSecantFrameDenominatorIdeal, evaluatedSecantFrameLattice_eq_matrix_jets]

end

end CollisionIdeals.Planar
