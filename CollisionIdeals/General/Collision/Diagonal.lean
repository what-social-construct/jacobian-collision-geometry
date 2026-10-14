module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

universe u v

open MvPolynomial

noncomputable section

variable {R : Type u} [CommRing R]
variable {ι : Type v}

/-- Two labelled copies of the source variables. -/
abbrev PairVars (ι : Type v) := Sum ι ι

/-- The polynomial ring on one copy of affine space. -/
abbrev SourceRing (R : Type u) (ι : Type v) [CommRing R] :=
  MvPolynomial ι R

/-- The polynomial ring on two copies of affine space. -/
abbrev PairRing (R : Type u) (ι : Type v) [CommRing R] :=
  MvPolynomial (PairVars ι) R

/-- Put a polynomial in the left copy of the source variables. -/
def leftRename : SourceRing R ι →ₐ[R] PairRing R ι :=
  MvPolynomial.rename Sum.inl

/-- Put a polynomial in the right copy of the source variables. -/
def rightRename : SourceRing R ι →ₐ[R] PairRing R ι :=
  MvPolynomial.rename Sum.inr

/-- A standard generator `xᵢ(left) - xᵢ(right)` of the diagonal ideal. -/
def diagonalGenerator (i : ι) : PairRing R ι :=
  (X (Sum.inl i : PairVars ι) : PairRing R ι) -
    (X (Sum.inr i : PairVars ι) : PairRing R ι)

/-- The diagonal ideal in the coordinate ring of two copies of affine space. -/
def diagonalIdeal : Ideal (PairRing R ι) :=
  Ideal.span (Set.range (diagonalGenerator (R := R) (ι := ι)))

/-- Collapse the two labelled copies of the source variables to one copy. -/
def diagonalEval : PairRing R ι →ₐ[R] SourceRing R ι :=
  MvPolynomial.rename (Sum.elim id id)

@[simp]
theorem leftRename_C (r : R) :
    leftRename (ι := ι) (C r) = C r := by
  simp [leftRename]

@[simp]
theorem rightRename_C (r : R) :
    rightRename (ι := ι) (C r) = C r := by
  simp [rightRename]

@[simp]
theorem leftRename_X (i : ι) :
    leftRename (R := R) (X i) = X (Sum.inl i) := by
  simp [leftRename]

@[simp]
theorem rightRename_X (i : ι) :
    rightRename (R := R) (X i) = X (Sum.inr i) := by
  simp [rightRename]

@[simp]
theorem leftRename_add (p q : SourceRing R ι) :
    leftRename (p + q) = leftRename p + leftRename q := by
  exact map_add _ _ _

@[simp]
theorem rightRename_add (p q : SourceRing R ι) :
    rightRename (p + q) = rightRename p + rightRename q := by
  exact map_add _ _ _

@[simp]
theorem leftRename_mul (p q : SourceRing R ι) :
    leftRename (p * q) = leftRename p * leftRename q := by
  exact map_mul _ _ _

@[simp]
theorem rightRename_mul (p q : SourceRing R ι) :
    rightRename (p * q) = rightRename p * rightRename q := by
  exact map_mul _ _ _

theorem diagonalGenerator_mem (i : ι) :
    diagonalGenerator (R := R) i ∈
      diagonalIdeal (R := R) (ι := ι) := by
  exact Ideal.subset_span (Set.mem_range_self i)

@[simp]
theorem diagonalEval_leftRename (p : SourceRing R ι) :
    diagonalEval (R := R) (ι := ι) (leftRename p) = p := by
  simp [diagonalEval, leftRename, MvPolynomial.rename_rename]

@[simp]
theorem diagonalEval_rightRename (p : SourceRing R ι) :
    diagonalEval (R := R) (ι := ι) (rightRename p) = p := by
  simp [diagonalEval, rightRename, MvPolynomial.rename_rename]

@[simp]
theorem diagonalEval_diagonalGenerator (i : ι) :
    diagonalEval (R := R) (diagonalGenerator (R := R) i) = 0 := by
  simp [diagonalEval, diagonalGenerator]

/--
Every polynomial in the two copies differs from the left copy of its
diagonal restriction by an element of the diagonal ideal.
-/
theorem sub_leftRename_diagonalEval_mem (p : PairRing R ι) :
    p - leftRename (diagonalEval (R := R) (ι := ι) p) ∈
      diagonalIdeal (R := R) (ι := ι) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp
  | add p q hp hq =>
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (diagonalIdeal (R := R) (ι := ι)).add_mem hp hq
  | mul_X p i hp =>
      cases i with
      | inl i =>
          rw [map_mul, map_mul, diagonalEval, rename_X, leftRename_X]
          simp only [Sum.elim_inl]
          change
            p * X (Sum.inl i) -
                leftRename (diagonalEval (R := R) (ι := ι) p) *
                  X (Sum.inl i) ∈
              diagonalIdeal (R := R) (ι := ι)
          rw [show
            p * X (Sum.inl i) -
                leftRename (diagonalEval (R := R) (ι := ι) p) *
                  X (Sum.inl i) =
              X (Sum.inl i) *
                (p - leftRename (diagonalEval (R := R) (ι := ι) p)) by
            ring]
          exact
            (diagonalIdeal (R := R) (ι := ι)).mul_mem_left _ hp
      | inr i =>
          rw [map_mul, map_mul, diagonalEval, rename_X, leftRename_X]
          simp only [Sum.elim_inr]
          change
            p * X (Sum.inr i) -
                leftRename (diagonalEval (R := R) (ι := ι) p) *
                  X (Sum.inl i) ∈
              diagonalIdeal (R := R) (ι := ι)
          rw [show
            p * X (Sum.inr i) -
                leftRename (diagonalEval (R := R) (ι := ι) p) *
                  X (Sum.inl i) =
              X (Sum.inr i) *
                  (p - leftRename (diagonalEval (R := R) (ι := ι) p)) -
                leftRename (diagonalEval (R := R) (ι := ι) p) *
                  diagonalGenerator (R := R) i by
            simp [diagonalGenerator]
            ring]
          exact
            (diagonalIdeal (R := R) (ι := ι)).sub_mem
              ((diagonalIdeal (R := R) (ι := ι)).mul_mem_left _ hp)
              ((diagonalIdeal (R := R) (ι := ι)).mul_mem_left _
                (diagonalGenerator_mem (R := R) i))

/-- The diagonal ideal is exactly the kernel of diagonal evaluation. -/
theorem diagonalEval_ker :
    RingHom.ker (diagonalEval (R := R) (ι := ι)).toRingHom =
      diagonalIdeal (R := R) (ι := ι) := by
  apply le_antisymm
  · intro p hp
    have hsub := sub_leftRename_diagonalEval_mem (R := R) (ι := ι) p
    change diagonalEval (R := R) (ι := ι) p = 0 at hp
    rw [hp, map_zero] at hsub
    simpa using hsub
  · rw [diagonalIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change diagonalEval (R := R) (ι := ι)
      (diagonalGenerator (R := R) i) = 0
    exact diagonalEval_diagonalGenerator (R := R) i

/-- Diagonal evaluation is surjective because left renaming is a section. -/
theorem diagonalEval_surjective :
    Function.Surjective
      (diagonalEval (R := R) (ι := ι)).toRingHom := by
  intro p
  exact ⟨leftRename p, by simp⟩

/-- The coordinate ring `S / I_Δ` is canonically the source ring. -/
noncomputable def diagonalQuotientEquiv :
    (PairRing R ι ⧸
        diagonalIdeal (R := R) (ι := ι)) ≃+*
      SourceRing R ι :=
  (Ideal.quotEquivOfEq
      (diagonalEval_ker (R := R) (ι := ι)).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (diagonalEval (R := R) (ι := ι)).toRingHom)
      (diagonalEval_surjective (R := R) (ι := ι)))

end

end CollisionIdeals
