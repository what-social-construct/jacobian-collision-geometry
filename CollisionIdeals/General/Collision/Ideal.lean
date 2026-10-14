module

public import CollisionIdeals.General.Collision.Diagonal

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

universe u v w

open MvPolynomial

noncomputable section

variable {R : Type u} [CommRing R]
variable {ι : Type v}
variable {κ : Type w}

/-- A collision equation attached to an output coordinate of `F`. -/
def collisionGenerator (F : κ → SourceRing R ι) (j : κ) : PairRing R ι :=
  leftRename (R := R) (ι := ι) (F j) -
    rightRename (R := R) (ι := ι) (F j)

/-- The collision ideal `I_R(F)`. -/
def collisionIdeal (F : κ → SourceRing R ι) : Ideal (PairRing R ι) :=
  Ideal.span (Set.range (collisionGenerator F))

/-- The coordinate ring of the self-fiber product cut out by `I_R(F)`. -/
abbrev CollisionRing (F : κ → SourceRing R ι) :=
  PairRing R ι ⧸ collisionIdeal F

/--
The image of `I_Δ` in the collision ring.  This is the ideal-theoretic
obstruction to the collision ideal being exactly the diagonal ideal.
-/
def obstructionIdeal (F : κ → SourceRing R ι) : Ideal (CollisionRing F) :=
  (diagonalIdeal (R := R) (ι := ι)).map
    (Ideal.Quotient.mk (collisionIdeal F))

/-- Every polynomial difference between the two copies vanishes modulo `I_Δ`. -/
theorem left_sub_right_mem_diagonal (p : SourceRing R ι) :
    leftRename (R := R) (ι := ι) p -
        rightRename (R := R) (ι := ι) p ∈
      diagonalIdeal (R := R) (ι := ι) := by
  rw [← diagonalEval_ker]
  change diagonalEval
    (leftRename (R := R) (ι := ι) p -
      rightRename (R := R) (ι := ι) p) = 0
  simp

/-- The canonical inclusion `I_R(F) ⊆ I_Δ`. -/
theorem collisionIdeal_le_diagonalIdeal (F : κ → SourceRing R ι) :
    collisionIdeal F ≤ diagonalIdeal (R := R) (ι := ι) := by
  rw [collisionIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact left_sub_right_mem_diagonal (F j)

/--
Substituting the two copies of `F` into any polynomial produces a difference
lying in `I_R(F)`.
-/
theorem bind_left_sub_right_mem_collisionIdeal
    (F : κ → SourceRing R ι) (p : MvPolynomial κ R) :
    leftRename (MvPolynomial.bind₁ F p) -
        rightRename (MvPolynomial.bind₁ F p) ∈ collisionIdeal F := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp
  | add p q hp hq =>
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (collisionIdeal F).add_mem hp hq
  | mul_X p j hp =>
      rw [map_mul, MvPolynomial.bind₁_X_right, map_mul, map_mul]
      rw [show
        leftRename (MvPolynomial.bind₁ F p) * leftRename (F j) -
            rightRename (MvPolynomial.bind₁ F p) * rightRename (F j) =
          leftRename (MvPolynomial.bind₁ F p) *
              (leftRename (F j) - rightRename (F j)) +
            (leftRename (MvPolynomial.bind₁ F p) -
                rightRename (MvPolynomial.bind₁ F p)) *
              rightRename (F j) by
        ring]
      exact
        (collisionIdeal F).add_mem
          ((collisionIdeal F).mul_mem_left _
            (Ideal.subset_span (Set.mem_range_self j)))
          ((collisionIdeal F).mul_mem_right _ hp)

/-- The obstruction quotient vanishes exactly when `I_R(F) = I_Δ`. -/
theorem obstructionIdeal_eq_bot_iff (F : κ → SourceRing R ι) :
    obstructionIdeal F = ⊥ ↔
      collisionIdeal F = diagonalIdeal (R := R) (ι := ι) := by
  rw [obstructionIdeal, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  constructor
  · intro h
    exact le_antisymm (collisionIdeal_le_diagonalIdeal F) h
  · intro h
    rw [h]

end

end CollisionIdeals
