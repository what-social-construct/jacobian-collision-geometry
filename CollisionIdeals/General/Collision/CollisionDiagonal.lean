module

public import CollisionIdeals.General.Collision.Ideal

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

universe u v w

open MvPolynomial

noncomputable section

variable {R : Type u} [CommRing R]
variable {ι : Type v}
variable {κ : Type w}

/-- The collision equations vanish under diagonal evaluation. -/
theorem collisionIdeal_le_diagonalEval_ker
    (F : κ → SourceRing R ι) :
    collisionIdeal F ≤
      RingHom.ker (diagonalEval (R := R) (ι := ι)).toRingHom := by
  rw [diagonalEval_ker]
  exact collisionIdeal_le_diagonalIdeal F

/--
The morphism on coordinate rings dual to the diagonal
`X → X ×_Y X`.
-/
def collisionDiagonal (F : κ → SourceRing R ι) :
    CollisionRing F →ₐ[R] SourceRing R ι :=
  Ideal.Quotient.liftₐ
    (collisionIdeal F)
    (diagonalEval (R := R) (ι := ι))
    (collisionIdeal_le_diagonalEval_ker F)

/--
Paper notation `bar μ_F` for diagonal evaluation on the collision ring.

Geometrically this is the coordinate-ring map dual to
`Δ_X : X → X ×_Y X`.
-/
abbrev barMu
    (F : κ → SourceRing R ι) :
    CollisionRing F →+* SourceRing R ι :=
  (collisionDiagonal F).toRingHom

@[simp]
theorem collisionDiagonal_mk
    (F : κ → SourceRing R ι) (p : PairRing R ι) :
    collisionDiagonal F (Ideal.Quotient.mk (collisionIdeal F) p) =
      diagonalEval (R := R) (ι := ι) p := by
  rfl

/-- Diagonal evaluation on the collision ring is surjective. -/
theorem collisionDiagonal_surjective
    (F : κ → SourceRing R ι) :
    Function.Surjective (collisionDiagonal F) := by
  intro p
  refine
    ⟨Ideal.Quotient.mk (collisionIdeal F) (leftRename p), ?_⟩
  rw [collisionDiagonal_mk, diagonalEval_leftRename]

/--
The concrete obstruction ideal is precisely the ideal defining the diagonal
inside the collision fiber product.
-/
theorem collisionDiagonal_ker (F : κ → SourceRing R ι) :
    RingHom.ker (collisionDiagonal F).toRingHom = obstructionIdeal F := by
  change
    RingHom.ker
        (Ideal.Quotient.lift
          (collisionIdeal F)
          (diagonalEval (R := R) (ι := ι)).toRingHom
          (collisionIdeal_le_diagonalEval_ker F)) =
      obstructionIdeal F
  rw [Ideal.ker_quotient_lift, diagonalEval_ker]
  rfl

/-- The diagonal map is injective exactly when `I_R(F) = I_Δ`. -/
theorem collisionDiagonal_injective_iff
    (F : κ → SourceRing R ι) :
    Function.Injective (collisionDiagonal F) ↔
      collisionIdeal F =
        diagonalIdeal (R := R) (ι := ι) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  change
    RingHom.ker (collisionDiagonal F).toRingHom = ⊥ ↔
      collisionIdeal F =
        diagonalIdeal (R := R) (ι := ι)
  rw [collisionDiagonal_ker, obstructionIdeal_eq_bot_iff]

end

end CollisionIdeals
