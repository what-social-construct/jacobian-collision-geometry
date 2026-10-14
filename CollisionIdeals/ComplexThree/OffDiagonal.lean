module

public import CollisionIdeals.ComplexThree.Basic
public import CollisionIdeals.General.ResidualCollision.Scheme

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry

noncomputable section

/-- The coordinate ring of the off-diagonal collision scheme of a polynomial
self-map of complex affine three-space. -/
abbrev ComplexThreeOffDiagonalRing
    (F : ComplexThreePolynomialMap) :=
  OffDiagonalRing F

/-- The off-diagonal collision scheme of a polynomial self-map of complex
affine three-space. -/
abbrev ComplexThreeOffDiagonalScheme
    (F : ComplexThreePolynomialMap) :=
  offDiagonalCollisionScheme F

/-- The complex three-dimensional off-diagonal scheme is nonempty exactly
when its coordinate ring is nontrivial. -/
theorem complexThreeOffDiagonalScheme_nonempty_iff_ring_nontrivial
    (F : ComplexThreePolynomialMap) :
    Nonempty (ComplexThreeOffDiagonalScheme F) ↔
      Nontrivial (ComplexThreeOffDiagonalRing F) := by
  rw [← not_isEmpty_iff, ← not_subsingleton_iff_nontrivial]
  exact not_congr
    (offDiagonalCollisionScheme_isEmpty_iff_subsingleton F)

/-- Nonemptiness of the off-diagonal scheme is exactly nonvanishing of the
collision obstruction. -/
theorem complexThreeOffDiagonalScheme_nonempty_iff_obstructionIdeal_ne_bot
    (F : ComplexThreePolynomialMap) :
    Nonempty (ComplexThreeOffDiagonalScheme F) ↔
      obstructionIdeal F ≠ ⊥ := by
  rw [← not_isEmpty_iff]
  exact not_congr
    (collisionOffDiagonalVanishing_iff_obstructionIdeal_eq_bot F)

/-- Nonemptiness of the off-diagonal scheme is exactly failure of the
collision ideal to equal the diagonal ideal. -/
theorem complexThreeOffDiagonalScheme_nonempty_iff_collisionIdeal_ne_diagonalIdeal
    (F : ComplexThreePolynomialMap) :
    Nonempty (ComplexThreeOffDiagonalScheme F) ↔
      collisionIdeal F ≠
        diagonalIdeal (R := ℂ) (ι := Fin 3) := by
  exact
    (complexThreeOffDiagonalScheme_nonempty_iff_obstructionIdeal_ne_bot F).trans
      (not_congr (obstructionIdeal_eq_bot_iff F))

/-- Since the collision ideal is always contained in the diagonal ideal,
nonemptiness is equivalently strict containment. -/
theorem complexThreeOffDiagonalScheme_nonempty_iff_collisionIdeal_lt_diagonalIdeal
    (F : ComplexThreePolynomialMap) :
    Nonempty (ComplexThreeOffDiagonalScheme F) ↔
      collisionIdeal F <
        diagonalIdeal (R := ℂ) (ι := Fin 3) := by
  rw [complexThreeOffDiagonalScheme_nonempty_iff_collisionIdeal_ne_diagonalIdeal]
  constructor
  · intro h
    exact lt_of_le_of_ne (collisionIdeal_le_diagonalIdeal F) h
  · exact ne_of_lt

end

end CollisionIdeals
