import CollisionIdeals.General.Galois.PolynomialDescent

/-!
# Vanishing collisions and the marked source field

When the collision obstruction vanishes, evaluating the diagonal generators
at a Galois collision pair makes each conjugate source coordinate equal to
the marked original coordinate. In particular the original function-field
extension is normal. These implications use only the supplied marked normal
closure, not the Keller condition or an automorphism theorem.
-/

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n} {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

/-- If the collision obstruction vanishes, every conjugate source coordinate
equals its marked original value. No Keller or separability input is needed. -/
theorem polynomialConjugate_coordinate_eq_of_obstructionIdeal_eq_bot
    (D : PolynomialNormalClosureData F N) (hObstruction : obstructionIdeal F = ⊥)
    (g : D.galoisGroup) (i : Fin n) :
    g (D.embedding
        (algebraMap (SourceRing k (Fin n)) (PolynomialMapSourceFunctionField F) (X i))) =
      D.embedding
        (algebraMap (SourceRing k (Fin n)) (PolynomialMapSourceFunctionField F) (X i)) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra k N :=
    polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  let c := polynomialGaloisCollisionPair D 1 g
  have hmem : diagonalGenerator (R := k) i ∈ collisionIdeal F := by
    rw [(obstructionIdeal_eq_bot_iff F).mp hObstruction]
    exact diagonalGenerator_mem i
  have hzero := collisionIdeal_le_collisionPairMap_ker c hmem
  change collisionPairMap c (diagonalGenerator i) = 0 at hzero
  have heq : c.left (X i) = c.right (X i) := by
    apply sub_eq_zero.mp
    simpa [collisionPairMap, diagonalGenerator] using hzero
  simpa only [c, polynomialGaloisCollisionPair_left,
    polynomialGaloisCollisionPair_right, mul_one,
    polynomialConjugateSourceMap_apply, AlgEquiv.one_apply] using heq.symm

/-- Vanishing collision obstruction implies normality of the original
function-field extension directly through the marked normal closure. -/
theorem polynomialSource_normal_of_obstructionIdeal_eq_bot
    (D : PolynomialNormalClosureData F N) (hObstruction : obstructionIdeal F = ⊥) :
    Normal (PolynomialMapBaseFunctionField F) (PolynomialMapSourceFunctionField F) := by
  apply (polynomialSource_normal_iff_conjugate_coordinates_mem D).mpr
  intro g i
  rw [polynomialConjugate_coordinate_eq_of_obstructionIdeal_eq_bot D hObstruction g i]
  exact ⟨_, rfl⟩

end

end CollisionIdeals
