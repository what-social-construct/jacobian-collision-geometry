import CollisionIdeals.General.Keller.ConjugateInvariantCriterion
import CollisionIdeals.General.Galois.CollisionVanishing

/-!
# Vanishing collisions remove the actual target boundary

When the collision obstruction vanishes, its collision ideal equals the
diagonal ideal. Evaluating the diagonal generators at each Galois collision
pair shows that every conjugate source coordinate equals the marked one.
The all-conjugate algebra, and hence its fixed algebra, is therefore
regular on the marked polynomial source.

For a Keller map, the existing source-regularity criterion identifies this
with an empty actual target boundary. This implication uses no
Ax--Grothendieck, purity, finite-etale rigidity, or Galois-rigidity input.
It does not assert that the obstruction vanishes for every Keller map.
-/

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n} {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

/-- Vanishing collision obstruction makes every fixed-algebra element
regular on the marked polynomial source, directly from the collision
equations. No Keller or separability hypothesis is needed for this step. -/
theorem polynomialConjugateInvariantAlgebra_source_regular_of_obstructionIdeal_eq_bot
    (D : PolynomialNormalClosureData F N) (hObstruction : obstructionIdeal F = ⊥) :
    ∀ z : polynomialConjugateInvariantAlgebra D,
      (z.val : N) ∈ Set.range (polynomialConjugateSourceMapOverImage D 1) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  have hSource : polynomialConjugateAlgebra D ≤
      (polynomialConjugateSourceMapOverImage D 1).range := by
    apply Algebra.adjoin_le
    rintro _ ⟨⟨g, i⟩, rfl⟩
    refine ⟨X i, ?_⟩
    simpa only [polynomialConjugateSourceMapOverImage_apply, AlgEquiv.one_apply] using
      (polynomialConjugate_coordinate_eq_of_obstructionIdeal_eq_bot D hObstruction g i).symm
  intro z
  exact hSource z.val.property

variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

/-- A vanishing collision obstruction makes the actual target-boundary
ideal the unit ideal. The converse planar endpoint has separate geometric
inputs; none is used in this direction. -/
theorem polynomialConjugateInvariantBoundaryIdeal_eq_top_of_obstructionIdeal_eq_bot
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F)
    (hObstruction : obstructionIdeal F = ⊥) :
    polynomialConjugateInvariantBoundaryIdeal D hKeller = ⊤ :=
  (polynomialConjugateInvariantAlgebra_source_regular_iff_boundary_eq_top D hKeller).mp
    (polynomialConjugateInvariantAlgebra_source_regular_of_obstructionIdeal_eq_bot
      D hObstruction)

end

end CollisionIdeals
