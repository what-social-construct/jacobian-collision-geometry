import CollisionIdeals.General.Keller.ConjugateInvariantObstruction
import CollisionIdeals.Planar.Research.Vanishing.FiniteBoundary

/-!
# The actual target boundary characterizes planar collision vanishing

The existing finite-boundary endpoint proves obstruction vanishing from
an empty target boundary, with purity and finite-etale rigidity explicit.
Conversely, obstruction vanishing identifies the conjugate source maps,
making the fixed algebra regular on the marked source and the actual
target boundary empty.

The source-regularity and conormal formulations are corollaries using the
same fixed algebra, marked source map, and reduced target boundary. No new
criterion predicate, quotient, or boundary model is introduced. These are
map-by-map equivalences, not universal vanishing theorems. Neither
Ax--Grothendieck nor Keller--Galois rigidity is an input here.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]
variable [Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N]

/-- Collision-obstruction vanishing is equivalent to emptiness of the
actual target boundary. The two geometric inputs are used only from
boundary emptiness to obstruction vanishing. -/
theorem planarObstructionIdeal_eq_bot_iff_conjugateInvariantBoundary_eq_top
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    obstructionIdeal F = ⊥ ↔
      polynomialConjugateInvariantBoundaryIdeal D hKeller = ⊤ := by
  constructor
  · intro hObstruction
    exact polynomialConjugateInvariantBoundaryIdeal_eq_top_of_obstructionIdeal_eq_bot
      D hKeller hObstruction
  · exact planarVanishing_of_conjugateInvariantBoundary_eq_top
      hPurity hFiniteEtaleRigidity D hKeller

/-- The same vanishing criterion expressed as regularity of every fixed
element on the marked polynomial source, with no new ring identification. -/
theorem planarObstructionIdeal_eq_bot_iff_conjugateInvariant_source_regular
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    obstructionIdeal F = ⊥ ↔
      ∀ z : polynomialConjugateInvariantAlgebra D,
        (z.val : N) ∈ Set.range (polynomialConjugateSourceMapOverImage D 1) :=
  (planarObstructionIdeal_eq_bot_iff_conjugateInvariantBoundary_eq_top
    hPurity hFiniteEtaleRigidity D hKeller).trans
    (polynomialConjugateInvariantAlgebra_source_regular_iff_boundary_eq_top D hKeller).symm

/-- The existing two target-coordinate conormal components give an
equivalent finite first-order formulation of collision-obstruction vanishing. -/
theorem planarObstructionIdeal_eq_bot_iff_conjugateInvariantBoundary_conormal_eq_zero
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (D : PolynomialNormalClosureData F N) (hKeller : IsKeller F) :
    letI := D.finiteIntermediate
    obstructionIdeal F = ⊥ ↔
      ∀ i : Fin 2, derivationConormalComponent (polynomialImageCoordinatePartial F i)
        (polynomialConjugateInvariantBoundaryIdeal D hKeller) = 0 := by
  letI := D.finiteIntermediate
  exact (planarObstructionIdeal_eq_bot_iff_conjugateInvariantBoundary_eq_top
    hPurity hFiniteEtaleRigidity D hKeller).trans
    ((polynomialConjugateInvariantBoundaryIdeal_eq_top_iff D hKeller).trans
      (polynomialConjugateInvariantBoundary_conormal_eq_zero_iff D hKeller).symm)

end

end CollisionIdeals.Planar
