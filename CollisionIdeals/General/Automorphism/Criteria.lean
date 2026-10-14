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

/-- A polynomial left inverse `G ∘ F = id` for a map with output variables `κ`. -/
def HasPolynomialLeftInverse (F : κ → SourceRing R ι) : Prop :=
  ∃ G : ι → MvPolynomial κ R,
    ∀ i, MvPolynomial.bind₁ F (G i) = X i

/--
A polynomial self-map is an automorphism when substitution by its
coordinate polynomials is a bijection of the coordinate polynomial ring.
-/
def IsPolynomialAutomorphism
    (F : ι → SourceRing R ι) : Prop :=
  Function.Bijective (MvPolynomial.bind₁ F)

/-- A polynomial automorphism has a polynomial left inverse. -/
theorem IsPolynomialAutomorphism.hasPolynomialLeftInverse
    {F : ι → SourceRing R ι}
    (hF : IsPolynomialAutomorphism F) :
    HasPolynomialLeftInverse F := by
  choose G hG using fun i ↦ hF.2 (X i)
  exact ⟨G, hG⟩

/-- A polynomial left inverse forces the collision ideal to be the diagonal ideal. -/
theorem collisionIdeal_eq_diagonalIdeal_of_hasPolynomialLeftInverse
    (F : κ → SourceRing R ι) (hF : HasPolynomialLeftInverse F) :
    collisionIdeal F = diagonalIdeal (R := R) (ι := ι) := by
  apply le_antisymm (collisionIdeal_le_diagonalIdeal F)
  rw [diagonalIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨G, hG⟩ := hF
  have hmem := bind_left_sub_right_mem_collisionIdeal F (G i)
  simpa [diagonalGenerator, hG i] using hmem

/-- Every polynomial automorphism has vanishing collision obstruction. -/
theorem obstructionIdeal_eq_bot_of_isPolynomialAutomorphism
    {F : ι → SourceRing R ι}
    (hF : IsPolynomialAutomorphism F) :
    obstructionIdeal F = ⊥ := by
  apply (obstructionIdeal_eq_bot_iff F).2
  exact
    collisionIdeal_eq_diagonalIdeal_of_hasPolynomialLeftInverse
      F hF.hasPolynomialLeftInverse

/-- Evaluate the coordinate polynomials of `F` at a point. -/
def pointMap (F : κ → SourceRing R ι) (a : ι → R) : κ → R :=
  fun j ↦ MvPolynomial.eval a (F j)

/-- Evaluate the pair ring at the ordered pair `(a,b)`. -/
def pairEval (a b : ι → R) : PairRing R ι →+* R :=
  MvPolynomial.eval (Sum.elim a b)

theorem collisionIdeal_le_pairEval_ker
    (F : κ → SourceRing R ι) (a b : ι → R)
    (h : pointMap F a = pointMap F b) :
    collisionIdeal F ≤ RingHom.ker (pairEval a b) := by
  rw [collisionIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  change pairEval a b
    (leftRename (F j) - rightRename (F j)) = 0
  have hj := congrFun h j
  change MvPolynomial.eval a (F j) = MvPolynomial.eval b (F j) at hj
  simp [pairEval, leftRename, rightRename, MvPolynomial.eval_rename, hj]

/-- If `I_R(F) = I_Δ`, then equality of images implies equality of points. -/
theorem pointMap_injective_of_collisionIdeal_eq_diagonalIdeal
    (F : κ → SourceRing R ι)
    (hIdeal : collisionIdeal F = diagonalIdeal (R := R) (ι := ι)) :
    Function.Injective (pointMap F) := by
  intro a b hCollision
  funext i
  have hmem :
      diagonalGenerator (R := R) i ∈ collisionIdeal F := by
    rw [hIdeal]
    exact diagonalGenerator_mem i
  have hzero :=
    collisionIdeal_le_pairEval_ker F a b hCollision hmem
  rw [RingHom.mem_ker] at hzero
  have : a i - b i = 0 := by
    simpa [pairEval, diagonalGenerator] using hzero
  exact sub_eq_zero.mp this

end

end CollisionIdeals
