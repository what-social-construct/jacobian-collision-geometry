import CollisionIdeals.Planar.Research.Vanishing.LocalCollision
import CollisionIdeals.General.Galois.PolynomialCollisionPair
import CollisionIdeals.General.Galois.LocalInertia

/-!
# An inertia-moved sheet has a nonregular source coordinate

If both coordinates of a conjugate polynomial sheet lie in a valuation
ring, inertia gives another collision sheet with the same residues.
Local Keller collision rigidity makes the two sheets equal. Consequently
an inertia element that moves a sheet forces at least one of its source
coordinates outside the valuation ring.

This is a direct local argument, with no conjugate ramification-index
realization as an input. It does not prove that all conjugate coordinates
are regular or that inertia is trivial.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
  [Algebra (PolynomialMapBaseFunctionField F) N]

/-- A moved inertia sheet cannot have both source coordinates in the
valuation ring. Only the ground-field constants are assumed regular. -/
theorem exists_coordinate_not_mem_of_inertia_moves_conjugateSheet
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (V : ValuationSubring N) [Algebra ℂ V]
    (hGround : ∀ c : ℂ, (algebraMap ℂ V c : N) =
      algebraMap (PolynomialMapBaseFunctionField F) N
        (algebraMap ℂ (PolynomialMapBaseFunctionField F) c))
    (g σ : D.galoisGroup)
    (hInertia : σ ∈ inertiaGroupAt (PolynomialMapBaseFunctionField F) V)
    (hMoved : σ ∉ D.intermediateFixingSubgroup.map
      (MulAut.conj g).toMonoidHom) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N :=
      polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    ∃ i : Fin 2, polynomialConjugateSourceMap D g (MvPolynomial.X i) ∉ V := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra ℂ N :=
    polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  by_contra h
  push_neg at h
  change ∃ s ∈ V.inertiaSubgroup (PolynomialMapBaseFunctionField F),
    (s : D.galoisGroup) = σ at hInertia
  obtain ⟨s, hs, rfl⟩ := hInertia
  let inclusion : V →ₐ[ℂ] N :=
    { V.subtype with commutes' := hGround }
  let φ : PlanePolynomial →ₐ[ℂ] V :=
    MvPolynomial.aeval fun i => ⟨polynomialConjugateSourceMap D g (MvPolynomial.X i), h i⟩
  let ψ : PlanePolynomial →ₐ[ℂ] V :=
    MvPolynomial.aeval fun i => s • φ (MvPolynomial.X i)
  have hφ : inclusion.comp φ = polynomialConjugateSourceMap D g := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [φ, inclusion]
  have hψ : inclusion.comp ψ =
      polynomialConjugateSourceMap D ((s : D.galoisGroup) * g) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, ψ, φ, MvPolynomial.aeval_X]
    change (s : D.galoisGroup)
        (polynomialConjugateSourceMap D g (MvPolynomial.X i)) =
      polynomialConjugateSourceMap D ((s : D.galoisGroup) * g) (MvPolynomial.X i)
    rfl
  have hAgree (i : Fin 2) : φ (F i) = ψ (F i) := by
    apply Subtype.ext
    change inclusion (φ (F i)) = inclusion (ψ (F i))
    rw [← AlgHom.comp_apply, hφ, ← AlgHom.comp_apply, hψ]
    exact polynomialConjugateSourceMapOverImage_apply_F_eq
      D g ((s : D.galoisGroup) * g) i
  have hResidue (i : Fin 2) :
      ψ (MvPolynomial.X i) - φ (MvPolynomial.X i) ∈ IsLocalRing.maximalIdeal V := by
    rw [valuationInertia_eq_maximalIdealInertia] at hs
    simpa only [ψ, MvPolynomial.aeval_X] using hs (φ (MvPolynomial.X i))
  have hEqual : ψ = φ :=
    Planar.collisionMapPair_left_eq_right_of_residue_agreement F hKeller
      { left := ψ, right := φ, agree := fun i => (hAgree i).symm } hResidue
  apply polynomialConjugateSourceMap_ne_of_not_mem_conjugateFixingSubgroup
    D g (s : D.galoisGroup) hMoved
  rw [← hφ, ← hψ, hEqual]

end

end CollisionIdeals
