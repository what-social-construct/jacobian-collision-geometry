import CollisionIdeals.Planar.ConjugateSecantEvaluation
import CollisionIdeals.Planar.Normalization
import CollisionIdeals.General.Galois.PolynomialCollisionPair

/-!
# Planar specialization of polynomial Galois collision map pairs

For a planar polynomial map `F`, a marked normal closure `N`, and Galois
elements `g` and `σ`, this file constructs the two source maps

`g : ℂ[x₁,x₂] → N` and `σg : ℂ[x₁,x₂] → N`.

The dimension-independent ground-field algebra, conjugate source maps,
stabilizer distinctness theorem, and Galois collision map pair are constructed
by `polynomialGaloisCollisionPair` in
`CollisionIdeals.General.Galois.PolynomialCollisionPair`.  This file supplies only the planar
off-diagonal specializations.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

open MvPolynomial

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/-- Distinct maps out of a polynomial ring differ on at least one variable. -/
theorem exists_coordinate_moved_of_collision_maps_ne
    {T : Type*} [CommRing T] [Algebra ℂ T]
    (c : CollisionMapPair F T)
    (hne : c.left ≠ c.right) :
    ∃ i : Fin 2, c.left (X i) ≠ c.right (X i) := by
  exact
    CollisionIdeals.exists_coordinate_moved_of_collision_maps_ne c hne

/--
A planar collision map pair with distinct source maps has a canonical
off-diagonal evaluation, using a classically chosen moved coordinate.
-/
noncomputable def planarOffDiagonalLiftOfLeftNeRight
    {T : Type*} [CommRing T] [IsDomain T] [Algebra ℂ T]
    (F : PlanarPolynomialMap)
    (hKeller : IsPlanarKeller F)
    (c : CollisionMapPair F T)
    (hne : c.left ≠ c.right) :
    OffDiagonalRing F →ₐ[ℂ] T :=
  let hi := exists_coordinate_moved_of_collision_maps_ne c hne
  planarOffDiagonalLift F hKeller c hi.choose hi.choose_spec

/--
The complex-algebra structure on the normal closure induced through the
base function field `ℂ(F₁,F₂)`.  It is named explicitly to avoid an
algebra-structure diamond with the coordinate-image algebra.
-/
noncomputable def normalExtensionComplexAlgebra : Algebra ℂ N :=
  polynomialNormalExtensionGroundAlgebra (F := F) (N := N)

/-- Compatibility of the explicit complex action with the action through
the coordinate-image algebra. -/
theorem normalExtensionComplexImageTower :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N :=
      normalExtensionComplexAlgebra (F := F) (N := N)
    IsScalarTower ℂ (PolynomialImageAlgebra F) N := by
  simpa only [normalExtensionComplexAlgebra] using
    (polynomialNormalExtensionGroundImageTower (F := F) (N := N))

/--
The polynomial source map for the conjugate sheet `g`, retained as a map
over the actual coordinate-image algebra.
-/
noncomputable def conjugateSourceMapOverImage
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    PlanePolynomial →ₐ[PolynomialImageAlgebra F] N :=
  polynomialConjugateSourceMapOverImage D g

@[simp]
theorem conjugateSourceMapOverImage_apply
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) (p : PlanePolynomial) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    conjugateSourceMapOverImage D g p =
      g (D.embedding
        (algebraMap PlanePolynomial
          (PolynomialMapSourceFunctionField F) p)) := by
  exact polynomialConjugateSourceMapOverImage_apply D g p

/-- Any two conjugate source maps agree on every output coordinate of `F`. -/
theorem conjugateSourceMapOverImage_apply_F_eq
    (D : PolynomialNormalClosureData F N)
    (g h : D.galoisGroup) (j : Fin 2) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    conjugateSourceMapOverImage D g (F j) =
      conjugateSourceMapOverImage D h (F j) := by
  exact polynomialConjugateSourceMapOverImage_apply_F_eq D g h j

/--
An element outside the stabilizer `gHg⁻¹` gives a genuinely distinct
conjugate polynomial sheet.  Equality on the polynomial source would extend
to its fraction field and force the element into that stabilizer.
-/
theorem conjugateSourceMapOverImage_ne_of_not_mem_conjugateFixingSubgroup
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup)
    (hσ : σ ∉ D.intermediateFixingSubgroup.map
      (MulAut.conj g).toMonoidHom) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    conjugateSourceMapOverImage D g ≠
      conjugateSourceMapOverImage D (σ * g) := by
  exact
    polynomialConjugateSourceMapOverImage_ne_of_not_mem_conjugateFixingSubgroup
      D g σ hσ

/-- The conjugate polynomial-source map, regarded as a complex-algebra map. -/
noncomputable def conjugateSourceMap
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N :=
      normalExtensionComplexAlgebra (F := F) (N := N)
    PlanePolynomial →ₐ[ℂ] N :=
  polynomialConjugateSourceMap D g

/--
The actual Galois collision map pair associated to the ordered pair of
conjugate sheets `(g, σg)`.
-/
noncomputable def galoisCollisionPair
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N :=
      normalExtensionComplexAlgebra (F := F) (N := N)
    CollisionMapPair F N :=
  polynomialGaloisCollisionPair D g σ

/-- The group-theoretic moved-sheet condition directly gives distinct maps
in the planar collision map pair. -/
theorem galoisCollisionPair_left_ne_right_of_not_mem
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup)
    (hσ : σ ∉ D.intermediateFixingSubgroup.map
      (MulAut.conj g).toMonoidHom) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N :=
      normalExtensionComplexAlgebra (F := F) (N := N)
    (galoisCollisionPair D g σ).left ≠
      (galoisCollisionPair D g σ).right := by
  simpa only [normalExtensionComplexAlgebra, galoisCollisionPair] using
    polynomialGaloisCollisionPair_left_ne_right_of_not_mem D g σ hσ

/--
If `σg` moves one source coordinate away from `g`, the actual Galois
collision map pair evaluates the planar off-diagonal ring in `N`.
-/
noncomputable def galoisOffDiagonalLift
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup)
    (hKeller : IsPlanarKeller F)
    (i : Fin 2)
    (hi :
      letI : Algebra (PolynomialImageAlgebra F) N :=
        polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
      letI : Algebra ℂ N :=
        normalExtensionComplexAlgebra (F := F) (N := N)
      (galoisCollisionPair D g σ).left (X i) ≠
        (galoisCollisionPair D g σ).right (X i)) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N :=
      normalExtensionComplexAlgebra (F := F) (N := N)
    OffDiagonalRing F →ₐ[ℂ] N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra ℂ N :=
    normalExtensionComplexAlgebra (F := F) (N := N)
  exact planarOffDiagonalLift F hKeller
    (galoisCollisionPair D g σ) i hi

/--
Coordinate-free version of `galoisOffDiagonalLift`: distinct conjugate
sheet maps automatically differ on one of the two polynomial coordinates.
-/
noncomputable def galoisOffDiagonalLiftOfDistinctSheets
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup)
    (hKeller : IsPlanarKeller F)
    (hne :
      letI : Algebra (PolynomialImageAlgebra F) N :=
        polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
      letI : Algebra ℂ N :=
        normalExtensionComplexAlgebra (F := F) (N := N)
      (galoisCollisionPair D g σ).left ≠
        (galoisCollisionPair D g σ).right) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N :=
      normalExtensionComplexAlgebra (F := F) (N := N)
    OffDiagonalRing F →ₐ[ℂ] N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra ℂ N :=
    normalExtensionComplexAlgebra (F := F) (N := N)
  exact planarOffDiagonalLiftOfLeftNeRight F hKeller
    (galoisCollisionPair D g σ) hne

/-- Canonical planar off-diagonal evaluation from the group-theoretic
moved-sheet condition `σ ∉ gHg⁻¹`. -/
noncomputable def galoisOffDiagonalLiftOfNotMem
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup)
    (hKeller : IsPlanarKeller F)
    (hσ : σ ∉ D.intermediateFixingSubgroup.map
      (MulAut.conj g).toMonoidHom) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N :=
      normalExtensionComplexAlgebra (F := F) (N := N)
    OffDiagonalRing F →ₐ[ℂ] N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra ℂ N :=
    normalExtensionComplexAlgebra (F := F) (N := N)
  exact galoisOffDiagonalLiftOfDistinctSheets D g σ hKeller
    (galoisCollisionPair_left_ne_right_of_not_mem D g σ hσ)

end

end CollisionIdeals.Planar
