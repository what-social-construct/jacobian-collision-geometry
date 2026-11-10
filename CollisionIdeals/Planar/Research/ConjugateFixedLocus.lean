import CollisionIdeals.General.Galois.ConjugateInvariants
import CollisionIdeals.Planar.Basic
import CollisionIdeals.Planar.Research.EvaluatedProjector

/-!
# Fixed-locus certificates in the actual all-conjugate algebra

This file corestricts the existing conjugate source maps to the actual
all-conjugate algebra. The Keller secant projector shows that every
nonidentity Galois automorphism has an empty scheme-theoretic fixed locus
there. This concerns the affine all-conjugate algebra, not the omitted
normalization boundary; it does not exclude setwise-stable primes.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar.Research

open MvPolynomial

noncomputable section

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance normalExtensionBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

/-- The inherited ring structure, exposed so clients can form ideals,
quotients, and inertia without reconstructing the subalgebra's base. -/
@[reducible] instance conjugateAlgebraCommRing
    (D : PolynomialNormalClosureData F N) :
    CommRing (polynomialConjugateAlgebra D) :=
  Subalgebra.toCommRing (R := PolynomialImageAlgebra F) (A := N)
    (polynomialConjugateAlgebra D)

/-- The existing conjugate source map, corestricted to the algebra generated
by all conjugate source coordinates. -/
def conjugateSourceInAlgebraOverImage
    (D : PolynomialNormalClosureData F N) (g : D.galoisGroup) :
    PlanePolynomial →ₐ[PolynomialImageAlgebra F] polynomialConjugateAlgebra D :=
  (polynomialConjugateSourceMapOverImage D g).codRestrict
    (polynomialConjugateAlgebra D) (polynomialConjugateAlgebra_polynomial_mem D g)

@[simp]
theorem coe_conjugateSourceInAlgebraOverImage
    (D : PolynomialNormalClosureData F N) (g : D.galoisGroup)
    (p : PlanePolynomial) :
    ((conjugateSourceInAlgebraOverImage D g p : polynomialConjugateAlgebra D) : N) =
      polynomialConjugateSourceMapOverImage D g p := rfl

/-- The action carries the corestricted source sheet `g` to the sheet `σg`. -/
theorem smul_conjugateSourceInAlgebraOverImage
    (D : PolynomialNormalClosureData F N) (σ g : D.galoisGroup)
    (p : PlanePolynomial) :
    σ • conjugateSourceInAlgebraOverImage D g p =
      conjugateSourceInAlgebraOverImage D (σ * g) p := by
  apply Subtype.ext
  rfl

/-- A nonidentity automorphism moves at least one of the actual conjugate
source maps. Faithfulness alone is used; no perfect-base hypothesis is added. -/
theorem exists_conjugateSourceInAlgebraOverImage_ne
    (D : PolynomialNormalClosureData F N) (σ : D.galoisGroup) (hσ : σ ≠ 1) :
    ∃ g : D.galoisGroup,
      conjugateSourceInAlgebraOverImage D g ≠
        conjugateSourceInAlgebraOverImage D (σ * g) := by
  by_contra! h
  apply hσ
  apply FaithfulSMul.eq_of_smul_eq_smul (α := polynomialConjugateAlgebra D)
  rintro ⟨z, hz⟩
  apply Subtype.ext
  change σ z = z
  refine Algebra.adjoin_induction
    (p := fun z _ => σ z = z) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨⟨g, i⟩, rfl⟩
    have hp := AlgHom.congr_fun (h g) (X i)
    exact (congrArg Subtype.val hp).symm
  · intro b
    change σ (algebraMap (PolynomialMapBaseFunctionField F) N
      (algebraMap (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) b)) = _
    exact σ.commutes _
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy]
  · intro x y _ _ hx hy
    simp only [map_mul, hx, hy]

/-- The complex scalars on the actual all-conjugate algebra, through the
existing coordinate-image base. -/
@[reducible]
def conjugateAlgebraComplexAlgebra (D : PolynomialNormalClosureData F N) :
    Algebra ℂ (polynomialConjugateAlgebra D) :=
  ((algebraMap (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D)).comp
    (algebraMap ℂ (PolynomialImageAlgebra F))).toAlgebra

/-- Expose the canonical complex scalars for direct evaluation by clients. -/
@[reducible] instance conjugateComplexAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra ℂ (polynomialConjugateAlgebra D) :=
  conjugateAlgebraComplexAlgebra D

local instance conjugateComplexImageTower
    (D : PolynomialNormalClosureData F N) :
    IsScalarTower ℂ (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The corestricted conjugate source sheet as a complex-algebra map. -/
def conjugateSourceInAlgebra
    (D : PolynomialNormalClosureData F N) (g : D.galoisGroup) :
    PlanePolynomial →ₐ[ℂ] polynomialConjugateAlgebra D :=
  (conjugateSourceInAlgebraOverImage D g).restrictScalars ℂ

/-- The two actual conjugate sheets form a collision pair already in the
all-conjugate algebra, without passing to its fraction field. -/
def conjugateAlgebraCollisionPair
    (D : PolynomialNormalClosureData F N) (g σ : D.galoisGroup) :
    CollisionMapPair F (polynomialConjugateAlgebra D) where
  left := conjugateSourceInAlgebra D g
  right := conjugateSourceInAlgebra D (σ * g)
  agree i := by
    apply Subtype.ext
    exact polynomialConjugateSourceMapOverImage_apply_F_eq D g (σ * g) i

/-- Distinctness of the source maps is unchanged by restricting scalars. -/
theorem conjugateAlgebraCollisionPair_left_ne_right
    (D : PolynomialNormalClosureData F N) (g σ : D.galoisGroup)
    (hne : conjugateSourceInAlgebraOverImage D g ≠
      conjugateSourceInAlgebraOverImage D (σ * g)) :
    (conjugateAlgebraCollisionPair D g σ).left ≠
      (conjugateAlgebraCollisionPair D g σ).right := by
  intro h
  apply hne
  ext p
  exact congrArg Subtype.val (AlgHom.congr_fun h p)

/-- An actual pair of identical conjugate source sheets evaluates the
canonical off-diagonal projector to zero already in the all-conjugate algebra. -/
theorem conjugateAlgebraCollisionPair_projector_eq_zero
    (D : PolynomialNormalClosureData F N) (g σ : D.galoisGroup)
    (c : ℂ) (hc : c ≠ 0) (hJacobian : planarJacobianDet F = C c)
    (heq : (conjugateAlgebraCollisionPair D g σ).left =
      (conjugateAlgebraCollisionPair D g σ).right) :
    collisionLift (conjugateAlgebraCollisionPair D g σ)
      (Planar.ExplicitSecant.collisionProjector F c hc) = 0 := by
  exact collisionLift_explicitProjector_eq_zero_of_left_eq_right
    F c hc hJacobian (conjugateAlgebraCollisionPair D g σ) heq

/-- An actual pair of distinct conjugate source sheets evaluates the
canonical off-diagonal projector to one in the all-conjugate algebra. -/
theorem conjugateAlgebraCollisionPair_projector_eq_one
    (D : PolynomialNormalClosureData F N) (g σ : D.galoisGroup)
    (c : ℂ) (hc : c ≠ 0)
    (hne : conjugateSourceInAlgebraOverImage D g ≠
      conjugateSourceInAlgebraOverImage D (σ * g)) :
    collisionLift (conjugateAlgebraCollisionPair D g σ)
      (Planar.ExplicitSecant.collisionProjector F c hc) = 1 := by
  exact collisionLift_explicitProjector_eq_one_of_left_ne_right F c hc
    (conjugateAlgebraCollisionPair D g σ)
    (conjugateAlgebraCollisionPair_left_ne_right D g σ hne)

/-- Every nonidentity normal-closure automorphism has a unit difference ideal
in the actual all-conjugate algebra. This is the fixed-locus certificate. -/
theorem span_galoisDifferences_eq_top
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (σ : D.galoisGroup) (hσ : σ ≠ 1) :
    Ideal.span (Set.range fun z : polynomialConjugateAlgebra D => σ • z - z) = ⊤ := by
  obtain ⟨c, hc, hJacobian⟩ := hKeller
  obtain ⟨g, hne⟩ := exists_conjugateSourceInAlgebraOverImage_ne D σ hσ
  have hSpan := span_coordinateDifferences_eq_top_of_left_ne_right
    F c hc hJacobian (conjugateAlgebraCollisionPair D g σ)
    (conjugateAlgebraCollisionPair_left_ne_right D g σ hne)
  apply top_unique
  rw [← hSpan]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change conjugateSourceInAlgebraOverImage D g (X i) -
    conjugateSourceInAlgebraOverImage D (σ * g) (X i) ∈ _
  rw [← smul_conjugateSourceInAlgebraOverImage D σ g (X i)]
  have hmem : σ • conjugateSourceInAlgebraOverImage D g (X i) -
      conjugateSourceInAlgebraOverImage D g (X i) ∈
      Ideal.span (Set.range fun z : polynomialConjugateAlgebra D => σ • z - z) :=
    Ideal.subset_span ⟨_, rfl⟩
  simpa only [neg_sub] using
    (Ideal.span (Set.range fun z : polynomialConjugateAlgebra D => σ • z - z)).neg_mem hmem

/-- The closed fixed locus defined by the difference ideal of a nonidentity
Galois automorphism has empty underlying prime spectrum. -/
theorem zeroLocus_galoisDifferences_eq_empty
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (σ : D.galoisGroup) (hσ : σ ≠ 1) :
    PrimeSpectrum.zeroLocus
      (Ideal.span (Set.range fun z : polynomialConjugateAlgebra D => σ • z - z) :
        Set (polynomialConjugateAlgebra D)) = ∅ :=
  PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr
    (span_galoisDifferences_eq_top D hKeller σ hσ)

/-- The scheme-theoretic fixed quotient of a nonidentity automorphism is
the zero ring, not merely an empty set of rational fixed points. -/
theorem subsingleton_quotient_galoisDifferences
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (σ : D.galoisGroup) (hσ : σ ≠ 1) :
    Subsingleton ((polynomialConjugateAlgebra D) ⧸
      Ideal.span (Set.range fun z : polynomialConjugateAlgebra D => σ • z - z)) :=
  Ideal.Quotient.subsingleton_iff.mpr
    (span_galoisDifferences_eq_top D hKeller σ hσ)

/-- The existing inertia subgroup is trivial for every proper ideal of the
all-conjugate algebra. No assertion about setwise stabilizers or about primes
on the omitted normalization boundary is made. -/
theorem conjugateAlgebra_inertia_eq_bot
    (D : PolynomialNormalClosureData F N) (hKeller : IsPlanarKeller F)
    (I : Ideal (polynomialConjugateAlgebra D)) (hI : I ≠ ⊤) :
    Ideal.inertia D.galoisGroup I = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro σ hσ
  apply Subgroup.mem_bot.mpr
  by_contra hne
  have hle :
      Ideal.span (Set.range fun z : polynomialConjugateAlgebra D => σ • z - z) ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact hσ z
  rw [span_galoisDifferences_eq_top D hKeller σ hne] at hle
  exact hI (top_unique hle)

end

end CollisionIdeals.Planar.Research
