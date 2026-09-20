import CollisionIdeals.General.GenericFiber.FunctionField
import CollisionIdeals.General.Galois.NormalClosure
import CollisionIdeals.General.Normalization.Model
import CollisionIdeals.General.Normalization.ImageGeometry
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Normalization models attached to a polynomial self-map

This file packages the dimension-independent normalization geometry of a
polynomial self-map.  It specializes the abstract field tower
`NormalClosureData K L N` and the relative integral-closure construction in
`NormalizationModel` to

`B = k[F₁, …, Fₙ] ⊂ A = k[x₁, …, xₙ] ⊂ L = k(x₁, …, xₙ) ⊂ N`.

The scheme-level API keeps all rings in one universe.  This avoids adding
universe-lift bookkeeping to the geometric constructions; all applications
over `ℂ` satisfy this convention.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {k : Type u} [Field k]
variable {n : ℕ}

/-- The polynomial coordinate ring of affine `n`-space over `k`. -/
abbrev PolynomialSourceCoordinateRing (k : Type u) [Field k] (n : ℕ) :=
  SourceRing k (Fin n)

/-- The coordinate-image algebra `k[F₁, …, Fₙ]`. -/
abbrev PolynomialImageAlgebra
    (F : PolynomialSelfMap k n) :=
  polynomialMapImageAlgebra F

/-- The source function field `L = k(x₁, …, xₙ)` attached to `F`. -/
abbrev PolynomialMapSourceFunctionField
    (_F : PolynomialSelfMap k n) :=
  PolynomialSourceFunctionField (R := k) (ι := Fin n)

/-- The image function field `K = Frac(k[F₁, …, Fₙ])`. -/
abbrev PolynomialMapBaseFunctionField
    (F : PolynomialSelfMap k n) :=
  PolynomialBaseFunctionField F

/--
Data exhibiting `N` as a finite normal closure of the function-field
extension induced by `F`.
-/
abbrev PolynomialNormalClosureData
    (F : PolynomialSelfMap k n)
    (N : Type u) [Field N]
    [Algebra (PolynomialMapBaseFunctionField F) N] :=
  NormalClosureData
    (PolynomialMapBaseFunctionField F)
    (PolynomialMapSourceFunctionField F)
    N

/--
Triviality of a polynomial map's marked normal closure forces triviality
of its induced source-function-field extension.
-/
theorem PolynomialNormalClosureData.functionFieldExtensionTrivial_of_extensionTrivial
    {F : PolynomialSelfMap k n}
    {N : Type u} [Field N]
    [Algebra (PolynomialMapBaseFunctionField F) N]
    (D : PolynomialNormalClosureData F N)
    (hN : NormalClosureData.ExtensionTrivial D) :
    PolynomialFunctionFieldExtensionTrivial F :=
  D.intermediateExtensionTrivial_of_extensionTrivial hN

/--
The integral closure of the coordinate-image algebra in the source
function field.
-/
abbrev PolynomialIntermediateNormalizationRing
    (F : PolynomialSelfMap k n) :=
  normalizedCoordinateRing
    (PolynomialImageAlgebra F)
    (PolynomialMapSourceFunctionField F)

/-- The intermediate normalized affine model `X̄ = Norm_L(Y)`. -/
def polynomialIntermediateNormalization
    (F : PolynomialSelfMap k n) : Scheme :=
  normalizedAffineModel
    (PolynomialImageAlgebra F)
    (PolynomialMapSourceFunctionField F)

/-- The canonical morphism `X̄ ⟶ Y = Spec k[F₁, …, Fₙ]`. -/
def polynomialIntermediateNormalizationToBase
    (F : PolynomialSelfMap k n) :
    polynomialIntermediateNormalization F ⟶
      Spec (.of (PolynomialImageAlgebra F)) :=
  normalizedModelToBase
    (PolynomialImageAlgebra F)
    (PolynomialMapSourceFunctionField F)

/--
The canonical map from affine `n`-space to its intermediate normalization.

For a Keller map, `General.Keller.Normalization` proves that this is an
open immersion using Zariski's main theorem.
-/
def polynomialSourceToIntermediateNormalization
    (F : PolynomialSelfMap k n) :
    Spec (.of (PolynomialSourceCoordinateRing k n)) ⟶
      polynomialIntermediateNormalization F :=
  intermediateToNormalization
    (B := PolynomialImageAlgebra F)
    (E := PolynomialMapSourceFunctionField F)
    (A := PolynomialSourceCoordinateRing k n)

/-- The intermediate-normalization map lies over the coordinate-image map. -/
theorem polynomialSourceToIntermediateNormalization_comp_toBase
    (F : PolynomialSelfMap k n) :
    polynomialSourceToIntermediateNormalization F ≫
        polynomialIntermediateNormalizationToBase F =
      polynomialSourceToImageBase F :=
  intermediateToNormalization_comp_toBase
    (B := PolynomialImageAlgebra F)
    (E := PolynomialMapSourceFunctionField F)
    (A := PolynomialSourceCoordinateRing k n)

/-- The Zariski-main open-immersion condition for the intermediate model. -/
def IsPolynomialSourceToIntermediateNormalizationOpenImmersion
    (F : PolynomialSelfMap k n) : Prop :=
  IsOpenImmersion (polynomialSourceToIntermediateNormalization F)

/-- The deleted boundary `X̄ ∖ X` of the intermediate affine-space model. -/
def polynomialIntermediateNormalizationBoundary
    (F : PolynomialSelfMap k n) :
    Set (polynomialIntermediateNormalization F) :=
  (Set.range (polynomialSourceToIntermediateNormalization F).base)ᶜ

/-- Finiteness of the integral closure defining the intermediate model. -/
def IsPolynomialIntermediateNormalizationFinite
    (F : PolynomialSelfMap k n) : Prop :=
  Module.Finite
    (PolynomialImageAlgebra F)
    (PolynomialIntermediateNormalizationRing F)

section NormalExtension

variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

/--
The `k[F₁, …, Fₙ]`-algebra structure on `N`, obtained through the base
function field.

It is explicit to avoid a typeclass diamond with other algebra structures
on a particular presentation of `N`.
-/
noncomputable def polynomialNormalExtensionBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  ((algebraMap (PolynomialMapBaseFunctionField F) N).comp
    (algebraMap (PolynomialImageAlgebra F)
      (PolynomialMapBaseFunctionField F))).toAlgebra

/--
The marked embedding `L ↪ N`, regarded as an algebra homomorphism over the
coordinate-image algebra.
-/
noncomputable def polynomialNormalClosureEmbeddingOverBase
    (D : PolynomialNormalClosureData F N) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    PolynomialMapSourceFunctionField F →ₐ[PolynomialImageAlgebra F] N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  exact
    { D.embedding.toRingHom with
      commutes' := fun b => by
        rw [IsScalarTower.algebraMap_apply
          (PolynomialImageAlgebra F)
          (PolynomialMapBaseFunctionField F)
          (PolynomialMapSourceFunctionField F)]
        exact D.embedding.commutes
          (algebraMap (PolynomialImageAlgebra F)
            (PolynomialMapBaseFunctionField F) b) }

/--
A Galois conjugate of the marked embedding, regarded as an algebra
homomorphism over the polynomial image algebra.

Using the same abstract source field for every conjugating element
identifies the normalization in a conjugate field with a conjugate copy of
the marked intermediate normalization.
-/
noncomputable def polynomialConjugateNormalClosureEmbeddingOverBase
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    PolynomialMapSourceFunctionField F →ₐ[PolynomialImageAlgebra F] N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  let gOverImage : N ≃ₐ[PolynomialImageAlgebra F] N :=
    { g.toRingEquiv with
      commutes' := fun b => by
        change
          g (algebraMap (PolynomialMapBaseFunctionField F) N
            (algebraMap (PolynomialImageAlgebra F)
              (PolynomialMapBaseFunctionField F) b)) =
            algebraMap (PolynomialMapBaseFunctionField F) N
              (algebraMap (PolynomialImageAlgebra F)
                (PolynomialMapBaseFunctionField F) b)
        exact g.commutes _ }
  exact
    gOverImage.toAlgHom.comp
      (polynomialNormalClosureEmbeddingOverBase D)

/-- Right multiplication by the fixing subgroup does not change a conjugate embedding. -/
theorem polynomialConjugateNormalClosureEmbeddingOverBase_right_mul
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup)
    (h : D.intermediateFixingSubgroup) :
    polynomialConjugateNormalClosureEmbeddingOverBase D
        (g * (h : D.galoisGroup)) =
      polynomialConjugateNormalClosureEmbeddingOverBase D g := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  apply AlgHom.ext
  intro x
  change g ((h : D.galoisGroup) (D.embedding x)) = g (D.embedding x)
  congr 1
  exact
    (IntermediateField.mem_fixingSubgroup_iff
      D.intermediateField (h : D.galoisGroup)).mp h.property
      (D.embedding x) ⟨x, rfl⟩

/-- The integral closure of the coordinate-image algebra in `N`. -/
abbrev PolynomialNormalizationInExtensionRing :=
  @normalizedCoordinateRing
    (PolynomialImageAlgebra F) N
    inferInstance inferInstance
    (polynomialNormalExtensionBaseAlgebra (F := F) (N := N))

/-- The relative integral-closure model `Z = Norm_N(Y)`. -/
def polynomialNormalizationInExtension : Scheme :=
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  normalizedAffineModel (PolynomialImageAlgebra F) N

/-- The canonical morphism `Z ⟶ Y`. -/
def polynomialNormalizationInExtensionToBase :
    polynomialNormalizationInExtension (F := F) (N := N) ⟶
      Spec (.of (PolynomialImageAlgebra F)) :=
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  normalizedModelToBase (PolynomialImageAlgebra F) N

/-- The normalization-ring map induced by the marked embedding `L ↪ N`. -/
def polynomialNormalizationRingMap
    (D : PolynomialNormalClosureData F N) :
    PolynomialIntermediateNormalizationRing F →ₐ[PolynomialImageAlgebra F]
      PolynomialNormalizationInExtensionRing (F := F) (N := N) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  exact
    normalizationMap N
      (polynomialNormalClosureEmbeddingOverBase D)

/-- The normalization-ring map for the conjugate sheet represented by a Galois element. -/
def polynomialConjugateNormalizationRingMap
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) :
    PolynomialIntermediateNormalizationRing F →ₐ[PolynomialImageAlgebra F]
      PolynomialNormalizationInExtensionRing (F := F) (N := N) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  exact
    normalizationMap N
      (polynomialConjugateNormalClosureEmbeddingOverBase D g)

/--
The normal-extension model dominates the marked intermediate
normalization: `Z ⟶ X̄`.
-/
def polynomialNormalClosureModelToIntermediateNormalization
    (D : PolynomialNormalClosureData F N) :
    polynomialNormalizationInExtension (F := F) (N := N) ⟶
      polynomialIntermediateNormalization F :=
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  normalizationDomination N
    (polynomialNormalClosureEmbeddingOverBase D)

/--
The conjugate normal-closure leg, with the conjugate target identified
abstractly with the marked intermediate normalization.
-/
def polynomialConjugateNormalClosureModelToIntermediateNormalization
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) :
    polynomialNormalizationInExtension (F := F) (N := N) ⟶
      polynomialIntermediateNormalization F :=
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  normalizationDomination N
    (polynomialConjugateNormalClosureEmbeddingOverBase D g)

/-- The conjugate normalization leg depends only on the right coset modulo the fixing subgroup. -/
theorem polynomialConjugateNormalClosureModelToIntermediateNormalization_right_mul
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup)
    (h : D.intermediateFixingSubgroup) :
    polynomialConjugateNormalClosureModelToIntermediateNormalization D
        (g * (h : D.galoisGroup)) =
      polynomialConjugateNormalClosureModelToIntermediateNormalization D g := by
  unfold polynomialConjugateNormalClosureModelToIntermediateNormalization
  rw [polynomialConjugateNormalClosureEmbeddingOverBase_right_mul D g h]

/-- The domination triangle `Z ⟶ X̄ ⟶ Y` commutes. -/
theorem polynomialNormalClosureModelToIntermediateNormalization_comp_toBase
    (D : PolynomialNormalClosureData F N) :
    polynomialNormalClosureModelToIntermediateNormalization D ≫
        polynomialIntermediateNormalizationToBase F =
      polynomialNormalizationInExtensionToBase (F := F) (N := N) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  exact
    normalizationDomination_comp_toBase N
      (polynomialNormalClosureEmbeddingOverBase D)

/-- Every conjugate normalization leg lies over the same affine base. -/
theorem polynomialConjugateNormalClosureModelToIntermediateNormalization_comp_toBase
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) :
    polynomialConjugateNormalClosureModelToIntermediateNormalization D g ≫
        polynomialIntermediateNormalizationToBase F =
      polynomialNormalizationInExtensionToBase (F := F) (N := N) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  exact
    normalizationDomination_comp_toBase N
      (polynomialConjugateNormalClosureEmbeddingOverBase D g)

/-- Finiteness of the integral closure in the normal extension. -/
def IsPolynomialFiniteNormalizationInExtension : Prop :=
  Module.Finite
    (PolynomialImageAlgebra F)
    (PolynomialNormalizationInExtensionRing (F := F) (N := N))

/--
The finite normalized cover attached to a polynomial function-field tower.

It packages the finite normal closure, finiteness of the intermediate and
normal normalization models, and the open immersion of the marked affine
sheet.  Ramification and boundary data belong to the later normalization
diagram.
-/
structure PolynomialNormalizedCover where
  normalClosure : PolynomialNormalClosureData F N
  finiteIntermediateModel :
    IsPolynomialIntermediateNormalizationFinite F
  finiteNormalClosureModel :
    IsPolynomialFiniteNormalizationInExtension (F := F) (N := N)
  intermediateOpen :
    IsPolynomialSourceToIntermediateNormalizationOpenImmersion F

end NormalExtension

end

end CollisionIdeals
