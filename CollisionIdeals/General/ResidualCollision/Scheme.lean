module

public import CollisionIdeals.General.ResidualCollision.Algebra
public import CollisionIdeals.General.FiberProduct.Polynomial
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} {κ : Type w}

/-- The affine scheme whose coordinate ring is the source polynomial ring. -/
def sourceAffineScheme : Scheme :=
  Spec (.of (SourceRing R ι))

/--
The affine collision scheme.  Its coordinate ring is
`S / I_R(F)`, equivalently `A ⊗_B A`.
-/
def collisionAffineScheme (F : κ → SourceRing R ι) : Scheme :=
  Spec (.of (CollisionRing F))

section AffinePullback

variable {ι₀ κ₀ : Type v}

/-- The affine target carrying the coordinate functions indexed by `κ₀`. -/
def targetAffineScheme : Scheme :=
  Spec (.of (MvPolynomial κ₀ R))

/-- The affine-scheme morphism contravariantly induced by `F`. -/
def coordinateSchemeHom
    (F : κ₀ → SourceRing R ι₀) :
    sourceAffineScheme (R := R) (ι := ι₀) ⟶
      targetAffineScheme (R := R) (κ₀ := κ₀) :=
  Spec.map
    (CommRingCat.ofHom (coordinateAlgHom F).toRingHom)

/--
The concrete collision scheme is canonically the categorical affine
self-fiber product induced by `F`.
-/
noncomputable def collisionAffineSchemeIsoPullback
    (F : κ₀ → SourceRing R ι₀) :
    collisionAffineScheme F ≅
      pullback (coordinateSchemeHom F) (coordinateSchemeHom F) := by
  letI : Algebra (MvPolynomial κ₀ R) (SourceRing R ι₀) :=
    (coordinateAlgHom F).toRingHom.toAlgebra
  change
    Spec (.of (CollisionRing F)) ≅
      pullback
        (Spec.map
          (CommRingCat.ofHom (coordinateAlgHom F).toRingHom))
        (Spec.map
          (CommRingCat.ofHom (coordinateAlgHom F).toRingHom))
  exact
    Scheme.Spec.mapIso
        (collisionTensorEquiv F).symm.toRingEquiv.toCommRingCatIso.op ≪≫
      (pullbackSpecIso
        (MvPolynomial κ₀ R)
        (SourceRing R ι₀)
        (SourceRing R ι₀)).symm

end AffinePullback

/--
The diagonal factor of the collision scheme, presented in the pair
coordinate ring as `Spec(S / I_Δ)`.
-/
def diagonalCollisionScheme : Scheme :=
  Spec
    (.of
      (PairRing R ι ⧸
        diagonalIdeal (R := R) (ι := ι)))

/--
The first-colon residual collision scheme

`R_F° = Spec(S / (I_R(F) : I_Δ))`.

When the collision diagonal is clopen, the colon is also the saturation
`I_R(F) : I_Δ^∞`, and this affine scheme is the complementary clopen
off-diagonal factor.
-/
def offDiagonalCollisionScheme
    (F : κ → SourceRing R ι) : Scheme :=
  Spec (.of (OffDiagonalRing F))

/-- The diagonal collision factor is canonically the source affine scheme. -/
noncomputable def diagonalCollisionSchemeIsoSource :
    diagonalCollisionScheme (R := R) (ι := ι) ≅
      sourceAffineScheme (R := R) (ι := ι) :=
  Scheme.Spec.mapIso
    (RingEquiv.toCommRingCatIso
      (diagonalQuotientEquiv (R := R) (ι := ι)).symm).op

/--
The Chinese-remainder decomposition of the collision ring becomes a
coproduct decomposition of affine schemes:

`Spec(S / I_R) ≅ Spec(S / I_Δ) ⨿ Spec(S / I_off)`.
-/
noncomputable def collisionSchemeIsoDiagonalCoprodOffDiagonal
    (F : κ → SourceRing R ι)
    (q : CollisionRing F)
    (hq : IsCollisionOffDiagonalProjector F q) :
    collisionAffineScheme F ≅
      diagonalCollisionScheme (R := R) (ι := ι) ⨿
        offDiagonalCollisionScheme F := by
  let e :=
    collisionRingEquivDiagonalProdOffDiagonal F q hq
  exact
    Scheme.Spec.mapIso e.symm.toCommRingCatIso.op ≪≫
      (asIso
        (AlgebraicGeometry.coprodSpec
          (PairRing R ι ⧸
            diagonalIdeal (R := R) (ι := ι))
          (PairRing R ι ⧸
            collisionOffDiagonalIdeal F))).symm

/--
After identifying `Spec(S / I_Δ)` with the source, the collision scheme is
the disjoint union of the diagonal copy of the source and its canonical
off-diagonal collision scheme.
-/
noncomputable def collisionSchemeIsoSourceCoprodOffDiagonal
    (F : κ → SourceRing R ι)
    (q : CollisionRing F)
    (hq : IsCollisionOffDiagonalProjector F q) :
    collisionAffineScheme F ≅
      sourceAffineScheme (R := R) (ι := ι) ⨿
        offDiagonalCollisionScheme F :=
  collisionSchemeIsoDiagonalCoprodOffDiagonal F q hq ≪≫
    coprod.mapIso
      (diagonalCollisionSchemeIsoSource (R := R) (ι := ι))
      (Iso.refl _)

/--
An affine spectrum is empty exactly when its coordinate ring is a zero
ring.
-/
theorem offDiagonalCollisionScheme_isEmpty_iff_subsingleton
    (F : κ → SourceRing R ι) :
    IsEmpty (offDiagonalCollisionScheme F) ↔
      Subsingleton (OffDiagonalRing F) := by
  exact PrimeSpectrum.isEmpty_iff_subsingleton

/--
The off-diagonal collision scheme is empty exactly when its defining ideal
is the unit ideal.
-/
theorem offDiagonalCollisionScheme_isEmpty_iff_ideal_eq_top
    (F : κ → SourceRing R ι) :
    IsEmpty (offDiagonalCollisionScheme F) ↔
      collisionOffDiagonalIdeal F = ⊤ := by
  exact
    (offDiagonalCollisionScheme_isEmpty_iff_subsingleton F).trans
      Ideal.Quotient.subsingleton_iff

/-- The geometric formulation of off-diagonal vanishing for one map. -/
def CollisionOffDiagonalVanishing
    (F : κ → SourceRing R ι) : Prop :=
  IsEmpty (offDiagonalCollisionScheme F)

/--
When the off-diagonal collision scheme vanishes, it is canonically
isomorphic to the empty scheme.
-/
noncomputable def offDiagonalCollisionSchemeIsoEmpty
    (F : κ → SourceRing R ι)
    (h : CollisionOffDiagonalVanishing F) :
    offDiagonalCollisionScheme F ≅ (∅ : Scheme) := by
  letI : IsEmpty (offDiagonalCollisionScheme F) := h
  exact isInitialOfIsEmpty.uniqueUpToIso emptyIsInitial

/--
The geometric off-diagonal scheme is empty exactly when the obstruction
ideal `I_Δ / I_R(F)` vanishes.
-/
theorem collisionOffDiagonalVanishing_iff_obstructionIdeal_eq_bot
    (F : κ → SourceRing R ι) :
    CollisionOffDiagonalVanishing F ↔
      obstructionIdeal F = ⊥ := by
  rw [CollisionOffDiagonalVanishing,
    offDiagonalCollisionScheme_isEmpty_iff_subsingleton]
  exact
    (obstructionIdeal_eq_bot_iff_offDiagonalRing_subsingleton F).symm

/--
If the off-diagonal collision scheme is empty, the collision scheme is
scheme-theoretically just its diagonal factor.
-/
noncomputable def collisionSchemeIsoDiagonalOfOffDiagonalVanishing
    (F : κ → SourceRing R ι)
    (h : CollisionOffDiagonalVanishing F) :
    collisionAffineScheme F ≅
      diagonalCollisionScheme (R := R) (ι := ι) := by
  have hObstruction : obstructionIdeal F = ⊥ :=
    (collisionOffDiagonalVanishing_iff_obstructionIdeal_eq_bot F).mp h
  have hIdeals :
      collisionIdeal F =
        diagonalIdeal (R := R) (ι := ι) :=
    (obstructionIdeal_eq_bot_iff F).mp hObstruction
  exact
    Scheme.Spec.mapIso
      (RingEquiv.toCommRingCatIso
        (Ideal.quotEquivOfEq hIdeals).symm).op

/--
Equivalently, an empty off-diagonal collision scheme gives
`X ×_Y X ≅ Δ_X ≅ X` in the affine coordinate presentation.
-/
noncomputable def collisionSchemeIsoSourceOfOffDiagonalVanishing
    (F : κ → SourceRing R ι)
    (h : CollisionOffDiagonalVanishing F) :
    collisionAffineScheme F ≅
      sourceAffineScheme (R := R) (ι := ι) :=
  collisionSchemeIsoDiagonalOfOffDiagonalVanishing F h ≪≫
    diagonalCollisionSchemeIsoSource (R := R) (ι := ι)

section AffinePullbackVanishing

variable {ι₀ κ₀ : Type v}

/--
In categorical fiber-product language, off-diagonal vanishing gives
`X ×_Y X ≅ Δ_X`.
-/
noncomputable def selfFiberProductSchemeIsoDiagonalOfVanishing
    (F : κ₀ → SourceRing R ι₀)
    (h : CollisionOffDiagonalVanishing F) :
    pullback (coordinateSchemeHom F) (coordinateSchemeHom F) ≅
      diagonalCollisionScheme (R := R) (ι := ι₀) :=
  (collisionAffineSchemeIsoPullback F).symm ≪≫
    collisionSchemeIsoDiagonalOfOffDiagonalVanishing F h

/--
After identifying the diagonal with its source, off-diagonal vanishing gives
the scheme-theoretic endpoint `X ×_Y X ≅ Δ_X ≅ X`.
-/
noncomputable def selfFiberProductSchemeIsoSourceOfVanishing
    (F : κ₀ → SourceRing R ι₀)
    (h : CollisionOffDiagonalVanishing F) :
    pullback (coordinateSchemeHom F) (coordinateSchemeHom F) ≅
      sourceAffineScheme (R := R) (ι := ι₀) :=
  (collisionAffineSchemeIsoPullback F).symm ≪≫
    collisionSchemeIsoSourceOfOffDiagonalVanishing F h

end AffinePullbackVanishing

end

end CollisionIdeals
