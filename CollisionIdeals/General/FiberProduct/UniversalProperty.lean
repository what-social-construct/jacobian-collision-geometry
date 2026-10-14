module

public import CollisionIdeals.General.Collision.Ideal

@[expose] public section

set_option autoImplicit false

namespace CollisionIdeals

universe u v w z

open MvPolynomial

noncomputable section

variable {R : Type u} [CommRing R]
variable {ι : Type v}
variable {κ : Type w}
variable {T : Type z} [CommRing T] [Algebra R T]
variable {F : κ → SourceRing R ι}

/-- The first projection on coordinate rings, followed by the collision quotient. -/
def collisionLeft (F : κ → SourceRing R ι) :
    SourceRing R ι →ₐ[R] CollisionRing F :=
  (Ideal.Quotient.mkₐ R (collisionIdeal F)).comp
    (leftRename (R := R) (ι := ι))

/-- The second projection on coordinate rings, followed by the collision quotient. -/
def collisionRight (F : κ → SourceRing R ι) :
    SourceRing R ι →ₐ[R] CollisionRing F :=
  (Ideal.Quotient.mkₐ R (collisionIdeal F)).comp
    (rightRename (R := R) (ι := ι))

@[simp]
theorem collisionLeft_apply
    (F : κ → SourceRing R ι) (p : SourceRing R ι) :
    collisionLeft F p =
      Ideal.Quotient.mk (collisionIdeal F) (leftRename p) := by
  rfl

@[simp]
theorem collisionRight_apply
    (F : κ → SourceRing R ι) (p : SourceRing R ι) :
    collisionRight F p =
      Ideal.Quotient.mk (collisionIdeal F) (rightRename p) := by
  rfl

/-- The two collision projections agree after applying each coordinate of `F`. -/
theorem collisionLeft_apply_F_eq_collisionRight_apply_F
    (F : κ → SourceRing R ι) (j : κ) :
    collisionLeft F (F j) = collisionRight F (F j) := by
  rw [collisionLeft_apply, collisionRight_apply, ← sub_eq_zero]
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_range_self j))

/--
A pair of maps out of the source coordinate ring which agree on all output
coordinates of `F`.
-/
structure CollisionMapPair
    (F : κ → SourceRing R ι) (T : Type z)
    [CommRing T] [Algebra R T] where
  left : SourceRing R ι →ₐ[R] T
  right : SourceRing R ι →ₐ[R] T
  agree : ∀ j, left (F j) = right (F j)

/-- Distinct maps in a collision map pair differ on at least one source
coordinate. -/
theorem exists_coordinate_moved_of_collision_maps_ne
    (c : CollisionMapPair F T)
    (hne : c.left ≠ c.right) :
    ∃ i : ι, c.left (X i) ≠ c.right (X i) := by
  by_contra h
  apply hne
  apply MvPolynomial.algHom_ext
  intro i
  by_contra hi
  exact h ⟨i, hi⟩

/-- Evaluate the two copies of the variables using a collision map pair. -/
def collisionPairMap
    (c : CollisionMapPair F T) :
    PairRing R ι →ₐ[R] T :=
  MvPolynomial.aeval
    (Sum.elim
      (fun i ↦ c.left (X i))
      (fun i ↦ c.right (X i)))

@[simp]
theorem collisionPairMap_comp_leftRename
    (c : CollisionMapPair F T) :
    (collisionPairMap c).comp (leftRename (R := R) (ι := ι)) = c.left := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [collisionPairMap, leftRename]

@[simp]
theorem collisionPairMap_comp_rightRename
    (c : CollisionMapPair F T) :
    (collisionPairMap c).comp (rightRename (R := R) (ι := ι)) = c.right := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [collisionPairMap, rightRename]

theorem collisionIdeal_le_collisionPairMap_ker
    (c : CollisionMapPair F T) :
    collisionIdeal F ≤ RingHom.ker (collisionPairMap c).toRingHom := by
  rw [collisionIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  change collisionPairMap c (leftRename (F j) - rightRename (F j)) = 0
  rw [map_sub]
  have hleft :
      collisionPairMap c (leftRename (F j)) = c.left (F j) := by
    exact AlgHom.congr_fun (collisionPairMap_comp_leftRename c) (F j)
  have hright :
      collisionPairMap c (rightRename (F j)) = c.right (F j) := by
    exact AlgHom.congr_fun (collisionPairMap_comp_rightRename c) (F j)
  rw [hleft, hright, c.agree j, sub_self]

/--
The map from the collision quotient induced by a pair of maps agreeing on
`F`.  This is the existence half of the collision ring's universal property.
-/
def collisionLift
    (c : CollisionMapPair F T) :
    CollisionRing F →ₐ[R] T :=
  Ideal.Quotient.liftₐ
    (collisionIdeal F)
    (collisionPairMap c)
    (collisionIdeal_le_collisionPairMap_ker c)

@[simp]
theorem collisionLift_comp_left
    (c : CollisionMapPair F T) :
    (collisionLift c).comp (collisionLeft F) = c.left := by
  apply MvPolynomial.algHom_ext
  intro i
  change collisionPairMap c (leftRename (X i)) = c.left (X i)
  exact AlgHom.congr_fun (collisionPairMap_comp_leftRename c) (X i)

@[simp]
theorem collisionLift_comp_right
    (c : CollisionMapPair F T) :
    (collisionLift c).comp (collisionRight F) = c.right := by
  apply MvPolynomial.algHom_ext
  intro i
  change collisionPairMap c (rightRename (X i)) = c.right (X i)
  exact AlgHom.congr_fun (collisionPairMap_comp_rightRename c) (X i)

/-- Restrict a map from the collision ring to its two source copies. -/
def collisionRestrict
    (h : CollisionRing F →ₐ[R] T) :
    CollisionMapPair F T where
  left := h.comp (collisionLeft F)
  right := h.comp (collisionRight F)
  agree j := by
    exact congrArg h (collisionLeft_apply_F_eq_collisionRight_apply_F F j)

@[simp]
theorem collisionRestrict_left
    (h : CollisionRing F →ₐ[R] T) :
    (collisionRestrict h).left = h.comp (collisionLeft F) := by
  rfl

@[simp]
theorem collisionRestrict_right
    (h : CollisionRing F →ₐ[R] T) :
    (collisionRestrict h).right = h.comp (collisionRight F) := by
  rfl

/--
Maps from the collision ring are determined by their restrictions to the
two source copies.
-/
theorem collisionHom_ext
    {h k : CollisionRing F →ₐ[R] T}
    (hleft :
      h.comp (collisionLeft F) = k.comp (collisionLeft F))
    (hright :
      h.comp (collisionRight F) = k.comp (collisionRight F)) :
    h = k := by
  apply DFunLike.ext _ _
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hpair :
      h.comp (Ideal.Quotient.mkₐ R (collisionIdeal F)) =
        k.comp (Ideal.Quotient.mkₐ R (collisionIdeal F)) := by
    apply MvPolynomial.algHom_ext
    intro s
    cases s with
    | inl i =>
        have hi := AlgHom.congr_fun hleft (X i)
        simpa [collisionLeft, leftRename] using hi
    | inr i =>
        have hi := AlgHom.congr_fun hright (X i)
        simpa [collisionRight, rightRename] using hi
  exact AlgHom.congr_fun hpair p

@[simp]
theorem collisionLift_collisionRestrict
    (h : CollisionRing F →ₐ[R] T) :
    collisionLift (collisionRestrict h) = h := by
  apply collisionHom_ext
  · rw [collisionLift_comp_left]
    rfl
  · rw [collisionLift_comp_right]
    rfl

@[simp]
theorem collisionRestrict_collisionLift
    (c : CollisionMapPair F T) :
    collisionRestrict (collisionLift c) = c := by
  cases c
  simp [collisionRestrict]

/--
The dimension-generic universal property of the collision ring:
maps from it are the same as pairs of maps from the source ring which agree
on every coordinate of `F`.
-/
def collisionUniversalEquiv
    (F : κ → SourceRing R ι) :
    (CollisionRing F →ₐ[R] T) ≃ CollisionMapPair F T where
  toFun := collisionRestrict
  invFun := collisionLift
  left_inv := collisionLift_collisionRestrict
  right_inv := collisionRestrict_collisionLift

end

end CollisionIdeals
