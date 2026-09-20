import CollisionIdeals.General.Keller.Interfaces
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# The Jacobian criterion for a Keller map

The source has a graph presentation over its coordinate-image algebra.
Its Jacobian is the transpose of the original Jacobian matrix, so a Keller
map gives a standard-smooth presentation of relative dimension zero.
-/

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial AlgebraicGeometry

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}

private def imageCoordinate (F : PolynomialSelfMap k n) (i : Fin n) :
    polynomialMapImageAlgebra F :=
  ⟨F i, X i, coordinateAlgHom_X F i⟩

private def graphRelation (F : PolynomialSelfMap k n) (i : Fin n) :
    MvPolynomial (Fin n) (polynomialMapImageAlgebra F) :=
  (F i).map (algebraMap k (polynomialMapImageAlgebra F)) - C (imageCoordinate F i)

private theorem image_eval_map (F : PolynomialSelfMap k n) (p : SourceRing k (Fin n)) :
    aeval (R := polynomialMapImageAlgebra F) (X : Fin n → SourceRing k (Fin n))
      (p.map (algebraMap k (polynomialMapImageAlgebra F))) = p := by
  change ((aeval (R := polynomialMapImageAlgebra F) X).restrictScalars k |>.comp
    (mapAlgHom (Algebra.ofId k (polynomialMapImageAlgebra F)))) p = p
  have h : ((aeval (R := polynomialMapImageAlgebra F) (X : Fin n → SourceRing k (Fin n))).restrictScalars k).comp
      (mapAlgHom (Algebra.ofId k (polynomialMapImageAlgebra F))) = AlgHom.id k _ := by
    ext i
    simp
  rw [h]
  rfl

set_option maxHeartbeats 600000 in
private theorem graphRelation_ker (F : PolynomialSelfMap k n) :
    RingHom.ker (aeval (R := polynomialMapImageAlgebra F)
      (X : Fin n → SourceRing k (Fin n))).toRingHom =
      Ideal.span (Set.range (graphRelation F)) := by
  let B := polynomialMapImageAlgebra F
  let ev := aeval (R := B) (X : Fin n → SourceRing k (Fin n))
  let lift : SourceRing k (Fin n) →+* MvPolynomial (Fin n) B :=
    MvPolynomial.map (algebraMap k B)
  let J := Ideal.span (Set.range (graphRelation F))
  have hcoord (i : Fin n) : C (imageCoordinate F i) - lift (F i) ∈ J := by
    have hmem : graphRelation F i ∈ J := Ideal.subset_span ⟨i, rfl⟩
    have hneg : -graphRelation F i ∈ J :=
      (Ideal.neg_mem_iff (α := MvPolynomial (Fin n) B) J).mpr hmem
    dsimp only [graphRelation] at hneg
    change C (imageCoordinate F i) - (F i).map (algebraMap k B) ∈ J
    convert hneg using 1
    abel
  have hconst (b : B) : C b - lift (b : SourceRing k (Fin n)) ∈ J := by
    obtain ⟨p, hp⟩ := b.property
    have hb : b = (coordinateAlgHom F).rangeRestrict p := Subtype.ext hp.symm
    rw [hb]
    clear hb hp b
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [show (coordinateAlgHom F).rangeRestrict (C a) = algebraMap k B a from
        (coordinateAlgHom F).rangeRestrict.commutes a]
      simp [lift, MvPolynomial.algebraMap_eq]
    | add p q hp hq =>
      simp only [map_add, Subalgebra.coe_add]
      convert J.add_mem hp hq using 1
      abel
    | mul_X p i hp =>
      have hi : (coordinateAlgHom F).rangeRestrict (X i) = imageCoordinate F i :=
        Subtype.ext (coordinateAlgHom_X F i)
      simp only [map_mul, hi, Subalgebra.coe_mul]
      apply Ideal.mul_sub_mul_mem (α := MvPolynomial (Fin n) B) J
      · exact hp
      · exact hcoord i
  apply le_antisymm
  · intro p hp
    have hdiff : p - lift (ev p) ∈ J := by
      clear hp
      induction p using MvPolynomial.induction_on with
      | C b =>
        rw [show ev (C b) = (b : SourceRing k (Fin n)) from
          aeval_C (R := B) (X : Fin n → SourceRing k (Fin n)) b]
        exact hconst b
      | add p q hp hq =>
        simp only [map_add]
        convert J.add_mem hp hq using 1
        abel
      | mul_X p i hp =>
        rw [map_mul, show ev (X i) = X i from
          aeval_X (R := B) (X : Fin n → SourceRing k (Fin n)) i, map_mul,
          show lift (X i) = X i from MvPolynomial.map_X _ i]
        convert J.mul_mem_right (X i) hp using 1
        ring
    simp only [RingHom.mem_ker] at hp
    rw [show ev p = 0 from hp, map_zero] at hdiff
    convert hdiff using 1
    abel
  · rw [Ideal.span_le]
    rintro p ⟨i, rfl⟩
    simp [RingHom.mem_ker, graphRelation, image_eval_map, imageCoordinate]

/-- The graph presentation over the actual coordinate-image algebra. -/
def polynomialImageGraphPresentation (F : PolynomialSelfMap k n) :
    Algebra.PreSubmersivePresentation (polynomialMapImageAlgebra F)
      (SourceRing k (Fin n)) (Fin n) (Fin n) where
  val := X
  σ' p := p.map (algebraMap k (polynomialMapImageAlgebra F))
  aeval_val_σ' := image_eval_map F
  algebra := (aeval (R := polynomialMapImageAlgebra F)
    (X : Fin n → SourceRing k (Fin n))).toAlgebra
  algebraMap_eq := rfl
  relation := graphRelation F
  span_range_relation_eq_ker := (graphRelation_ker F).symm
  map := id
  map_inj := Function.injective_id

/-- The graph Jacobian is the original polynomial Jacobian determinant. -/
theorem polynomialImageGraphPresentation_jacobian (F : PolynomialSelfMap k n) :
    (polynomialImageGraphPresentation F).jacobian = jacobianDet F := by
  classical
  let P := polynomialImageGraphPresentation F
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Algebra.Generators.algebraMap_eq]
  change (aeval P.val).toRingHom P.jacobiMatrix.det = jacobianDet F
  rw [RingHom.map_det]
  have hmatrix :
      (aeval P.val).toRingHom.mapMatrix P.jacobiMatrix = (jacobianMatrix F).transpose := by
    ext i j
    simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
      P, polynomialImageGraphPresentation, graphRelation, pderiv_map,
      image_eval_map, jacobianMatrix, Matrix.transpose_apply]
  rw [hmatrix, Matrix.det_transpose]
  rfl

/-- The graph presentation of a Keller map is submersive. -/
def polynomialImageSubmersivePresentation
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    Algebra.SubmersivePresentation (polynomialMapImageAlgebra F)
      (SourceRing k (Fin n)) (Fin n) (Fin n) where
  toPreSubmersivePresentation := polynomialImageGraphPresentation F
  jacobian_isUnit := by
    obtain ⟨c, hc, hJ⟩ := hKeller
    rw [polynomialImageGraphPresentation_jacobian, hJ]
    exact (isUnit_iff_ne_zero.mpr hc).map C

/-- The Keller Jacobian condition implies actual algebraic étaleness over
the coordinate-image algebra, in every ambient dimension. -/
theorem polynomialSource_etale_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) :
    Algebra.Etale (polynomialMapImageAlgebra F) (SourceRing k (Fin n)) := by
  let P := polynomialImageSubmersivePresentation F hKeller
  letI := P.isStandardSmoothOfRelativeDimension (n := 0) (by
    simp [Algebra.Presentation.dimension])
  infer_instance

/-- The scheme-theoretic Keller étaleness interface is a theorem. -/
theorem kellerEtaleBridge (F : PolynomialSelfMap k n) : KellerEtaleBridge F := by
  intro hKeller
  exact HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr (polynomialSource_etale_of_isKeller F hKeller))

end

end CollisionIdeals
