import CollisionIdeals.Planar.Research.Vanishing.LowTotalDegreeFrame
import CollisionIdeals.Planar.Research.InvariantQuotientAction
import CollisionIdeals.General.Keller.ConjugateInvariantSections
import CollisionIdeals.General.Normalization.FilteredPolynomialDerivation
import CollisionIdeals.General.Normalization.DerivationFiniteStage

/-!
# Actual finite stable stages in total polynomial degree at most two

Bounded ground-polynomial degree in the finite conjugate-coordinate
presentation gives finite coefficient-field stages of the original
normal closure. The low-total-degree Keller frames preserve these
stages. Pulling a stage back to the existing invariant algebra and
mapping it to the existing quotient supplies a finite preserved base
module, so the torsion annihilator theorem forces its classes to vanish.

The total-degree bound is essential to this construction. It is not a
generic-degree-two hypothesis or a theorem for arbitrary planar maps.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open MvPolynomial

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance totalDegreeStageBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

@[reducible] local instance totalDegreeStageBaseFieldAlgebra :
    Algebra (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) :=
  OreLocalization.instAlgebra

local instance totalDegreeStageBaseFieldSMul :
    SMul (PolynomialImageAlgebra F) (PolynomialMapBaseFunctionField F) := Algebra.toSMul

@[reducible] local instance totalDegreeStageConjugateAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateAlgebra D)

@[reducible] local instance totalDegreeStageInvariantAlgebra
    (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D) :=
  Subalgebra.algebra (polynomialConjugateInvariantAlgebra D)

/-- Every actual invariant boundary class vanishes in total polynomial
degree at most two. Finite-stage preservation is constructed internally;
no coherent-stage or uniform-denominator premise is supplied. -/
theorem planarKellerInvariantQuotient_eq_zero_of_totalDegree_le_two
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = C c)
    (hDegree : ∀ j : Fin 2, (F j).totalDegree ≤ 2)
    (q : polynomialConjugateInvariantAlgebra D ⧸ LinearMap.range
      (Algebra.linearMap (PolynomialImageAlgebra F) (polynomialConjugateInvariantAlgebra D))) :
    q = 0 := by
  let B : Type := PolynomialImageAlgebra F
  let S : Type := polynomialConjugateInvariantAlgebra D
  letI : SMul B S := Algebra.toSMul
  letI : Module B S := Algebra.toModule
  let M : Type := S ⧸ LinearMap.range (Algebra.linearMap B S)
  letI : Module B M := Submodule.Quotient.module _
  let baseQuotientMulAction : MulAction B M := inferInstance
  letI : MulAction B M := baseQuotientMulAction
  let baseQuotientSMul : SMul B M := inferInstance
  letI : SMul B M := baseQuotientSMul
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI : IsScalarTower ℂ B N :=
    polynomialNormalExtensionGroundImageTower (F := F) (N := N)
  letI : Module ℂ S := Module.compHom S (algebraMap ℂ B)
  letI : Module ℂ M := Module.compHom M (algebraMap ℂ B)
  letI : IsScalarTower ℂ B S :=
    IsScalarTower.of_algebraMap_smul (fun (_ : ℂ) (_ : S) => rfl)
  letI : IsScalarTower ℂ B M :=
    IsScalarTower.of_algebraMap_smul (fun (_ : ℂ) (_ : M) => rfl)
  letI := D.finiteIntermediate
  let e : PlanePolynomial ≃ₐ[ℂ] B :=
    AlgEquiv.ofInjective (coordinateAlgHom F)
      (coordinateAlgHom_injective_of_finiteDimensional F)
  let nabla : Fin 2 → M →+ M :=
    fun i => planarKellerInvariantQuotientOperator D c hc hJ i
  have hLeibniz : ∀ (i : Fin 2) (b : B) (m : M),
      nabla i (b • m) = polynomialEquivPartial e i b • m + b • nabla i m :=
    fun i b m => planarKellerInvariantQuotientOperator_leibniz D c hc hJ i b m
  letI : FiniteDimensional (PolynomialMapBaseFunctionField F) N := D.finiteNormal
  letI : Algebra.IsSeparable (PolynomialMapBaseFunctionField F) N := inferInstance
  letI : Finite D.galoisGroup := D.finiteGaloisGroup
  letI : Fintype D.galoisGroup := Fintype.ofFinite _
  let x : D.galoisGroup × Fin 2 → N :=
    fun gj => polynomialConjugateSourceMap D gj.1 (X gj.2)
  let delta : Fin 2 → Derivation ℂ N N :=
    Fin.cases (planarKellerFirstFrameNormal D c)
      (fun _ => planarKellerSecondFrameNormal D c)
  choose v hv hGenerator using
    (fun (i : Fin 2) (gj : D.galoisGroup × Fin 2) =>
      exists_affine_conjugateFrame_generator D c hc hJ hDegree i gj)
  have hGenerator' (i : Fin 2) (gj : D.galoisGroup × Fin 2) :
      delta i (x gj) = aeval x (v i gj) := hGenerator i gj
  let inclusion : S →ₗ[ℂ] N :=
    (((polynomialConjugateAlgebra D).val.comp
      (polynomialConjugateInvariantAlgebra D).val).toLinearMap).restrictScalars ℂ
  let projection : S →ₗ[ℂ] M :=
    ((LinearMap.range (Algebra.linearMap B S)).mkQ).restrictScalars ℂ
  have hInjective : Function.Injective inclusion := by
    intro z w h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hLift (i : Fin 2) (z : S) :
      inclusion (planarKellerInvariantFrame D c hc hJ i z) =
        delta i (inclusion z) :=
    planarKellerInvariantFrame_coe D c hc hJ i z
  have hProjection (i : Fin 2) (z : S) :
      projection (planarKellerInvariantFrame D c hc hJ i z) =
        planarKellerInvariantQuotientOperator D c hc hJ i (projection z) :=
    (planarKellerInvariantQuotientOperator_mk D c hc hJ i z).symm
  have hTorsion : Module.IsTorsion B M :=
    polynomialConjugateInvariantAlgebra_quotient_isTorsion D
  refine Submodule.Quotient.induction_on _ q ?_
  intro z
  obtain ⟨p, hp⟩ :=
    (polynomialConjugateAlgebra_mem_iff_exists_coordinatePolynomial D (z.val : N)).mp
      z.val.property
  have hz : inclusion z ∈ evaluationDegreeStage ℂ x p.totalDegree := by
    change (z.val : N) ∈ evaluationDegreeStage ℂ x p.totalDegree
    rw [← hp]
    exact aeval_mem_evaluationDegreeStage x p
  change projection z = 0
  exact eq_zero_of_mem_finite_stable_lift (B := B) (M := M)
    e nabla hLeibniz
    hTorsion inclusion hInjective projection
    (fun i => planarKellerInvariantFrame D c hc hJ i)
    (fun i => (delta i).toLinearMap.toAddMonoidHom)
    hLift hProjection (evaluationDegreeStage ℂ x p.totalDegree)
    (fun i n hn => derivation_mem_evaluationDegreeStage
      x (delta i) (v i) (hv i) (hGenerator' i) p.totalDegree hn) z hz

end

end CollisionIdeals
