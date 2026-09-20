import CollisionIdeals.General.Galois.MarkedGaloisGroup
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral closures in an intermediate field tower

The inclusion of function fields induces the actual map between their
integral closures. Finiteness and the upper Galois action are derived from
the field tower; no ramification-index equality is supplied as an input.
Apply this construction over the height-one localized base of
`LocalBaseChange`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

/-- A group fixing a field also fixes any base acting through that field.
No Dedekind, finiteness, or separability hypothesis is required. -/
theorem intermediateFieldGalois_baseCommutes
    (R L N H : Type*) [CommRing R] [Field L] [Field N]
    [Algebra R L] [Algebra R N] [Algebra L N] [IsScalarTower R L N]
    [Group H] [MulSemiringAction H N] [IsGaloisGroup H L N] :
    SMulCommClass H R N := by
  constructor
  intro g r x
  simpa only [IsScalarTower.algebraMap_smul] using
    (smul_comm g (algebraMap R L r) x)

section RingMap

variable (R L N : Type*) [CommRing R] [Field L] [Field N]
  [Algebra R L] [Algebra R N] [Algebra L N] [IsScalarTower R L N]

/-- Restriction of the field embedding to the integral closures. -/
abbrev intermediateNormalizationMap :
    integralClosure R L →ₐ[R] integralClosure R N :=
  (IsScalarTower.toAlgHom R L N).mapIntegralClosure

/-- The induced scalar structure between the two normalization rings. -/
abbrev intermediateNormalizationAlgebra :
    Algebra (integralClosure R L) (integralClosure R N) :=
  (intermediateNormalizationMap R L N).toRingHom.toAlgebra

local instance intermediateLocalTowerRingMapAlgebra :
    Algebra (integralClosure R L) (integralClosure R N) :=
  intermediateNormalizationAlgebra R L N

/-- The normalization map is the original field embedding on elements. -/
@[simp]
theorem intermediateNormalizationMap_coe (x : integralClosure R L) :
    (intermediateNormalizationMap R L N x : N) = algebraMap L N (x : L) := rfl

/-- Compatibility with the inclusions in the top function field. -/
theorem intermediateNormalization_isScalarTower :
    IsScalarTower (integralClosure R L) (integralClosure R N) N :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Compatibility with the common base. -/
theorem intermediateNormalization_base_isScalarTower :
    IsScalarTower R (integralClosure R L) (integralClosure R N) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply R L N r

end RingMap

section FiniteTower

variable (R K L N : Type*) [CommRing R] [IsDedekindDomain R]
  [Field K] [Field L] [Field N]
  [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra K N] [Algebra R L] [Algebra R N]
  [IsScalarTower R K L] [IsScalarTower R K N]
  [Algebra L N] [IsScalarTower R L N]
  [FiniteDimensional K L] [FiniteDimensional K N]
  [Algebra.IsSeparable K L] [Algebra.IsSeparable K N]

local instance intermediateLocalTowerFiniteAlgebra :
    Algebra (integralClosure R L) (integralClosure R N) :=
  intermediateNormalizationAlgebra R L N

local instance intermediateLocalTowerBaseTower :
    IsScalarTower R (integralClosure R L) (integralClosure R N) :=
  intermediateNormalization_base_isScalarTower R L N

local instance intermediateLocalTowerFieldTower :
    IsScalarTower (integralClosure R L) (integralClosure R N) N :=
  intermediateNormalization_isScalarTower R L N

include K in
omit [Algebra K L] [IsScalarTower R K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The top normalization is finite over the intermediate normalization,
because it is already finite over their common base. -/
theorem intermediateNormalization_finite :
    Module.Finite (integralClosure R L) (integralClosure R N) := by
  letI := IsIntegralClosure.finite R K N (integralClosure R N)
  exact Module.Finite.of_restrictScalars_finite R
    (integralClosure R L) (integralClosure R N)

omit [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra K N] [IsScalarTower R K L] [IsScalarTower R K N]
  [FiniteDimensional K L] [FiniteDimensional K N]
  [Algebra.IsSeparable K L] [Algebra.IsSeparable K N] in
/-- There is no torsion in the upper normalization extension. -/
theorem intermediateNormalization_isTorsionFree :
    Module.IsTorsionFree (integralClosure R L) (integralClosure R N) := by
  letI : Module.IsTorsionFree (integralClosure R L) N :=
    .trans_faithfulSMul (integralClosure R L) L N
  exact Function.Injective.moduleIsTorsionFree
    (IsScalarTower.toAlgHom (integralClosure R L) (integralClosure R N) N)
    Subtype.val_injective (fun r x => map_smul _ r x)

variable (H : Type*) [Group H] [MulSemiringAction H N] [IsGaloisGroup H L N]

/-- The upper field Galois action restricts to the top normalization. -/
abbrev intermediateNormalizationGaloisAction :
    MulSemiringAction H (integralClosure R N) := by
  letI : SMulCommClass H R N := intermediateFieldGalois_baseCommutes R L N H
  infer_instance

include K in
/-- The upper field Galois group is also the Galois group of the actual
normalization-ring extension. -/
theorem intermediateNormalization_isGaloisGroup :
    letI : SMulCommClass H R N := intermediateFieldGalois_baseCommutes R L N H
    IsGaloisGroup H (integralClosure R L) (integralClosure R N) := by
  letI : SMulCommClass H R N := intermediateFieldGalois_baseCommutes R L N H
  letI : IsDedekindDomain (integralClosure R L) :=
    integralClosure.isDedekindDomain R K L
  letI : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI : IsFractionRing (integralClosure R N) N :=
    integralClosure.isFractionRing_of_finite_extension K N
  letI := intermediateNormalization_finite R K L N
  exact IsGaloisGroup.of_isFractionRing H
    (integralClosure R L) (integralClosure R N) L N

end FiniteTower

section MarkedTower

variable (R K L N : Type*) [CommRing R] [IsDedekindDomain R]
  [Field K] [Field L] [Field N]
  [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra K N] [Algebra R L] [Algebra R N]
  [IsScalarTower R K L] [IsScalarTower R K N]
  [FiniteDimensional K L] [FiniteDimensional K N]
  [Algebra.IsSeparable K L] [IsGalois K N]

variable (ι : L →ₐ[K] N)

/-- The normalization-ring extension determined by a marked field embedding. -/
abbrev markedIntermediateNormalizationAlgebra :
    Algebra (integralClosure R L) (integralClosure R N) :=
  ((ι.restrictScalars R).mapIntegralClosure).toRingHom.toAlgebra

local instance intermediateLocalTowerGaloisCommutes :
    SMulCommClass (N ≃ₐ[K] N) R N :=
  intermediateFieldGalois_baseCommutes R K N (N ≃ₐ[K] N)

/-- The fixing subgroup of the marked field embedding is the actual upper
Galois group of the normalization rings, derived from the field theorem. -/
theorem markedIntermediateNormalization_isGaloisGroup :
    letI : Algebra (integralClosure R L) (integralClosure R N) :=
      markedIntermediateNormalizationAlgebra R K L N ι
    IsGaloisGroup ι.fieldRange.fixingSubgroup
      (integralClosure R L) (integralClosure R N) := by
  letI : Algebra (integralClosure R L) (integralClosure R N) :=
    markedIntermediateNormalizationAlgebra R K L N ι
  letI : Algebra L N := ι.toRingHom.toAlgebra
  letI : IsScalarTower R L N := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R N r = ι (algebraMap R L r)
    rw [IsScalarTower.algebraMap_apply R K N,
      IsScalarTower.algebraMap_apply R K L, ι.commutes])
  letI : IsGaloisGroup ι.fieldRange.fixingSubgroup L N :=
    fixingSubgroup_isGaloisGroup_of_embedding ι
  exact intermediateNormalization_isGaloisGroup R K L N ι.fieldRange.fixingSubgroup

end MarkedTower

end

end CollisionIdeals
