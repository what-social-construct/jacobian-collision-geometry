import CollisionIdeals.General.Normalization.IntermediateLocalTower
import CollisionIdeals.General.Normalization.LocalIndex

/-!
# The local index for a marked normalization tower

The ring-theoretic Galois actions required by the tower formula are derived
from the marked field embedding. In particular the upper Galois group is
the actual fixing subgroup, not an independently supplied comparator.
The base here is already Dedekind, as obtained by localization at a divisor.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

attribute [local instance] Ideal.Quotient.field

variable (R K L N : Type u) [CommRing R] [IsDedekindDomain R]
  [Field K] [Field L] [Field N]
  [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra K N] [Algebra R L] [Algebra R N]
  [IsScalarTower R K L] [IsScalarTower R K N]
  [FiniteDimensional K L] [FiniteDimensional K N]
  [Algebra.IsSeparable K L] [IsGalois K N]

variable (ι : L →ₐ[K] N)

local instance : SMulCommClass (N ≃ₐ[K] N) R N :=
  intermediateFieldGalois_baseCommutes R K N (N ≃ₐ[K] N)

/-- The marked normalization tower has the expected local index. Both
Galois-ring certificates and the finite upper extension are constructed
from the field data. -/
theorem markedNormalization_localRamificationIndex_eq :
    letI : Algebra (integralClosure R L) (integralClosure R N) :=
      markedIntermediateNormalizationAlgebra R K L N ι
    ∀ (p : Ideal R) [p.IsMaximal] (_hp : p ≠ ⊥)
    (P : Ideal (integralClosure R L)) [P.IsMaximal] [P.LiesOver p]
    (Q : Ideal (integralClosure R N)) [Q.IsMaximal] [Q.LiesOver P] [Q.LiesOver p]
    [Algebra.IsSeparable (R ⧸ p) ((integralClosure R N) ⧸ Q)]
    [Algebra.IsSeparable ((integralClosure R L) ⧸ P) ((integralClosure R N) ⧸ Q)],
    localRamificationIndex (R := R) P =
      inertiaQuotientIndex (Q.inertia (N ≃ₐ[K] N)) ι.fieldRange.fixingSubgroup := by
  letI : Algebra (integralClosure R L) (integralClosure R N) :=
    markedIntermediateNormalizationAlgebra R K L N ι
  intro p _ hp P _ _ Q _ _ _ _ _
  let S : Type u := integralClosure R L
  let T : Type u := integralClosure R N
  letI : Algebra L N := ι.toRingHom.toAlgebra
  letI : IsScalarTower R L N := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R N r = ι (algebraMap R L r)
    rw [IsScalarTower.algebraMap_apply R K N,
      IsScalarTower.algebraMap_apply R K L, ι.commutes])
  letI : IsScalarTower R S T := intermediateNormalization_base_isScalarTower R L N
  letI : IsScalarTower S T N := intermediateNormalization_isScalarTower R L N
  letI : IsDedekindDomain S := integralClosure.isDedekindDomain R K L
  letI : IsDedekindDomain T := integralClosure.isDedekindDomain R K N
  letI : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  letI : IsFractionRing T N := integralClosure.isFractionRing_of_finite_extension K N
  letI : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  letI : Module.IsTorsionFree R N := .trans_faithfulSMul R K N
  letI : Module.IsTorsionFree R S := IsIntegralClosure.isTorsionFree R L (A := S)
  letI : Module.IsTorsionFree R T := IsIntegralClosure.isTorsionFree R N (A := T)
  letI : Module.IsTorsionFree S T := intermediateNormalization_isTorsionFree R L N
  letI : Module.Finite R T := IsIntegralClosure.finite R K N T
  letI : Module.Finite S T := intermediateNormalization_finite R K L N
  letI : IsGaloisGroup (N ≃ₐ[K] N) R T :=
    IsGaloisGroup.of_isFractionRing (N ≃ₐ[K] N) R T K N
  letI : IsGaloisGroup ι.fieldRange.fixingSubgroup S T :=
    markedIntermediateNormalization_isGaloisGroup R K L N ι
  exact localRamificationIndex_eq_inertiaQuotientIndex
    ι.fieldRange.fixingSubgroup p hp P Q

end

end CollisionIdeals
