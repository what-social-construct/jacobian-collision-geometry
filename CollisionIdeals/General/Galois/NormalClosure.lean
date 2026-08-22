import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Perfect

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

universe uK uL uN

/--
Data exhibiting `N` as a finite normal closure of the marked extension
`L / K`.

The distinguished embedding remembers the original copy of `L` inside
the normal closure.
-/
structure NormalClosureData
    (K : Type uK) (L : Type uL) (N : Type uN)
    [Field K] [Field L] [Field N]
    [Algebra K L] [Algebra K N] where
  embedding : L →ₐ[K] N
  normalClosure : IsNormalClosure K L N
  finiteIntermediate : FiniteDimensional K L
  finiteNormal : FiniteDimensional K N

namespace NormalClosureData

variable {K : Type uK} {L : Type uL} {N : Type uN}
variable [Field K] [Field L] [Field N]
variable [Algebra K L] [Algebra K N]

/-- A supplied normal closure is normal over its base field. -/
theorem normal
    (D : NormalClosureData K L N) :
    Normal K N := by
  letI : IsNormalClosure K L N := D.normalClosure
  exact IsNormalClosure.normal (F := K) (K := L) (L := N)

/-- The distinguished copy of `L` inside `N`. -/
def intermediateField
    (D : NormalClosureData K L N) :
    IntermediateField K N :=
  D.embedding.fieldRange

/-- The Galois group of the supplied normal closure. -/
abbrev galoisGroup
    (_D : NormalClosureData K L N) :=
  N ≃ₐ[K] N

/-- The subgroup fixing the distinguished intermediate field. -/
def intermediateFixingSubgroup
    (D : NormalClosureData K L N) :
    Subgroup D.galoisGroup :=
  D.intermediateField.fixingSubgroup

/-- The Galois group of the supplied finite normal closure is finite. -/
theorem finiteGaloisGroup
    (D : NormalClosureData K L N) :
    Finite D.galoisGroup := by
  letI : FiniteDimensional K N := D.finiteNormal
  infer_instance

/-- The fixed field of the distinguished fixing subgroup is the marked copy of `L`. -/
theorem fixedField_intermediateFixingSubgroup
    [PerfectField K]
    (D : NormalClosureData K L N) :
    IntermediateField.fixedField
        D.intermediateFixingSubgroup =
      D.intermediateField := by
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : Algebra.IsSeparable K N :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI : IsGalois K N := IsGalois.mk
  exact IsGalois.fixedField_fixingSubgroup D.intermediateField

/--
If the marked extension `L / K` is not normal, then the subgroup of the
normal-closure Galois group fixing the marked copy of `L` is nontrivial.

Indeed, a trivial fixing subgroup would have fixed field all of `N`.
Galois correspondence identifies that fixed field with the marked copy of
`L`, making the distinguished embedding `L →ₐ[K] N` an equivalence.  Normality
of the normal closure would then transfer back to `L / K`.
-/
theorem intermediateFixingSubgroup_ne_bot_of_not_normal
    [PerfectField K]
    (D : NormalClosureData K L N)
    (hNotNormal : ¬ Normal K L) :
    D.intermediateFixingSubgroup ≠ ⊥ := by
  intro hFixing
  have hIntermediate : D.intermediateField = ⊤ := by
    calc
      D.intermediateField =
          IntermediateField.fixedField D.intermediateFixingSubgroup :=
        D.fixedField_intermediateFixingSubgroup.symm
      _ = IntermediateField.fixedField
          (⊥ : Subgroup D.galoisGroup) := by rw [hFixing]
      _ = ⊤ := IntermediateField.fixedField_bot
  have hSurjective : Function.Surjective D.embedding := by
    intro z
    rw [← AlgHom.mem_fieldRange]
    change z ∈ D.intermediateField
    rw [hIntermediate]
    trivial
  let e : L ≃ₐ[K] N :=
    AlgEquiv.ofBijective D.embedding
      ⟨D.embedding.injective, hSurjective⟩
  exact hNotNormal ((e.transfer_normal).mpr D.normal)

/--
Because `N` is the actual normal closure of the marked copy of `L`, the
action of `Gal(N/K)` on its conjugate sheets is faithful. Equivalently,
the subgroup fixing `L` is core-free.
-/
theorem intermediateFixingSubgroup_normalCore_eq_bot
    [PerfectField K]
    (D : NormalClosureData K L N) :
    D.intermediateFixingSubgroup.normalCore = ⊥ := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Normal K N := D.normal
  letI : Algebra L N := D.embedding.toRingHom.toAlgebra
  letI : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (D.embedding.commutes x).symm
  let C := D.intermediateFixingSubgroup.normalCore
  have hNormalClosure :
      IntermediateField.normalClosure K L N = ⊤ := by
    letI : IsNormalClosure K L N := D.normalClosure
    exact
      (Algebra.IsAlgebraic.isNormalClosure_iff
        (F := K) (K := L) (L := N)).mp inferInstance |>.2
  have hle :
      IntermediateField.normalClosure K L N ≤
        IntermediateField.fixedField C := by
    rw [normalClosure_le_iff]
    intro f
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨x, rfl⟩ := hy
    let g : N ≃ₐ[K] N :=
      AlgEquiv.ofBijective
        (f.liftNormal N)
        (Algebra.IsAlgebraic.algHom_bijective
          (f.liftNormal N))
    have hconj :
        g⁻¹ * σ * (g⁻¹)⁻¹ ∈
          D.intermediateFixingSubgroup := by
      exact hσ g⁻¹
    have hfix :
        (g⁻¹ * σ * (g⁻¹)⁻¹) (D.embedding x) =
          D.embedding x := by
      exact
        (IntermediateField.mem_fixingSubgroup_iff
          D.intermediateField
          (g⁻¹ * σ * (g⁻¹)⁻¹)).mp hconj
          (D.embedding x) ⟨x, rfl⟩
    have hfix' := congrArg g hfix
    change
      g (g.symm (σ (g (D.embedding x)))) =
        g (D.embedding x) at hfix'
    have hfix'' :
        σ (g (D.embedding x)) =
          g (D.embedding x) := by
      simpa only [AlgEquiv.apply_symm_apply] using hfix'
    have hg :
        g (D.embedding x) = f x := by
      change
        (f.liftNormal N) (algebraMap L N x) =
          f x
      exact f.liftNormal_commutes N x
    change σ (f x) = f x
    simpa only [hg] using hfix''
  have hfixed :
      IntermediateField.fixedField C = ⊤ := by
    apply top_unique
    rw [← hNormalClosure]
    exact hle
  have hcorrespondence :
      (IntermediateField.fixedField C).fixingSubgroup = C :=
    IntermediateField.fixingSubgroup_fixedField C
  rw [hfixed] at hcorrespondence
  change C = ⊥
  simpa using hcorrespondence.symm

/--
The type-correct statement that the marked extension `L / K` is
trivial. Since the algebra map between fields is injective,
surjectivity is equivalent to its being an isomorphism.
-/
def IntermediateExtensionTrivial
    (K : Type uK) (L : Type uL)
    [Field K] [Field L] [Algebra K L] : Prop :=
  Function.Surjective (algebraMap K L)

/-- The type-correct statement that the normal extension `N / K` is trivial. -/
def ExtensionTrivial
    (_D : NormalClosureData K L N) : Prop :=
  Function.Surjective (algebraMap K N)

/--
If the marked extension `L / K` is trivial, then its supplied normal
closure is trivial over `K`.
-/
theorem extensionTrivial_of_intermediateExtensionTrivial
    (D : NormalClosureData K L N)
    (hL : IntermediateExtensionTrivial K L) :
    D.ExtensionTrivial := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  have hNormalClosure :
      IntermediateField.normalClosure K L N = ⊤ := by
    letI : IsNormalClosure K L N := D.normalClosure
    exact
      (Algebra.IsAlgebraic.isNormalClosure_iff
        (F := K) (K := L) (L := N)).mp inferInstance |>.2
  have hle :
      IntermediateField.normalClosure K L N ≤ ⊥ := by
    rw [normalClosure_le_iff]
    intro f
    rintro y ⟨x, rfl⟩
    obtain ⟨k, hk⟩ := hL x
    rw [← hk]
    change f (algebraMap K L k) ∈
      (⊥ : IntermediateField K N)
    rw [f.commutes]
    exact
      IntermediateField.algebraMap_mem
        (⊥ : IntermediateField K N) k
  have hbot : (⊥ : IntermediateField K N) = ⊤ := by
    apply top_unique
    rw [← hNormalClosure]
    exact hle
  intro z
  have hz : z ∈ (⊥ : IntermediateField K N) := by
    rw [hbot]
    trivial
  simpa only [IntermediateField.mem_bot] using hz

/--
If the supplied normal closure is already `K`, then the marked
intermediate extension `L / K` is trivial.
-/
theorem intermediateExtensionTrivial_of_extensionTrivial
    (D : NormalClosureData K L N)
    (hN : D.ExtensionTrivial) :
    IntermediateExtensionTrivial K L := by
  intro x
  obtain ⟨k, hk⟩ := hN (D.embedding x)
  refine ⟨k, D.embedding.injective ?_⟩
  change
    D.embedding (algebraMap K L k) =
      D.embedding x
  rw [D.embedding.commutes]
  exact hk

/-- For a supplied normal closure, `L = K` if and only if `N = K`. -/
theorem extensionTrivial_iff_intermediateExtensionTrivial
    (D : NormalClosureData K L N) :
    D.ExtensionTrivial ↔ IntermediateExtensionTrivial K L :=
  ⟨D.intermediateExtensionTrivial_of_extensionTrivial,
    D.extensionTrivial_of_intermediateExtensionTrivial⟩

/-- The algebra equivalence represented by triviality of `N / K`. -/
noncomputable def extensionEquivBase
    (D : NormalClosureData K L N)
    (h : D.ExtensionTrivial) :
    K ≃ₐ[K] N :=
  AlgEquiv.ofBijective
    (Algebra.ofId K N)
    ⟨(Algebra.ofId K N).injective, h⟩

/-- A trivial finite marked extension has degree one. -/
theorem intermediate_finrank_eq_one
    (D : NormalClosureData K L N)
    (hTrivial : IntermediateExtensionTrivial K L) :
    Module.finrank K L = 1 := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  apply finrank_eq_one (1 : L) one_ne_zero
  intro z
  obtain ⟨c, hc⟩ := hTrivial z
  exact ⟨c, by simpa [Algebra.smul_def] using hc⟩

end NormalClosureData

end

end CollisionIdeals
