import CollisionIdeals.Planar.Research.SecantFrameDenominator
import CollisionIdeals.Planar.Research.KellerFrameExtension
import CollisionIdeals.General.Galois.PolynomialCollisionPair
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The evaluated first-jet secant--frame denominator

The coefficient family consists of the explicit ordered secant matrix and
its adjugate on every moved conjugate pair `(g, σg)`, followed by their
zeroth, first-frame, and second-frame derivatives.  The coefficient lattice
also contains the normalization ring.  Its denominator ideal is nonzero
because this is a finite family in the fraction field.

The denominator construction does not assert trace landing for arbitrary
boundary sections.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

/-- Derivations for the canonical ground-field structure on the closure. -/
abbrev NormalClosureDerivation
    (F : PlanarPolynomialMap) (N : Type) [Field N]
    [Algebra (PolynomialMapBaseFunctionField F) N] :=
  letI : Algebra ℂ N :=
    polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  Derivation ℂ N N

/-- Oriented conjugate pairs whose second sheet is moved by `C`.
For prime-order `C`, this is exactly the manuscript's pairs with
`C ⊈ gHg⁻¹` and `σ ≠ 1`.  It is meaningful for any subgroup. -/
def MovedConjugatePair
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup) :=
  {p : D.galoisGroup × C //
    (p.2 : D.galoisGroup) ∉
      D.intermediateFixingSubgroup.map (MulAut.conj p.1).toMonoidHom}

instance movedConjugatePair_finite
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup) :
    Finite (MovedConjugatePair D C) := by
  letI : Finite D.galoisGroup := D.finiteGaloisGroup
  unfold MovedConjugatePair
  infer_instance

/-- The ordered telescoping matrix from the explicit divided differences. -/
def explicitSecantMatrix (F : PlanarPolynomialMap) :
    Matrix (Fin 2) (Fin 2) (PairRing ℂ (Fin 2)) :=
  fun i j => if j = 0 then ExplicitSecant.first (F i)
    else ExplicitSecant.second (F i)

theorem explicitSecantMatrix_det (F : PlanarPolynomialMap) :
    (explicitSecantMatrix F).det = ExplicitSecant.determinant F := by
  simp [Matrix.det_fin_two, explicitSecantMatrix,
    ExplicitSecant.determinant, secantDet]

/-- The canonical pair evaluation, retaining only its ring-homomorphism
structure so no auxiliary ground-field instance is required by callers. -/
def conjugateSecantPairMap
    (D : PolynomialNormalClosureData F N) (g σ : D.galoisGroup) :
    PairRing ℂ (Fin 2) →+* N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra ℂ N :=
    polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  exact (collisionPairMap (polynomialGaloisCollisionPair D g σ)).toRingHom

/-- Evaluation of the actual secant matrix on `(g, σg)`. -/
def evaluatedSecantMatrix
    (D : PolynomialNormalClosureData F N) (g σ : D.galoisGroup) :
    Matrix (Fin 2) (Fin 2) N :=
  (explicitSecantMatrix F).map
    (conjugateSecantPairMap D g σ)

/-- Evaluation of the actual adjugate matrix on the same pair. -/
def evaluatedSecantAdjugate
    (D : PolynomialNormalClosureData F N) (g σ : D.galoisGroup) :
    Matrix (Fin 2) (Fin 2) N :=
  (evaluatedSecantMatrix D g σ).adjugate

/-- Taking the adjugate commutes with conjugate-pair evaluation. -/
theorem evaluatedSecantAdjugate_eq_map
    (D : PolynomialNormalClosureData F N) (g σ : D.galoisGroup) :
    evaluatedSecantAdjugate D g σ =
      (explicitSecantMatrix F).adjugate.map
        (conjugateSecantPairMap D g σ) := by
  exact (RingHom.map_adjugate
    (conjugateSecantPairMap D g σ)
    (explicitSecantMatrix F)).symm

/-- A moved pair, matrix/adjugate choice, row, column, and jet order
(`0`, `P`, or `Q`). -/
abbrev SecantFrameCoefficientIndex
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup) :=
  MovedConjugatePair D C × Fin 2 × Fin 2 × Fin 2 × Fin 3

/-- The evaluated matrix/adjugate first jets for two supplied derivations.
The canonical Keller-frame specialization is defined below. -/
def evaluatedSecantFrameCoefficient
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N)
    (i : SecantFrameCoefficientIndex D C) : N :=
  let g := i.1.val.1
  let σ : D.galoisGroup := i.1.val.2
  let a := (if i.2.1 = 0 then evaluatedSecantMatrix D g σ
    else evaluatedSecantAdjugate D g σ) i.2.2.1 i.2.2.2.1
  if i.2.2.2.2 = 0 then a
  else if i.2.2.2.2 = 1 then dP a else dQ a

/-- Include `1` among the finite generators, so the lattice contains `T`. -/
def evaluatedSecantFrameGenerator
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N)
    (i : Option (SecantFrameCoefficientIndex D C)) : N :=
  i.elim 1 (evaluatedSecantFrameCoefficient D C dP dQ)

variable (T : Type) [CommRing T] [Algebra T N]

/-- The actual finite coefficient lattice, including the copy of `T`. -/
def evaluatedSecantFrameLattice
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N) : Submodule T N :=
  Submodule.span T (Set.range (evaluatedSecantFrameGenerator D C dP dQ))

/-- The lattice is exactly `T` plus the span of the evaluated first jets. -/
theorem evaluatedSecantFrameLattice_eq_one_sup_span
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N) :
    evaluatedSecantFrameLattice T D C dP dQ =
      (1 : Submodule T N) ⊔ Submodule.span T
        (Set.range (evaluatedSecantFrameCoefficient D C dP dQ)) := by
  have hrange : Set.range (evaluatedSecantFrameGenerator D C dP dQ) =
      {1} ∪ Set.range (evaluatedSecantFrameCoefficient D C dP dQ) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inl rfl
      | some i => exact Or.inr ⟨i, rfl⟩
    · rintro (h | ⟨i, rfl⟩)
      · exact ⟨none, h.symm⟩
      · exact ⟨some i, rfl⟩
  rw [evaluatedSecantFrameLattice, hrange, Submodule.span_union,
    ← Submodule.one_eq_span]

theorem one_le_evaluatedSecantFrameLattice
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N) :
    (1 : Submodule T N) ≤ evaluatedSecantFrameLattice T D C dP dQ := by
  rw [evaluatedSecantFrameLattice_eq_one_sup_span]
  exact le_sup_left

/-- Multipliers clearing every evaluated first-jet coefficient into `T`. -/
def evaluatedSecantFrameDenominatorIdeal
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N) : Ideal T :=
  (1 : Submodule T N).colon (evaluatedSecantFrameLattice T D C dP dQ)

/-- Membership means that every actual evaluated first-jet coefficient is
cleared into the normalization ring. -/
theorem mem_evaluatedSecantFrameDenominatorIdeal_iff
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N) (s : T) :
    s ∈ evaluatedSecantFrameDenominatorIdeal T D C dP dQ ↔
      ∀ i, s • evaluatedSecantFrameCoefficient D C dP dQ i ∈
        (1 : Submodule T N) := by
  rw [evaluatedSecantFrameDenominatorIdeal, Submodule.mem_colon]
  constructor
  · intro h i
    exact h _ (Submodule.subset_span ⟨some i, rfl⟩)
  · intro h z hz
    refine Submodule.span_induction
      (p := fun z _ => s • z ∈ (1 : Submodule T N)) ?_ ?_ ?_ ?_ hz
    · rintro z ⟨i, rfl⟩
      cases i with
      | none =>
          apply (1 : Submodule T N).smul_mem s
          rw [Submodule.one_eq_span]
          exact Submodule.subset_span rfl
      | some i => exact h i
    · simp
    · intro x y hx hy ihx ihy
      simpa [smul_add] using (1 : Submodule T N).add_mem ihx ihy
    · intro a x hx ih
      rw [smul_smul, mul_comm, ← smul_smul]
      exact (1 : Submodule T N).smul_mem a ih

/-- This construction is an instance of the finite-denominator theorem;
the index contains precisely the evaluated matrix and frame data above. -/
theorem evaluatedSecantFrameDenominatorIdeal_ne_bot
    [IsDomain T] [IsFractionRing T N]
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (dP dQ : NormalClosureDerivation F N) :
    evaluatedSecantFrameDenominatorIdeal T D C dP dQ ≠ ⊥ := by
  letI : Fintype (Option (SecantFrameCoefficientIndex D C)) :=
    Fintype.ofFinite _
  let e := Fintype.equivFin (Option (SecantFrameCoefficientIndex D C))
  let coefficients := evaluatedSecantFrameGenerator D C dP dQ ∘ e.symm
  have hrange : Set.range coefficients =
      Set.range (evaluatedSecantFrameGenerator D C dP dQ) :=
    e.symm.surjective.range_comp _
  have h := finiteCoefficientDenominatorIdeal_ne_bot T N coefficients
  simpa only [finiteCoefficientDenominatorIdeal, finiteCoefficientSubmodule,
    evaluatedSecantFrameDenominatorIdeal, evaluatedSecantFrameLattice,
    hrange] using h

/-- The concrete first-jet coefficient family using the extended Keller
frame, rather than arbitrary supplied operators. -/
def secantFrameCoefficient
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (c : ℂ) : SecantFrameCoefficientIndex D C → N :=
  evaluatedSecantFrameCoefficient D C
    (planarKellerFirstFrameNormal D c) (planarKellerSecondFrameNormal D c)

/-- The manuscript's first-jet coefficient lattice `Λˢᶠ_{C,1}`. -/
def secantFrameLattice
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (c : ℂ) : Submodule T N :=
  evaluatedSecantFrameLattice T D C
    (planarKellerFirstFrameNormal D c) (planarKellerSecondFrameNormal D c)

/-- The manuscript's first-jet denominator ideal `𝔡ˢᶠ_{C,1}`. -/
def secantFrameDenominatorIdeal
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (c : ℂ) : Ideal T :=
  evaluatedSecantFrameDenominatorIdeal T D C
    (planarKellerFirstFrameNormal D c) (planarKellerSecondFrameNormal D c)

theorem secantFrameLattice_eq_one_sup_span
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (c : ℂ) :
    secantFrameLattice T D C c = (1 : Submodule T N) ⊔
      Submodule.span T (Set.range (secantFrameCoefficient D C c)) :=
  evaluatedSecantFrameLattice_eq_one_sup_span T D C _ _

theorem one_le_secantFrameLattice
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (c : ℂ) : (1 : Submodule T N) ≤ secantFrameLattice T D C c :=
  one_le_evaluatedSecantFrameLattice T D C _ _

theorem mem_secantFrameDenominatorIdeal_iff
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (c : ℂ) (s : T) :
    s ∈ secantFrameDenominatorIdeal T D C c ↔
      ∀ i, s • secantFrameCoefficient D C c i ∈ (1 : Submodule T N) :=
  mem_evaluatedSecantFrameDenominatorIdeal_iff T D C _ _ s

/-- The actual secant--frame ideal is nonzero; no landing or pole-witness
hypothesis is needed for this finite-denominator conclusion. -/
theorem secantFrameDenominatorIdeal_ne_bot
    [IsDomain T] [IsFractionRing T N]
    (D : PolynomialNormalClosureData F N) (C : Subgroup D.galoisGroup)
    (c : ℂ) : secantFrameDenominatorIdeal T D C c ≠ ⊥ :=
  evaluatedSecantFrameDenominatorIdeal_ne_bot T D C _ _

end

end CollisionIdeals.Planar
