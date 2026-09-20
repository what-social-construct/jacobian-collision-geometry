import CollisionIdeals.Planar.KellerFrame
import CollisionIdeals.General.Galois.PolynomialCollisionPair
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field

/-!
# The Keller frame on the marked normal closure

The polynomial Keller frame extends first to the source fraction field and
then to the finite separable marked normal closure. Both extensions are
constructed from base change for Kähler differentials along formally étale
maps; no extension-existence hypothesis is supplied.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals

noncomputable section

open scoped TensorProduct

section FormallyEtale

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
variable [Algebra.FormallyEtale A B]

/-- The canonical extension of a derivation through a formally étale map. -/
def derivationExtendFormallyEtale (d : Derivation R A A) : Derivation R B B :=
  (((Algebra.linearMap A B).comp d.liftKaehlerDifferential).liftBaseChange B).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).symm.toLinearMap
      |>.compDer (KaehlerDifferential.D R B)

@[simp]
theorem derivationExtendFormallyEtale_algebraMap
    (d : Derivation R A A) (a : A) :
    derivationExtendFormallyEtale (B := B) d (algebraMap A B a) =
      algebraMap A B (d a) := by
  simp [derivationExtendFormallyEtale,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

/-- A derivation on a formally étale extension is determined on the base. -/
theorem derivation_ext_formallyEtale (d₁ d₂ : Derivation R B B)
    (h : ∀ a : A, d₁ (algebraMap A B a) = d₂ (algebraMap A B a)) : d₁ = d₂ := by
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B
  have he : d₁.liftKaehlerDifferential.comp e.toLinearMap =
      d₂.liftKaehlerDifferential.comp e.toLinearMap := by
    ext b
    simp [e, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D,
      Derivation.liftKaehlerDifferential_comp_D, h]
  apply Derivation.ext
  intro b
  obtain ⟨x, hx⟩ := e.surjective (KaehlerDifferential.D R B b)
  rw [← Derivation.liftKaehlerDifferential_comp_D d₁,
    ← Derivation.liftKaehlerDifferential_comp_D d₂, ← hx]
  exact LinearMap.congr_fun he x

end FormallyEtale

/-- The two-variable chain rule for a derivation after polynomial evaluation. -/
theorem planarDerivation_chainRule {E : Type*} [CommRing E] [Algebra ℂ E]
    (δ : Derivation ℂ E E) (φ : PlanePolynomial →ₐ[ℂ] E) (p : PlanePolynomial) :
    δ (φ p) = φ (MvPolynomial.pderiv 0 p) * δ (φ (MvPolynomial.X 0)) +
      φ (MvPolynomial.pderiv 1 p) * δ (φ (MvPolynomial.X 1)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]; ring
  | mul_X p i hp =>
    fin_cases i <;> simp [Derivation.leibniz, hp] <;> ring

/-- Keller target coordinates determine a derivation on every polynomial sheet. -/
theorem planarDerivation_eq_of_target_values {E : Type*} [Field E] [Algebra ℂ E]
    (F : PlanarPolynomialMap) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c)
    (δ : Derivation ℂ E E) (φ : PlanePolynomial →ₐ[ℂ] E)
    (d : Derivation ℂ PlanePolynomial PlanePolynomial)
    (h : ∀ i, δ (φ (F i)) = φ (d (F i))) (p : PlanePolynomial) :
    δ (φ p) = φ (d p) := by
  have hchain (q : PlanePolynomial) :
      φ (d q) = φ (MvPolynomial.pderiv 0 q) * φ (d (MvPolynomial.X 0)) +
        φ (MvPolynomial.pderiv 1 q) * φ (d (MvPolynomial.X 1)) := by
    simpa only [AlgHom.id_apply, map_add, map_mul] using
      congrArg φ (planarDerivation_chainRule d (AlgHom.id ℂ PlanePolynomial) q)
  have hzero (i : Fin 2) :
      φ (MvPolynomial.pderiv 0 (F i)) *
          (δ (φ (MvPolynomial.X 0)) - φ (d (MvPolynomial.X 0))) +
      φ (MvPolynomial.pderiv 1 (F i)) *
          (δ (φ (MvPolynomial.X 1)) - φ (d (MvPolynomial.X 1))) = 0 := by
    have hi := h i
    rw [planarDerivation_chainRule δ φ, hchain] at hi
    linear_combination hi
  have hdet :
      φ (MvPolynomial.pderiv 0 (F 0)) * φ (MvPolynomial.pderiv 1 (F 1)) -
        φ (MvPolynomial.pderiv 1 (F 0)) * φ (MvPolynomial.pderiv 0 (F 1)) ≠ 0 := by
    have hj := congrArg φ hJ
    simp only [planarJacobianDet, jacobianDet_fin_two, map_sub, map_mul] at hj
    rw [hj]
    simpa using (algebraMap ℂ E).injective.ne hc
  have hx : δ (φ (MvPolynomial.X 0)) = φ (d (MvPolynomial.X 0)) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hdet
    linear_combination φ (MvPolynomial.pderiv 1 (F 1)) * hzero 0 -
      φ (MvPolynomial.pderiv 1 (F 0)) * hzero 1
  have hy : δ (φ (MvPolynomial.X 1)) = φ (d (MvPolynomial.X 1)) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hdet
    linear_combination φ (MvPolynomial.pderiv 0 (F 0)) * hzero 1 -
      φ (MvPolynomial.pderiv 0 (F 1)) * hzero 0
  rw [planarDerivation_chainRule δ φ, hchain, hx, hy]

/-- Extend a polynomial planar derivation to its source fraction field. -/
def planarDerivationFraction (d : Derivation ℂ PlanePolynomial PlanePolynomial) :
    Derivation ℂ (FractionRing PlanePolynomial) (FractionRing PlanePolynomial) := by
  letI : Algebra.FormallyEtale PlanePolynomial (FractionRing PlanePolynomial) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors PlanePolynomial)
  exact derivationExtendFormallyEtale d

@[simp]
theorem planarDerivationFraction_algebraMap
    (d : Derivation ℂ PlanePolynomial PlanePolynomial) (p : PlanePolynomial) :
    planarDerivationFraction d (algebraMap PlanePolynomial (FractionRing PlanePolynomial) p) =
      algebraMap PlanePolynomial (FractionRing PlanePolynomial) (d p) := by
  letI : Algebra.FormallyEtale PlanePolynomial (FractionRing PlanePolynomial) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors PlanePolynomial)
  unfold planarDerivationFraction
  exact derivationExtendFormallyEtale_algebraMap d p

variable {F : PlanarPolynomialMap} {N : Type} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

/-- The marked embedding supplies the source-function-field action on `N`. -/
def planarNormalExtensionSourceAlgebra (D : PolynomialNormalClosureData F N) :
    Algebra (PolynomialMapSourceFunctionField F) N :=
  D.embedding.toRingHom.toAlgebra

theorem planarNormalExtensionGroundSourceTower (D : PolynomialNormalClosureData F N) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    letI := planarNormalExtensionSourceAlgebra D
    IsScalarTower ℂ (PolynomialMapSourceFunctionField F) N := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI := planarNormalExtensionSourceAlgebra D
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap (PolynomialMapBaseFunctionField F) N
      (algebraMap ℂ (PolynomialMapBaseFunctionField F) c) =
    D.embedding (algebraMap ℂ (PolynomialMapSourceFunctionField F) c)
  rw [IsScalarTower.algebraMap_apply ℂ (PolynomialMapBaseFunctionField F)
    (PolynomialMapSourceFunctionField F), D.embedding.commutes]

/-- Extend any polynomial planar derivation to the marked normal closure. -/
def planarDerivationNormal (D : PolynomialNormalClosureData F N)
    (d : Derivation ℂ PlanePolynomial PlanePolynomial) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    Derivation ℂ N N := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI := planarNormalExtensionSourceAlgebra D
  letI := planarNormalExtensionGroundSourceTower D
  letI : IsScalarTower (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) N :=
    IsScalarTower.of_algebraMap_eq fun x => (D.embedding.commutes x).symm
  letI : FiniteDimensional (PolynomialMapBaseFunctionField F) N := D.finiteNormal
  letI : FiniteDimensional (PolynomialMapSourceFunctionField F) N :=
    FiniteDimensional.right (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) N
  letI : Algebra.FormallyEtale (PolynomialMapSourceFunctionField F) N :=
    Algebra.FormallyEtale.of_isSeparable _ _
  exact derivationExtendFormallyEtale (planarDerivationFraction d)

@[simp]
theorem planarDerivationNormal_embedding
    (D : PolynomialNormalClosureData F N)
    (d : Derivation ℂ PlanePolynomial PlanePolynomial)
    (x : PolynomialMapSourceFunctionField F) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarDerivationNormal D d (D.embedding x) =
      D.embedding (planarDerivationFraction d x) := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI := planarNormalExtensionSourceAlgebra D
  letI := planarNormalExtensionGroundSourceTower D
  letI : IsScalarTower (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) N :=
    IsScalarTower.of_algebraMap_eq fun x => (D.embedding.commutes x).symm
  letI : FiniteDimensional (PolynomialMapBaseFunctionField F) N := D.finiteNormal
  letI : FiniteDimensional (PolynomialMapSourceFunctionField F) N :=
    FiniteDimensional.right (PolynomialMapBaseFunctionField F)
      (PolynomialMapSourceFunctionField F) N
  letI : Algebra.FormallyEtale (PolynomialMapSourceFunctionField F) N :=
    Algebra.FormallyEtale.of_isSeparable _ _
  exact derivationExtendFormallyEtale_algebraMap (planarDerivationFraction d) x

/-- On the marked polynomial sheet, extension recovers the original frame. -/
@[simp]
theorem planarDerivationNormal_polynomial
    (D : PolynomialNormalClosureData F N)
    (d : Derivation ℂ PlanePolynomial PlanePolynomial) (p : PlanePolynomial) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarDerivationNormal D d
        (D.embedding (algebraMap PlanePolynomial (PolynomialMapSourceFunctionField F) p)) =
      D.embedding (algebraMap PlanePolynomial (PolynomialMapSourceFunctionField F) (d p)) := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  rw [planarDerivationNormal_embedding, planarDerivationFraction_algebraMap]

/-- The first Keller derivation on the normal closure. -/
def planarKellerFirstFrameNormal (D : PolynomialNormalClosureData F N) (c : ℂ) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    Derivation ℂ N N :=
  planarDerivationNormal D (planarKellerFirstFrame F c)

/-- The second Keller derivation on the normal closure. -/
def planarKellerSecondFrameNormal (D : PolynomialNormalClosureData F N) (c : ℂ) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    Derivation ℂ N N :=
  planarDerivationNormal D (planarKellerSecondFrame F c)

/-- The extended first derivation is dual to the first target coordinate. -/
theorem planarKellerFirstFrameNormal_apply_first
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarKellerFirstFrameNormal D c
        (D.embedding (algebraMap PlanePolynomial (PolynomialMapSourceFunctionField F) (F 0))) = 1 := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  simp [planarKellerFirstFrameNormal, planarKellerFirstFrame_apply_first F c hc hJ]

theorem planarKellerFirstFrameNormal_apply_second
    (D : PolynomialNormalClosureData F N) (c : ℂ) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarKellerFirstFrameNormal D c
        (D.embedding (algebraMap PlanePolynomial (PolynomialMapSourceFunctionField F) (F 1))) = 0 := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  simp [planarKellerFirstFrameNormal, planarKellerFirstFrame_apply_second]

theorem planarKellerSecondFrameNormal_apply_first
    (D : PolynomialNormalClosureData F N) (c : ℂ) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarKellerSecondFrameNormal D c
        (D.embedding (algebraMap PlanePolynomial (PolynomialMapSourceFunctionField F) (F 0))) = 0 := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  simp [planarKellerSecondFrameNormal, planarKellerSecondFrame_apply_first]

/-- The extended second derivation is dual to the second target coordinate. -/
theorem planarKellerSecondFrameNormal_apply_second
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c) :
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarKellerSecondFrameNormal D c
        (D.embedding (algebraMap PlanePolynomial (PolynomialMapSourceFunctionField F) (F 1))) = 1 := by
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  simp [planarKellerSecondFrameNormal, planarKellerSecondFrame_apply_second F c hc hJ]

/-- A frame with constant target derivatives preserves every conjugate source ring. -/
theorem planarDerivationNormal_conjugate_polynomial
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c)
    (d : Derivation ℂ PlanePolynomial PlanePolynomial)
    (hd : ∀ i : Fin 2, ∃ r : ℂ, d (F i) = MvPolynomial.C r)
    (g : D.galoisGroup) (p : PlanePolynomial) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarDerivationNormal D d (polynomialConjugateSourceMap D g p) =
      polynomialConjugateSourceMap D g (d p) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI := planarNormalExtensionSourceAlgebra D
  letI := planarNormalExtensionGroundSourceTower D
  apply planarDerivation_eq_of_target_values F c hc hJ
  intro i
  have hi : polynomialConjugateSourceMap D g (F i) =
      D.embedding (algebraMap PlanePolynomial (PolynomialMapSourceFunctionField F) (F i)) := by
    simpa using polynomialConjugateSourceMapOverImage_apply_F_eq D g 1 i
  obtain ⟨r, hr⟩ := hd i
  rw [hi, planarDerivationNormal_polynomial, hr]
  change algebraMap (PolynomialMapSourceFunctionField F) N
      (algebraMap PlanePolynomial (PolynomialMapSourceFunctionField F) (MvPolynomial.C r)) = _
  rw [show (MvPolynomial.C r : PlanePolynomial) = algebraMap ℂ PlanePolynomial r from rfl,
    ← IsScalarTower.algebraMap_apply ℂ PlanePolynomial (PolynomialMapSourceFunctionField F),
    ← IsScalarTower.algebraMap_apply ℂ (PolynomialMapSourceFunctionField F) N]
  exact (polynomialConjugateSourceMap D g).commutes r |>.symm

theorem planarKellerFirstFrameNormal_conjugate_polynomial
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c)
    (g : D.galoisGroup) (p : PlanePolynomial) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarKellerFirstFrameNormal D c (polynomialConjugateSourceMap D g p) =
      polynomialConjugateSourceMap D g (planarKellerFirstFrame F c p) := by
  apply planarDerivationNormal_conjugate_polynomial D c hc hJ
  intro i
  fin_cases i
  · exact ⟨1, by simpa using planarKellerFirstFrame_apply_first F c hc hJ⟩
  · exact ⟨0, by simpa using planarKellerFirstFrame_apply_second F c⟩

theorem planarKellerSecondFrameNormal_conjugate_polynomial
    (D : PolynomialNormalClosureData F N) (c : ℂ) (hc : c ≠ 0)
    (hJ : planarJacobianDet F = MvPolynomial.C c)
    (g : D.galoisGroup) (p : PlanePolynomial) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra ℂ N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    planarKellerSecondFrameNormal D c (polynomialConjugateSourceMap D g p) =
      polynomialConjugateSourceMap D g (planarKellerSecondFrame F c p) := by
  apply planarDerivationNormal_conjugate_polynomial D c hc hJ
  intro i
  fin_cases i
  · exact ⟨0, by simpa using planarKellerSecondFrame_apply_first F c⟩
  · exact ⟨1, by simpa using planarKellerSecondFrame_apply_second F c hc hJ⟩

end

end CollisionIdeals
