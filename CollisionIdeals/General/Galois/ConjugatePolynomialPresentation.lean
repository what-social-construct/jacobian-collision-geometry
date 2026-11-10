import CollisionIdeals.General.Galois.ConjugateAlgebra
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# A ground-polynomial presentation of the existing conjugate algebra

The same all-conjugate algebra is the ground-field polynomial image of
the finite family of conjugate source coordinates. Its definition as a
base-image algebra is unchanged. Base coefficients need no extra
generators: every one is already a polynomial on the marked source sheet.

This presentation supplies polynomial representatives for bounded-degree
stages. It asserts no degree bound for arbitrary elements and no finite
module structure on the whole conjugate algebra.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open MvPolynomial

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

@[reducible] local instance conjugatePresentationBaseAlgebra :
    Algebra (PolynomialImageAlgebra F) N :=
  polynomialNormalExtensionBaseAlgebra (F := F) (N := N)

/-- Evaluate ground polynomials in the actual conjugate source coordinates.
The codomain is the original normal-closure field, not a replacement algebra. -/
def polynomialConjugateCoordinateEval (D : PolynomialNormalClosureData F N) :
    letI : Algebra k N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    MvPolynomial (D.galoisGroup × Fin n) k →ₐ[k] N := by
  letI : Algebra k N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  exact aeval fun gi => polynomialConjugateSourceMap D gi.1 (X gi.2)

/-- Restricting the coordinate presentation to a single sheet gives the
existing conjugate polynomial source map. -/
theorem polynomialConjugateCoordinateEval_comp_rename
    (D : PolynomialNormalClosureData F N) (g : D.galoisGroup) :
    letI : Algebra k N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    (polynomialConjugateCoordinateEval D).comp (rename fun i : Fin n => (g, i)) =
      polynomialConjugateSourceMap D g := by
  letI : Algebra k N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  apply MvPolynomial.algHom_ext
  intro i
  simp [polynomialConjugateCoordinateEval]

@[simp]
theorem polynomialConjugateCoordinateEval_rename
    (D : PolynomialNormalClosureData F N) (g : D.galoisGroup)
    (p : PolynomialSourceCoordinateRing k n) :
    letI : Algebra k N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    polynomialConjugateCoordinateEval D (rename (fun i : Fin n => (g, i)) p) =
      polynomialConjugateSourceMap D g p := by
  letI : Algebra k N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  exact AlgHom.congr_fun (polynomialConjugateCoordinateEval_comp_rename D g) p

/-- Ground polynomial evaluation has exactly the original conjugate algebra
as its range after restricting scalars. No alternate algebra is introduced. -/
theorem polynomialConjugateCoordinateEval_range
    (D : PolynomialNormalClosureData F N) :
    letI : Algebra k N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    letI : IsScalarTower k (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionGroundImageTower (F := F) (N := N)
    (polynomialConjugateCoordinateEval D).range =
      (polynomialConjugateAlgebra D).restrictScalars k := by
  letI : Algebra k N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI : IsScalarTower k (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionGroundImageTower (F := F) (N := N)
  apply le_antisymm
  · change (aeval (fun gi : D.galoisGroup × Fin n =>
      polynomialConjugateSourceMap D gi.1 (X gi.2))).range ≤ _
    rw [← Algebra.adjoin_range_eq_range_aeval]
    apply Algebra.adjoin_le
    rintro z ⟨⟨g, i⟩, rfl⟩
    exact polynomialConjugateAlgebra_coordinate_mem D g i
  · intro z hz
    change z ∈ Algebra.adjoin (PolynomialImageAlgebra F)
      (Set.range fun gi : D.galoisGroup × Fin n =>
        polynomialConjugateSourceMapOverImage D gi.1 (X gi.2)) at hz
    refine Algebra.adjoin_induction
      (p := fun z _ => z ∈ (polynomialConjugateCoordinateEval D).range)
      ?_ ?_ ?_ ?_ hz
    · rintro z ⟨⟨g, i⟩, rfl⟩
      refine ⟨X (g, i), ?_⟩
      simp [polynomialConjugateCoordinateEval]
    · intro b
      refine ⟨rename (fun i : Fin n => (1, i))
        (b : PolynomialSourceCoordinateRing k n), ?_⟩
      change polynomialConjugateCoordinateEval D
        (rename (fun i : Fin n => (1, i))
          (b : PolynomialSourceCoordinateRing k n)) = _
      rw [polynomialConjugateCoordinateEval_rename]
      change polynomialConjugateSourceMapOverImage D 1
        (algebraMap (PolynomialImageAlgebra F) (PolynomialSourceCoordinateRing k n) b) = _
      exact (polynomialConjugateSourceMapOverImage D 1).commutes b
    · intro x y _ _ hx hy
      exact (polynomialConjugateCoordinateEval D).range.add_mem hx hy
    · intro x y _ _ hx hy
      exact (polynomialConjugateCoordinateEval D).range.mul_mem hx hy

/-- Membership in the existing all-conjugate algebra is precisely
existence of a ground-polynomial representative in its coordinate family. -/
theorem polynomialConjugateAlgebra_mem_iff_exists_coordinatePolynomial
    (D : PolynomialNormalClosureData F N) (z : N) :
    letI : Algebra k N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    letI : IsScalarTower k (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionGroundImageTower (F := F) (N := N)
    z ∈ polynomialConjugateAlgebra D ↔
      ∃ p : MvPolynomial (D.galoisGroup × Fin n) k,
        polynomialConjugateCoordinateEval D p = z := by
  letI : Algebra k N := polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI : IsScalarTower k (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionGroundImageTower (F := F) (N := N)
  change z ∈ (polynomialConjugateAlgebra D).restrictScalars k ↔ _
  rw [← polynomialConjugateCoordinateEval_range]
  rfl

end

end CollisionIdeals
