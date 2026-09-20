import CollisionIdeals.General.Keller.Basic
import CollisionIdeals.General.Normalization.BaseTransversality
import Mathlib.Data.Finsupp.Weight

/-!
# Monomial weights of Keller maps

The Jacobian at the origin has no zero column. Consequently, every source
coordinate occurs as a nonzero linear term in some component of a Keller
map. If every supported monomial of every component has nonnegative integer
weight, each source coordinate has nonnegative weight as well.

The support hypothesis is appropriate for monomial valuations with no
cancellation. Regularity of the component polynomials at an arbitrary
valuation does not itself imply this hypothesis.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

/-- Every source coordinate occurs linearly in some component of a Keller map. -/
theorem exists_linearCoeff_ne_zero_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) (i : Fin n) :
    ∃ j : Fin n, coeff (Finsupp.single i 1) (F j) ≠ 0 := by
  classical
  have hcoeff (j : Fin n) :
      constantCoeff (pderiv i (F j)) = coeff (Finsupp.single i 1) (F j) := by
    have h := coeff_X_mul_pderiv i (Finsupp.single i 1 + 0) (F j)
    rw [coeff_X_mul] at h
    simpa using h
  by_contra! hzero
  have hdet : constantCoeff (jacobianDet F) = 0 := by
    rw [jacobianDet, RingHom.map_det]
    apply Matrix.det_eq_zero_of_column_eq_zero i
    intro j
    change constantCoeff (pderiv i (F j)) = 0
    rw [hcoeff j, hzero j]
  obtain ⟨c, hc, hJ⟩ := hKeller
  rw [hJ, constantCoeff_C] at hdet
  exact hc hdet

/-- Nonnegative weights on the component supports of a Keller map force
nonnegative weights on all source coordinates. -/
theorem nonneg_weights_of_isKeller
    (F : PolynomialSelfMap k n) (hKeller : IsKeller F) (w : Fin n → ℤ)
    (hSupport : ∀ (j : Fin n) (m : Fin n →₀ ℕ),
      coeff m (F j) ≠ 0 → 0 ≤ Finsupp.weight w m) :
    ∀ i : Fin n, 0 ≤ w i := by
  intro i
  obtain ⟨j, hj⟩ := exists_linearCoeff_ne_zero_of_isKeller F hKeller i
  simpa only [Finsupp.weight_single, one_smul] using
    hSupport j (Finsupp.single i 1) hj

end

end CollisionIdeals
