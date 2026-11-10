import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The canonical tensor map for a fixed-point-free finite-group action

The unit difference-ideal certificate makes distinct graph kernels
comaximal. Chinese remainders then make the canonical tensor map
surjective. This algebraic leaf does not assume that the scalar ring is
the invariant ring, and does not assert injectivity or étaleness.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar.Research.FiniteGroupCover

open scoped TensorProduct

variable (R S G : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- Evaluation on the graph of one group element. -/
def graphMap (g : G) : S ⊗[R] S →ₐ[R] S :=
  Algebra.TensorProduct.lift (AlgHom.id R S) (MulSemiringAction.toAlgHom R S g)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem graphMap_tmul (g : G) (a b : S) :
    graphMap R S G g (a ⊗ₜ[R] b) = a * (g • b) := rfl

/-- The canonical map to the product of all action graphs. -/
def canonicalMap : S ⊗[R] S →ₐ[R] (G → S) :=
  Pi.algHom R (fun _ : G => S) (graphMap R S G)

@[simp]
theorem canonicalMap_apply (t : S ⊗[R] S) (g : G) :
    canonicalMap R S G t g = graphMap R S G g t := rfl

@[simp]
theorem canonicalMap_tmul (a b : S) (g : G) :
    canonicalMap R S G (a ⊗ₜ[R] b) g = a * (g • b) := rfl

/-- The graph evaluations are surjective by their common left section. -/
theorem graphMap_surjective (g : G) : Function.Surjective (graphMap R S G g) := by
  intro a
  exact ⟨a ⊗ₜ[R] (1 : S), by simp⟩

/-- Distinct graph kernels are comaximal when nonidentity group elements
have unit difference ideals. -/
theorem graphMap_ker_isCoprime
    (hfree : ∀ g : G, g ≠ 1 →
      Ideal.span (Set.range fun z : S => g • z - z) = ⊤)
    {g h : G} (hgh : g ≠ h) :
    IsCoprime (RingHom.ker (graphMap R S G g))
      (RingHom.ker (graphMap R S G h)) := by
  let I := RingHom.ker (graphMap R S G g)
  let J := RingHom.ker (graphMap R S G h)
  have hnontriv : h * g⁻¹ ≠ 1 := by
    intro heq
    apply hgh
    exact (mul_inv_eq_one.mp heq).symm
  have hle : Ideal.span (Set.range fun z : S => (h * g⁻¹) • z - z) ≤
      Ideal.comap (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S) (I ⊔ J) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨z, rfl⟩
    let t : S ⊗[R] S := (1 : S) ⊗ₜ[R] (g⁻¹ • z)
    have hi : t - z ⊗ₜ[R] (1 : S) ∈ I := by
      change graphMap R S G g (t - z ⊗ₜ[R] (1 : S)) = 0
      simp [t]
    have hj : t - ((h * g⁻¹) • z) ⊗ₜ[R] (1 : S) ∈ J := by
      change graphMap R S G h (t - ((h * g⁻¹) • z) ⊗ₜ[R] (1 : S)) = 0
      simp [t, mul_smul]
    have hmem := (I ⊔ J).sub_mem
      (show t - z ⊗ₜ[R] (1 : S) ∈ I ⊔ J from (le_sup_left : I ≤ I ⊔ J) hi)
      (show t - ((h * g⁻¹) • z) ⊗ₜ[R] (1 : S) ∈ I ⊔ J from (le_sup_right : J ≤ I ⊔ J) hj)
    change ((h * g⁻¹) • z - z) ⊗ₜ[R] (1 : S) ∈ I ⊔ J
    simpa only [sub_sub_sub_cancel_left, TensorProduct.sub_tmul] using hmem
  rw [hfree (h * g⁻¹) hnontriv] at hle
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply (Ideal.eq_top_iff_one _).mpr
  have hmem := hle (show (1 : S) ∈ (⊤ : Ideal S) from trivial)
  simpa using hmem

/-- Chinese remainders turn the unit difference-ideal certificate into
surjectivity of the canonical tensor map. -/
theorem canonicalMap_surjective [Finite G]
    (hfree : ∀ g : G, g ≠ 1 →
      Ideal.span (Set.range fun z : S => g • z - z) = ⊤) :
    Function.Surjective (canonicalMap R S G) := by
  intro f
  have hcop : Pairwise (fun g h : G =>
      IsCoprime (RingHom.ker (graphMap R S G g)) (RingHom.ker (graphMap R S G h))) := by
    intro g h hgh
    exact graphMap_ker_isCoprime R S G hfree hgh
  obtain ⟨t, ht⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun g : G => f g ⊗ₜ[R] (1 : S))
  refine ⟨t, funext fun g => ?_⟩
  have hmem := ht g
  change graphMap R S G g (t - f g ⊗ₜ[R] (1 : S)) = 0 at hmem
  have heq : graphMap R S G g t - f g = 0 := by simpa using hmem
  exact sub_eq_zero.mp heq

end CollisionIdeals.Planar.Research.FiniteGroupCover
