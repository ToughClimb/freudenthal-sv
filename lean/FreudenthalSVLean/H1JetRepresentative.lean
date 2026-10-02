import FreudenthalSVLean.H1ZeroHilbertSpace
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
# Fixed linear actual representatives of H1_0 Hilbert jets

For the continuous divergence stage in manuscript Lemma `means`, a
single algebraic linear section selects actual H1_0 data for every
genuine Hilbert jet. Its true full H1 energy equals the squared Hilbert
norm. The section need not be pointwise continuous: all analytic norms
and weak derivatives are preserved exactly at the L2-class level.
This uses the proved jet range, not any assumed Sobolev representative.
-/

open scoped BigOperators
open MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.H1ZeroLinearity
open FreudenthalSVLean.H1ZeroL2Jet
open FreudenthalSVLean.H1ZeroHilbertSpace

noncomputable section

namespace FreudenthalSVLean.H1JetRepresentative

set_option backward.isDefEq.respectTransparency false

def jetClass : h1ZeroSpace →ₗ[ℝ] jetSpace := jetLinear.rangeRestrict

theorem representative_exists : ∃ S : jetSpace →ₗ[ℝ] h1ZeroSpace,
    ∀ W, jetLinear (S W) = W.val := by
  obtain ⟨S, hS⟩ := jetClass.exists_rightInverse_of_surjective jetLinear.range_rangeRestrict
  refine ⟨S, fun W => ?_⟩
  exact congrArg Subtype.val (LinearMap.congr_fun hS W)

def representative : jetSpace →ₗ[ℝ] h1ZeroSpace := Classical.choose representative_exists

theorem representative_class (W : jetSpace) : jetLinear (representative W) = W.val :=
  Classical.choose_spec representative_exists W

theorem representative_energy (W : jetSpace) :
    (∫ x, ((representative W).val.1 x) ^ 2) +
      ∑ i : Fin 3, ∫ x, ((representative W).val.2 i x) ^ 2 = ‖W‖ ^ 2 := by
  rw [← jetLinear_norm_square, representative_class]
  rfl

theorem representative_gradient_bound (W : jetSpace) :
    (∑ i : Fin 3, ∫ x, ((representative W).val.2 i x) ^ 2) ≤ ‖W‖ ^ 2 := by
  rw [← representative_energy]
  exact le_add_of_nonneg_left (integral_nonneg (fun _ => sq_nonneg _))

end FreudenthalSVLean.H1JetRepresentative
