import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Fixed bounded linear sections of surjective Hilbert operators

For the fixed linear continuous lift used in manuscript Lemma `means`,
surjectivity of a genuine bounded linear operator from a Hilbert space
implies a single bounded linear section. Restriction to the orthogonal
complement of its closed kernel is bijective, and the Banach inverse
theorem supplies the continuous inverse. This general result assumes
surjectivity; it does not prove surjectivity of cube divergence.
-/

open scoped Topology

noncomputable section

namespace FreudenthalSVLean.HilbertLinearSection

theorem section_of_surjective {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (f : E →L[ℝ] F)
    (hf : Function.Surjective f) : ∃ B : F →L[ℝ] E, ∀ y, f (B y) = y := by
  let K : Submodule ℝ E := f.ker
  let g : Kᗮ →L[ℝ] F := f.comp Kᗮ.subtypeL
  have hinj : g.ker = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    apply (Submodule.mem_bot ℝ).mpr
    have hxK : x.val ∈ K := hx
    have hz : x.val ∈ K ⊓ Kᗮ := ⟨hxK, x.property⟩
    rw [K.inf_orthogonal_eq_bot] at hz
    apply Subtype.ext
    exact (Submodule.mem_bot ℝ).mp hz
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    refine ⟨⟨x - K.starProjection x, K.sub_starProjection_mem_orthogonal x⟩, ?_⟩
    change f (x - K.starProjection x) = y
    have hp : f (K.starProjection x) = 0 := K.starProjection_apply_mem x
    rw [map_sub, hp, sub_zero, hx]
  let e := ContinuousLinearEquiv.ofBijective g hinj (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨Kᗮ.subtypeL.comp e.symm.toContinuousLinearMap, fun y => ?_⟩
  exact ContinuousLinearEquiv.ofBijective_apply_symm_apply g hinj
    (LinearMap.range_eq_top.mpr hsurj) y

end FreudenthalSVLean.HilbertLinearSection
