import FreudenthalSVLean.FiniteClosedIntervalGluing
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Gradient bounds for continuous finite closed-convex gluing

For the manuscript's piecewise-polynomial Sobolev interface, a continuous
function on a finite closed convex cover of Euclidean space inherits a
global norm-difference bound from bounded local derivatives.  Restriction
to a straight line gives a finite closed order-connected interval cover;
the proved one-sided gluing theorem handles all interface points and
segments lying entirely in shared faces.  There is no generic assumption
that almost-everywhere differentiability gives weak differentiability.
-/

open scoped Topology
open Set

noncomputable section

namespace FreudenthalSVLean.FiniteClosedConvexGluing

set_option backward.isDefEq.respectTransparency false

theorem norm_difference_bound {I : Type*} [Finite I]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : I → Set E) (hclosed : ∀ i, IsClosed (s i))
    (hconvex : ∀ i, Convex ℝ (s i)) (hcover : ⋃ i, s i = univ)
    (f : E → F) (hf : Continuous f) (g : I → E → F)
    (dg : I → E → E →L[ℝ] F) (hmatch : ∀ i, EqOn f (g i) (s i))
    (hd : ∀ i x, HasFDerivAt (g i) (dg i x) x)
    (C : ℝ) (hbound : ∀ i x, x ∈ s i → ‖dg i x‖ ≤ C) (x y : E) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  let path : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hp : Continuous path := path.continuous_of_finiteDimensional
  let sets (i : I) : Set ℝ := path ⁻¹' s i
  have hc (i : I) : IsClosed (sets i) := (hclosed i).preimage hp
  have ho (i : I) : OrdConnected (sets i) := ((hconvex i).affine_preimage path).ordConnected
  have hcov : Icc (0 : ℝ) 1 ⊆ ⋃ i, sets i := by
    intro a ha
    have hm : path a ∈ ⋃ i, s i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp hm
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hdr (i : I) (a : ℝ) (_ha : a ∈ sets i) (_hb : a ∈ Ico (0 : ℝ) 1) :
      HasDerivAt (fun b => g i (path b)) (dg i (path a) (y - x)) a :=
    (hd i (path a)).comp_hasDerivAt a AffineMap.hasDerivAt_lineMap
  have hb (i : I) (a : ℝ) (ha : a ∈ sets i) (_hb : a ∈ Ico (0 : ℝ) 1) :
      ‖dg i (path a) (y - x)‖ ≤ C * ‖y - x‖ :=
    ((dg i (path a)).le_opNorm (y - x)).trans
      (mul_le_mul_of_nonneg_right (hbound i (path a) ha) (norm_nonneg _))
  have hr := FiniteClosedIntervalGluing.norm_difference_bound sets hc ho 0 1 (by norm_num)
    hcov (fun a => f (path a)) (hf.comp hp).continuousOn
    (fun i a => g i (path a)) (fun i a => dg i (path a) (y - x))
    (fun i a ha => hmatch i ha) hdr (C * ‖y - x‖) hb
  simpa only [path, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, mul_one] using hr

end FreudenthalSVLean.FiniteClosedConvexGluing
