import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp

/-!
# Volume integration on the reference coordinate-chain tetrahedron

The manuscript defines the reference Freudenthal tetrahedron by
`0 ≤ z ≤ y ≤ x ≤ 1`.  This module proves the Fubini bridge from the
three-dimensional Lebesgue volume integral on that region to its nested
interval-integral representation.  Compactness supplies every integrability
hypothesis; the simplex integral is not introduced as an algebraic formula.

Coordinates are represented by the product `ℝ × (ℝ × ℝ)`.  Transport to
`Fin 3 → ℝ` and to translated/permuted/scaled tetrahedra is a subsequent
formalization obligation.
-/

open MeasureTheory Set

noncomputable section

namespace FreudenthalSVLean.ReferenceChainMeasure

abbrev Point := ℝ × (ℝ × ℝ)

def triangleSet (t : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc 0 t ∧ p.2 ∈ Icc 0 p.1}

def chainSet : Set Point :=
  {p | p.1 ∈ Icc 0 1 ∧ p.2.1 ∈ Icc 0 p.1 ∧ p.2.2 ∈ Icc 0 p.2.1}

theorem triangleSet_isCompact (t : ℝ) : IsCompact (triangleSet t) := by
  have hclosed : IsClosed (triangleSet t) :=
    ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_const)).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd continuous_fst))
  apply (isCompact_Icc : IsCompact (Icc (0, 0) (t, t))).of_isClosed_subset hclosed
  intro p hp
  exact ⟨⟨hp.1.1, hp.2.1⟩, ⟨hp.1.2, hp.2.2.trans hp.1.2⟩⟩

theorem chainSet_isCompact : IsCompact chainSet := by
  have hy : Continuous (fun p : Point => p.2.1) := continuous_snd.fst
  have hz : Continuous (fun p : Point => p.2.2) := continuous_snd.snd
  have hclosed : IsClosed chainSet :=
    ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_const)).inter
        (((isClosed_le continuous_const hy).inter (isClosed_le hy continuous_fst)).inter
          ((isClosed_le continuous_const hz).inter (isClosed_le hz hy)))
  apply (isCompact_Icc : IsCompact (Icc ((0, (0, 0)) : Point)
    ((1, (1, 1)) : Point))).of_isClosed_subset hclosed
  intro p hp
  exact ⟨⟨hp.1.1, hp.2.1.1, hp.2.2.1⟩,
    ⟨hp.1.2, hp.2.1.2.trans hp.1.2, hp.2.2.2.trans (hp.2.1.2.trans hp.1.2)⟩⟩

/-- Fubini's theorem on a triangular coordinate section, for every continuous
integrand and every real upper endpoint. -/
theorem triangle_integral (t : ℝ) (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    (∫ p in triangleSet t, f p) = ∫ y in Icc 0 t, ∫ z in Icc 0 y, f (y, z) := by
  have hm := (triangleSet_isCompact t).measurableSet
  have hi := (hf.continuousOn.integrableOn_compact (μ := volume)
    (triangleSet_isCompact t)).integrable_indicator hm
  rw [← integral_indicator hm]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Icc 0 t
  · have hfun : (fun z => (triangleSet t).indicator f (y, z)) =
        (Icc 0 y).indicator (fun z => f (y, z)) := by
      funext z
      have hy' : 0 ≤ y ∧ y ≤ t := hy
      simp [triangleSet, indicator, hy']
    rw [hfun, integral_indicator measurableSet_Icc]
    simp [hy]
  · have hfun : (fun z => (triangleSet t).indicator f (y, z)) = 0 := by
      funext z
      have hy' : ¬ (0 ≤ y ∧ y ≤ t) := hy
      simp [triangleSet, indicator, hy']
    rw [hfun]
    simp [hy]

/-- The volume integral on the reference tetrahedron is its nested set
integral; no unproved simplex quadrature rule is assumed. -/
theorem chain_integral_set (f : Point → ℝ) (hf : Continuous f) :
    (∫ p in chainSet, f p) =
      ∫ x in Icc 0 1, ∫ y in Icc 0 x, ∫ z in Icc 0 y, f (x, y, z) := by
  have hm := chainSet_isCompact.measurableSet
  have hi := (hf.continuousOn.integrableOn_compact (μ := volume)
    chainSet_isCompact).integrable_indicator hm
  rw [← integral_indicator hm]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Icc 0 1
  · have hfun : (fun yz => chainSet.indicator f (x, yz)) =
        (triangleSet x).indicator (fun yz => f (x, yz)) := by
      funext yz
      have hx' : 0 ≤ x ∧ x ≤ 1 := hx
      simp [chainSet, triangleSet, indicator, hx']
    rw [hfun, integral_indicator (triangleSet_isCompact x).measurableSet]
    rw [triangle_integral x (fun yz => f (x, yz))
      (hf.comp (continuous_const.prodMk continuous_id))]
    simp [hx]
  · have hfun : (fun yz => chainSet.indicator f (x, yz)) = 0 := by
      funext yz
      have hx' : ¬ (0 ≤ x ∧ x ≤ 1) := hx
      simp [chainSet, indicator, hx']
    rw [hfun]
    simp [hx]

/-- Signed interval integrals agree with the positive-volume nested set
integrals on the ordered reference tetrahedron. -/
theorem chain_integral_interval (f : Point → ℝ) (hf : Continuous f) :
    (∫ p in chainSet, f p) =
      ∫ x in 0..(1 : ℝ), ∫ y in 0..x, ∫ z in 0..y, f (x, y, z) := by
  rw [chain_integral_set f hf, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  change (∫ y in Icc 0 x, ∫ z in Icc 0 y, f (x, y, z)) =
    ∫ y in 0..x, ∫ z in 0..y, f (x, y, z)
  rw [intervalIntegral.integral_of_le hx.1, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  change (∫ z in Icc 0 y, f (x, y, z)) = ∫ z in 0..y, f (x, y, z)
  rw [intervalIntegral.integral_of_le hy.1, ← integral_Icc_eq_integral_Ioc]

end FreudenthalSVLean.ReferenceChainMeasure
