import FreudenthalSVLean.CubeZeroMeanL2
import FreudenthalSVLean.H1ZeroHilbertSpace

/-!
# The genuine closed Hilbert space of zero-mean cube pressures

For the continuous stage in manuscript Lemma `means`, cube support is
the fixed-point condition of a genuine bounded L2 indicator operator,
and zero mean is the kernel of pairing with the cube indicator. Their
intersection is closed and complete. Actual zero-extended pressure
functions map linearly onto this space, with exactly the true squared
L2 norm. No divergence surjectivity is inferred from these properties.
-/

open scoped BigOperators Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.CubeZeroMeanL2
open FreudenthalSVLean.H1ZeroL2Jet
open FreudenthalSVLean.WeakFaceTrace

noncomputable section

namespace FreudenthalSVLean.CubePressureHilbert

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

theorem cube_measurable : MeasurableSet cube := measurableSet_Icc

theorem cubeMask_memLp (q : ScalarL2) : MemLp (cube.indicator (q : Space → ℝ)) 2
    (volume : Measure Space) := (Lp.memLp q).indicator cube_measurable

def cubeMaskValue (q : ScalarL2) : ScalarL2 :=
  (cubeMask_memLp q).toLp (cube.indicator q)

theorem cubeMaskValue_ae (q : ScalarL2) : (cubeMaskValue q : Space → ℝ) =ᵐ[volume]
    cube.indicator (q : Space → ℝ) :=
  MemLp.coeFn_toLp (cubeMask_memLp q)

def cubeMaskLinear : ScalarL2 →ₗ[ℝ] ScalarL2 where
  toFun := cubeMaskValue
  map_add' q r := by
    apply Lp.ext
    filter_upwards [cubeMaskValue_ae (q + r),
      Lp.coeFn_add (cubeMaskValue q) (cubeMaskValue r),
      cubeMaskValue_ae q, cubeMaskValue_ae r,
      Lp.coeFn_add q r] with x ha hab hb hc hx
    rw [ha, hab]
    change cube.indicator (q + r : ScalarL2) x =
      cubeMaskValue q x + cubeMaskValue r x
    rw [hb, hc]
    by_cases hm : x ∈ cube
    · rw [indicator_of_mem hm, indicator_of_mem hm, indicator_of_mem hm]
      exact hx
    · rw [indicator_of_notMem hm, indicator_of_notMem hm, indicator_of_notMem hm, zero_add]
  map_smul' c q := by
    change cubeMaskValue (c • q) = c • cubeMaskValue q
    apply Lp.ext
    filter_upwards [cubeMaskValue_ae (c • q),
      Lp.coeFn_smul c (cubeMaskValue q), cubeMaskValue_ae q,
      Lp.coeFn_smul c q] with x ha hab hb hx
    rw [ha, hab]
    change cube.indicator (c • q : ScalarL2) x =
      c * cubeMaskValue q x
    rw [hb]
    by_cases hm : x ∈ cube
    · rw [indicator_of_mem hm, indicator_of_mem hm]
      exact hx
    · rw [indicator_of_notMem hm, indicator_of_notMem hm, mul_zero]

theorem cubeMaskLinear_norm_le (q : ScalarL2) : ‖cubeMaskLinear q‖ ≤ ‖q‖ := by
  change ‖cubeMaskValue q‖ ≤ ‖q‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cubeMaskValue_ae q] with x hx
  change ‖cubeMaskValue q x‖ ≤ _
  rw [hx]
  by_cases hm : x ∈ cube
  · rw [indicator_of_mem hm]
  · rw [indicator_of_notMem hm, norm_zero]
    exact norm_nonneg _

def cubeMask : ScalarL2 →L[ℝ] ScalarL2 :=
  cubeMaskLinear.mkContinuous 1 (fun q => by simpa only [one_mul] using cubeMaskLinear_norm_le q)

theorem cubeMask_toLp {f : Space → ℝ} (hf : MemLp f 2 volume) :
    cubeMask (hf.toLp f) = (hf.indicator cube_measurable).toLp (cube.indicator f) := by
  change (((Lp.memLp (hf.toLp f)).indicator cube_measurable).toLp
    (cube.indicator (hf.toLp f))) = _
  apply MemLp.toLp_congr
  filter_upwards [hf.coeFn_toLp] with x hx
  by_cases hm : x ∈ cube
  · rw [indicator_of_mem hm, indicator_of_mem hm, hx]
  · rw [indicator_of_notMem hm, indicator_of_notMem hm]

def cubeOne : ScalarL2 := indicatorConstLp 2 (measurableSet_Icc : MeasurableSet cube)
  ((isCompact_Icc : IsCompact cube).measure_lt_top.ne) 1

def cubeMean : ScalarL2 →L[ℝ] ℝ := innerSL ℝ cubeOne

theorem cubeMean_eq_integral (q : ScalarL2) : cubeMean q = ∫ x in cube, q x :=
  L2.inner_indicatorConstLp_one measurableSet_Icc
    ((isCompact_Icc : IsCompact cube).measure_lt_top.ne) q

def pressureHilbert : Submodule ℝ ScalarL2 :=
  LinearMap.ker (cubeMask - ContinuousLinearMap.id ℝ ScalarL2).toLinearMap ⊓
    LinearMap.ker cubeMean.toLinearMap

theorem mem_pressureHilbert (q : ScalarL2) : q ∈ pressureHilbert ↔
    cubeMask q = q ∧ cubeMean q = 0 := by
  simp only [pressureHilbert, Submodule.mem_inf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, sub_apply,
    ContinuousLinearMap.id_apply, sub_eq_zero]

theorem pressureHilbert_isClosed : IsClosed (pressureHilbert : Set ScalarL2) :=
  (cubeMask - ContinuousLinearMap.id ℝ ScalarL2).isClosed_ker.inter cubeMean.isClosed_ker

instance : CompleteSpace pressureHilbert := pressureHilbert_isClosed.completeSpace_coe

def pressureClassLinear : cubePressureFunctions →ₗ[ℝ] ScalarL2 where
  toFun q := q.property.1.toLp q.val
  map_add' q r := MemLp.toLp_add q.property.1 r.property.1
  map_smul' c q := MemLp.toLp_const_smul c q.property.1

theorem pressureClass_mem (q : cubePressureFunctions) : pressureClassLinear q ∈ pressureHilbert := by
  apply (mem_pressureHilbert _).mpr
  have he : cube.indicator q.val = q.val := by
    funext x
    by_cases hx : x ∈ cube
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, q.property.2.1 x hx]
  constructor
  · change cubeMask (q.property.1.toLp q.val) = q.property.1.toLp q.val
    rw [cubeMask_toLp]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall (congrFun he))
  · rw [cubeMean_eq_integral]
    change (∫ x in cube, (q.property.1.toLp q.val) x) = 0
    rw [integral_congr_ae (ae_restrict_of_ae q.property.1.coeFn_toLp)]
    calc
      _ = ∫ x, cube.indicator q.val x := (integral_indicator measurableSet_Icc).symm
      _ = 0 := by rw [he]; exact q.property.2.2

def pressureClass : cubePressureFunctions →ₗ[ℝ] pressureHilbert :=
  pressureClassLinear.codRestrict _ pressureClass_mem

theorem pressureClass_norm_square (q : cubePressureFunctions) :
    ‖pressureClass q‖ ^ 2 = ∫ x, (q.val x) ^ 2 := toLp_norm_square q.property.1

theorem pressureClass_surjective : Function.Surjective pressureClass := by
  intro q
  have hq := (mem_pressureHilbert q.val).mp q.property
  let f : Space → ℝ := cube.indicator q.val
  have hf : MemLp f 2 volume := (Lp.memLp q.val).indicator cube_measurable
  have hm : (∫ x, f x) = 0 := by
    change (∫ x, cube.indicator q.val x) = 0
    rw [integral_indicator cube_measurable, ← cubeMean_eq_integral]
    exact hq.2
  let Q : cubePressureFunctions := ⟨f, hf,
    (fun x hx => indicator_of_notMem hx q.val), hm⟩
  refine ⟨Q, ?_⟩
  apply Subtype.ext
  change cubeMask q.val = q.val
  exact hq.1

end FreudenthalSVLean.CubePressureHilbert
