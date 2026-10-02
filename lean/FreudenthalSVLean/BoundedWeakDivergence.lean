import FreudenthalSVLean.WeakH1ZeroGradientSupport
import FreudenthalSVLean.WeakH1ZeroCubeEnergy

/-!
# Actual bounded divergence on the genuine weak H1_0 cube space

For the continuous stage in manuscript Lemma `means`, the actual weak
divergence is represented by a fixed linear map into actual zero-mean
cube-supported L2 functions. Masking outside the cube only selects a
pointwise representative of the already proved weak gradient: the
result agrees almost everywhere with the genuine weak divergence.
Actual integration and Cauchy--Schwarz give squared L2 divergence
energy at most three times the full weak-gradient energy. Boundedness
of divergence is proved; surjectivity and a bounded inverse are not.
-/

open scoped BigOperators
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.CubeZeroMeanL2
open FreudenthalSVLean.H1ZeroLinearity
open FreudenthalSVLean.WeakH1ZeroGradientSupport

noncomputable section

namespace FreudenthalSVLean.BoundedWeakDivergence

set_option backward.isDefEq.respectTransparency false

def partialLinear (i : Fin 3) : h1ZeroSpace →ₗ[ℝ] cubePressureFunctions where
  toFun v := ⟨maskedGradient v.val.2 i,
    ((v.property.1.2 i).1.indicator (measurableSet_Icc : MeasurableSet cube)),
    (fun x hx => indicator_of_notMem hx (v.val.2 i)),
    (integral_congr_ae (maskedGradient_ae v.property i).symm).trans
      (inH1ZeroCube_gradient_integral_zero v.property i)⟩
  map_add' v w := by
    apply Subtype.ext
    funext x
    change cube.indicator (fun y => v.val.2 i y + w.val.2 i y) x =
      cube.indicator (v.val.2 i) x + cube.indicator (w.val.2 i) x
    by_cases hx : x ∈ cube
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, zero_add]
  map_smul' c v := by
    apply Subtype.ext
    funext x
    change cube.indicator (fun y => c * v.val.2 i y) x = c * cube.indicator (v.val.2 i) x
    by_cases hx : x ∈ cube
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

def weakDivergenceLinear : (Fin 3 → h1ZeroSpace) →ₗ[ℝ] cubePressureFunctions :=
  ∑ j : Fin 3, (partialLinear j).comp (LinearMap.proj j)

theorem weakDivergenceLinear_val (v : Fin 3 → h1ZeroSpace) :
    (weakDivergenceLinear v).val = fun x => ∑ j : Fin 3, maskedGradient (v j).val.2 j x := by
  simp only [weakDivergenceLinear, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.coe_sum]
  rfl

theorem weakDivergenceLinear_ae (v : Fin 3 → h1ZeroSpace) :
    (weakDivergenceLinear v).val =ᵐ[volume] (fun x => ∑ j : Fin 3, (v j).val.2 j x) := by
  rw [weakDivergenceLinear_val]
  have hall : ∀ᵐ x : Space ∂volume, ∀ j : Fin 3,
      maskedGradient (v j).val.2 j x = (v j).val.2 j x := by
    apply ae_all_iff.mpr
    intro j
    exact (maskedGradient_ae (v j).property j).symm
  filter_upwards [hall] with x hx
  exact Finset.sum_congr rfl (fun j _ => hx j)

def vectorGradientEnergy (v : Fin 3 → h1ZeroSpace) : ℝ :=
  ∑ j : Fin 3, ∑ i : Fin 3, ∫ x, ((v j).val.2 i x) ^ 2

theorem weakDivergenceLinear_energy (v : Fin 3 → h1ZeroSpace) :
    (∫ x, ((weakDivergenceLinear v).val x) ^ 2) ≤ 3 * vectorGradientEnergy v := by
  have himem : MemLp (fun x => ∑ j : Fin 3, (v j).val.2 j x) 2 volume :=
    memLp_finsetSum Finset.univ (fun j _ => (v j).property.1.2 j |>.1)
  have hiR : Integrable (fun x => 3 * ∑ j : Fin 3, ((v j).val.2 j x) ^ 2) :=
    (integrable_finsetSum Finset.univ (fun j _ => ((v j).property.1.2 j).1.integrable_sq)).const_mul 3
  calc
    _ = ∫ x, (∑ j : Fin 3, (v j).val.2 j x) ^ 2 := integral_congr_ae
      ((weakDivergenceLinear_ae v).mono (fun _ h => congrArg (fun z : ℝ => z ^ 2) h))
    _ ≤ ∫ x, 3 * ∑ j : Fin 3, ((v j).val.2 j x) ^ 2 :=
      integral_mono himem.integrable_sq hiR (fun x => by
        simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] using
          (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : Fin 3 => (v j).val.2 j x)))
    _ = 3 * ∑ j : Fin 3, ∫ x, ((v j).val.2 j x) ^ 2 := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => ((v j).property.1.2 j).1.integrable_sq)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
      change (∑ j : Fin 3, ∫ x, ((v j).val.2 j x) ^ 2) ≤
        ∑ j : Fin 3, ∑ i : Fin 3, ∫ x, ((v j).val.2 i x) ^ 2
      apply Finset.sum_le_sum
      intro j _
      exact Finset.single_le_sum (f := fun i : Fin 3 => ∫ x, ((v j).val.2 i x) ^ 2)
        (fun i _ => integral_nonneg (fun _ => sq_nonneg _))
        (Finset.mem_univ j)

end FreudenthalSVLean.BoundedWeakDivergence
