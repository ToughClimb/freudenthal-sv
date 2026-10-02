import FreudenthalSVLean.CubePressureHilbert
import FreudenthalSVLean.H1JetRepresentative
import FreudenthalSVLean.BoundedWeakDivergence

/-!
# Genuine bounded divergence between complete cube Hilbert spaces

For manuscript Lemma `means`, the operator is the actual weak divergence
from three genuine H1_0 jets to mean-zero cube L2 classes. Fixed linear
actual representatives preserve the exact full H1 norm. Their divergence
agrees almost everywhere with the operator and its squared L2 norm is at
most three times the genuine gradient energy, hence the squared Hilbert
norm. Surjectivity is a separate analytic assertion, not a consequence
of this boundedness proof.
-/

open scoped BigOperators
open MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.H1ZeroLinearity
open FreudenthalSVLean.H1ZeroL2Jet
open FreudenthalSVLean.H1ZeroHilbertSpace
open FreudenthalSVLean.H1JetRepresentative
open FreudenthalSVLean.CubePressureHilbert
open FreudenthalSVLean.BoundedWeakDivergence

noncomputable section

namespace FreudenthalSVLean.HilbertCubeDivergence

set_option backward.isDefEq.respectTransparency false

abbrev VectorHilbert := PiLp 2 (fun _ : Fin 3 => jetSpace)

def vectorRepresentative : VectorHilbert →ₗ[ℝ] (Fin 3 → h1ZeroSpace) :=
  LinearMap.pi (fun j => representative.comp (PiLp.projₗ 2 (fun _ : Fin 3 => jetSpace) j))

theorem vectorRepresentative_apply (W : VectorHilbert) (j : Fin 3) :
    vectorRepresentative W j = representative (W j) := rfl

theorem vectorRepresentative_gradient_bound (W : VectorHilbert) :
    vectorGradientEnergy (vectorRepresentative W) ≤ ‖W‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum (fun j _ => representative_gradient_bound (W j))

theorem vectorRepresentative_full_energy (W : VectorHilbert) :
    (∑ j : Fin 3, ((∫ x, ((vectorRepresentative W j).val.1 x) ^ 2) +
      ∑ i : Fin 3, ∫ x, ((vectorRepresentative W j).val.2 i x) ^ 2)) = ‖W‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl (fun j _ => representative_energy (W j))

def divergenceLinear : VectorHilbert →ₗ[ℝ] pressureHilbert :=
  pressureClass.comp (weakDivergenceLinear.comp vectorRepresentative)

theorem divergenceLinear_energy (W : VectorHilbert) :
    ‖divergenceLinear W‖ ^ 2 ≤ 3 * ‖W‖ ^ 2 := by
  change ‖pressureClass (weakDivergenceLinear (vectorRepresentative W))‖ ^ 2 ≤ _
  rw [pressureClass_norm_square]
  exact (weakDivergenceLinear_energy _).trans
    (mul_le_mul_of_nonneg_left (vectorRepresentative_gradient_bound W) (by norm_num))

theorem divergenceLinear_norm_bound (W : VectorHilbert) :
    ‖divergenceLinear W‖ ≤ 3 * ‖W‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * ‖W‖)).mp
  have h := divergenceLinear_energy W
  nlinarith [sq_nonneg ‖W‖]

def divergenceHilbert : VectorHilbert →L[ℝ] pressureHilbert :=
  divergenceLinear.mkContinuous 3 divergenceLinear_norm_bound

theorem divergenceHilbert_ae (W : VectorHilbert) :
    ((divergenceHilbert W).val : Space → ℝ) =ᵐ[volume]
      (fun x => ∑ j : Fin 3, (vectorRepresentative W j).val.2 j x) :=
  (MemLp.coeFn_toLp (weakDivergenceLinear (vectorRepresentative W)).property.1).trans
    (weakDivergenceLinear_ae _)

end FreudenthalSVLean.HilbertCubeDivergence
