import FreudenthalSVLean.ConformingDivergenceMean

/-!
# Actual zero-extended mean-zero L2 functions on the cube

For the continuous input in manuscript Lemma `means`, the domain is a
proved real vector space of actual L2 functions supported in the closed
cube and with genuine zero Lebesgue mean. Finite cube volume proves
their actual L1 integrability. The exact finite-element pressure image
embeds by a fixed linear map on every positive N, with exactly the
physical pressure energy as its squared L2 integral. No divergence
solvability or continuous right-inverse estimate is assumed here.
-/

open scoped BigOperators
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.GlobalPolynomialL2
open FreudenthalSVLean.ConformingDivergenceMean

noncomputable section

namespace FreudenthalSVLean.CubeZeroMeanL2

set_option backward.isDefEq.respectTransparency false

theorem supported_memLp_integrable {f : Space → ℝ} (hf : MemLp f 2 volume)
    (hs : ∀ x : Space, x ∉ cube → f x = 0) : Integrable f := by
  let : IsFiniteMeasure ((volume : Measure Space).restrict cube) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_Icc : IsCompact cube).measure_lt_top⟩
  have hsupport : Function.support f ⊆ cube := by
    intro x hx
    by_contra hn
    exact hx (hs x hn)
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  exact (hf.mono_measure Measure.restrict_le_self).integrable (by norm_num)

/-- Actual representatives, with genuine Lebesgue L2 and zero-mean conditions. -/
def cubePressureFunctions : Submodule ℝ (Space → ℝ) where
  carrier := {f | MemLp f 2 volume ∧ (∀ x : Space, x ∉ cube → f x = 0) ∧ (∫ x, f x) = 0}
  zero_mem' := ⟨MemLp.zero', fun _ _ => rfl, integral_zero _ _⟩
  add_mem' := by
    rintro f g ⟨hf, hfs, hfm⟩ ⟨hg, hgs, hgm⟩
    refine ⟨hf.add hg, ?_, ?_⟩
    · intro x hx
      simp only [Pi.add_apply, hfs x hx, hgs x hx, zero_add]
    · change (∫ x, f x + g x) = 0
      rw [integral_add (supported_memLp_integrable hf hfs) (supported_memLp_integrable hg hgs)]
      rw [hfm, hgm, zero_add]
  smul_mem' := by
    rintro c f ⟨hf, hfs, hfm⟩
    refine ⟨hf.const_smul c, ?_, ?_⟩
    · intro x hx
      simp only [Pi.smul_apply, hfs x hx, smul_zero]
    · change (∫ x, c * f x) = 0
      rw [integral_const_mul, hfm, mul_zero]

theorem cubePressureFunctions_integrable (q : cubePressureFunctions) : Integrable q.val :=
  supported_memLp_integrable q.property.1 q.property.2.1

def pressureEmbedding {N k : ℕ} (hN : 0 < N) :
    pressureSpace N k →ₗ[ℝ] cubePressureFunctions :=
  ((piecewisePressureLinear N).comp (pressureSpace N k).subtype).codRestrict _ (fun q =>
    ⟨piecewisePressure_memLp hN q.val, piecewisePressure_zero_off_cube hN q.val,
      pressureSpace_integral_zero hN q⟩)

theorem pressureEmbedding_val {N k : ℕ} (hN : 0 < N) (q : pressureSpace N k) :
    (pressureEmbedding hN q).val = piecewisePressure q.val := rfl

theorem pressureEmbedding_energy {N k : ℕ} (hN : 0 < N) (q : pressureSpace N k) :
    (∫ x, ((pressureEmbedding hN q).val x) ^ 2) = pressureEnergy q.val :=
  piecewisePressure_square_integral hN q.val

theorem piecewisePressure_integral_on_element {N : ℕ} (hN : 0 < N) (q : BrokenPressure N)
    (t : Tet N) : (∫ x in tetrahedron t, piecewisePressure q x) =
      StarMeanRouting.tetIntegral hN t (q t) := by
  apply integral_congr_ae
  have hu := ae_unique_owner hN
  filter_upwards [ae_restrict_of_ae hu,
    ae_restrict_mem (tetrahedron_isCompact hN t).measurableSet] with x hx ht
  exact piecewisePressure_on_unique q t x ht (fun u hxu => (hx t u ht hxu).symm)

end FreudenthalSVLean.CubeZeroMeanL2
