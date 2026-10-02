import FreudenthalSVLean.H1ApproximationL2
import FreudenthalSVLean.WeakGradientLinearity

/-!
# Closedness of genuine weak derivatives under strong L2 convergence

For the continuous divergence step in manuscript Lemma `means`, actual
weak derivative identities are preserved by strong convergence in the
true L2 spaces. Genuine test-product integrals are Hilbert inner
products; their continuity passes every actual smooth compactly
supported integration-by-parts identity to the limit. This is a proved
weak-derivative closure theorem, not an assumed Sobolev completion rule.
-/

open scoped Topology
open MeasureTheory Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.WeakVelocityGradient
open FreudenthalSVLean.WeakGradientLinearity
open FreudenthalSVLean.H1ApproximationL2

noncomputable section

namespace FreudenthalSVLean.WeakGradientL2Closed

set_option backward.isDefEq.respectTransparency false

theorem real_inner_toLp_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, RCLike.conj_to_real]
  ring

theorem integral_product_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : ℕ → α → ℝ} {f φ : α → ℝ}
    (hu : ∀ n, MemLp (u n) 2 μ) (hf : MemLp f 2 μ) (hφ : MemLp φ 2 μ)
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun n => ∫ x, u n x * φ x ∂μ) atTop (𝓝 (∫ x, f x * φ x ∂μ)) := by
  have hi := ht.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hφ.toLp φ))
  simpa only [real_inner_toLp_eq_integral] using hi

theorem hasWeakPartial_L2_closed {u v : ℕ → Space → ℝ} {f g : Space → ℝ} {i : Fin 3}
    (hu : ∀ n, MemLp (u n) 2 volume) (hv : ∀ n, MemLp (v n) 2 volume)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hw : ∀ n, HasWeakPartial (u n) (v n) i)
    (htu : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hf.toLp f)))
    (htv : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hg.toLp g))) :
    HasWeakPartial f g i := by
  intro φ hφ hc
  have hmφ : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hmd := test_partial_memLp hφ hc i
  have hgφ := integral_product_tendsto hv hg hmφ htv
  have hfd := integral_product_tendsto hu hf hmd htu
  exact tendsto_nhds_unique hgφ (hfd.neg.congr' (Eventually.of_forall
    (fun n => (hw n φ hφ hc).symm)))

theorem hasL2WeakGradient_L2_closed {u : ℕ → Space → ℝ}
    {v : ℕ → Fin 3 → Space → ℝ} {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hw : ∀ n, HasL2WeakGradient (u n) (v n)) (hf : MemLp f 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume)
    (htu : Tendsto (fun n => (hw n).1.toLp (u n)) atTop (𝓝 (hf.toLp f)))
    (htv : ∀ i, Tendsto (fun n => ((hw n).2 i).1.toLp (v n i)) atTop (𝓝 ((hg i).toLp (g i)))) :
    HasL2WeakGradient f g := by
  refine ⟨hf, fun i => ⟨hg i, ?_⟩⟩
  exact hasWeakPartial_L2_closed (fun n => (hw n).1) (fun n => ((hw n).2 i).1)
    hf (hg i) (fun n => ((hw n).2 i).2) htu (htv i)

end FreudenthalSVLean.WeakGradientL2Closed
