import FreudenthalSVLean.WeakGradientL2Closed
import FreudenthalSVLean.H1ZeroL2Jet

/-!
# Closedness of the actual H1_0 smooth-closure criterion

For the continuous divergence step in manuscript Lemma `means`, strong
L2 convergence of actual values and all three actual weak derivatives
preserves H1_0 membership. Weak integration-by-parts identities pass to
the limit by the proved L2 closure theorem. A diagonal choice of actual
C-infinity interior-supported approximations and a genuine squared L2
triangle estimate supplies one smooth H1 approximation of the limit.
No assumed identification with a Sobolev completion is used.
-/

open scoped BigOperators ContDiff Topology
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakVelocityGradient
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.H1ApproximationL2
open FreudenthalSVLean.WeakGradientL2Closed

noncomputable section

namespace FreudenthalSVLean.H1ZeroL2Closed

set_option backward.isDefEq.respectTransparency false

def dataError (f : Space → ℝ) (g : Fin 3 → Space → ℝ)
    (F : Space → ℝ) (G : Fin 3 → Space → ℝ) : ℝ :=
  (∫ x, (f x - F x) ^ 2) + ∑ i : Fin 3, ∫ x, (g i x - G i x) ^ 2

theorem dataError_nonneg (f : Space → ℝ) (g : Fin 3 → Space → ℝ)
    (F : Space → ℝ) (G : Fin 3 → Space → ℝ) : 0 ≤ dataError f g F G :=
  add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

theorem dataError_value_le (f : Space → ℝ) (g : Fin 3 → Space → ℝ)
    (F : Space → ℝ) (G : Fin 3 → Space → ℝ) :
    (∫ x, (f x - F x) ^ 2) ≤ dataError f g F G :=
  le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

theorem dataError_gradient_le (f : Space → ℝ) (g : Fin 3 → Space → ℝ)
    (F : Space → ℝ) (G : Fin 3 → Space → ℝ) (i : Fin 3) :
    (∫ x, (g i x - G i x) ^ 2) ≤ dataError f g F G := by
  have hs : (∫ x, (g i x - G i x) ^ 2) ≤ ∑ j : Fin 3, ∫ x, (g j x - G j x) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 3 => ∫ x, (g j x - G j x) ^ 2)
      (fun j _ => integral_nonneg (fun _ => sq_nonneg _)) (Finset.mem_univ i)
  exact hs.trans (le_add_of_nonneg_left (integral_nonneg (fun _ => sq_nonneg _)))

theorem dataError_symm (f : Space → ℝ) (g : Fin 3 → Space → ℝ)
    (F : Space → ℝ) (G : Fin 3 → Space → ℝ) : dataError f g F G = dataError F G f g := by
  have hs (a b : Space → ℝ) : (∫ x, (a x - b x) ^ 2) = ∫ x, (b x - a x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  simp only [dataError, hs f F, hs (g _) (G _)]

theorem dataError_triangle {f F u : Space → ℝ} {g G v : Fin 3 → Space → ℝ}
    (hf : MemLp f 2 volume) (hF : MemLp F 2 volume) (hu : MemLp u 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume) (hG : ∀ i, MemLp (G i) 2 volume)
    (hv : ∀ i, MemLp (v i) 2 volume) :
    dataError f g F G ≤ 2 * (dataError f g u v + dataError F G u v) := by
  have hvalue := integral_square_sub_triangle hf hF hu
  have hgrad := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => integral_square_sub_triangle (hg i) (hG i) (hv i))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hgrad
  unfold dataError
  linarith

theorem dataError_value_L2_tendsto {u : ℕ → Space → ℝ} {v : ℕ → Fin 3 → Space → ℝ}
    {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hu : ∀ n, MemLp (u n) 2 volume) (hf : MemLp f 2 volume)
    (ht : Tendsto (fun n => dataError (u n) (v n) f g) atTop (𝓝 0)) :
    Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hf.toLp f)) :=
  toLp_tendsto_of_square_error hu hf
    (squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      (fun n => dataError_value_le (u n) (v n) f g) ht)

theorem dataError_gradient_L2_tendsto {u : ℕ → Space → ℝ} {v : ℕ → Fin 3 → Space → ℝ}
    {f : Space → ℝ} {g : Fin 3 → Space → ℝ} (i : Fin 3)
    (hv : ∀ n, MemLp (v n i) 2 volume) (hg : MemLp (g i) 2 volume)
    (ht : Tendsto (fun n => dataError (u n) (v n) f g) atTop (𝓝 0)) :
    Tendsto (fun n => (hv n).toLp (v n i)) atTop (𝓝 (hg.toLp (g i))) :=
  toLp_tendsto_of_square_error hv hg
    (squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      (fun n => dataError_gradient_le (u n) (v n) f g i) ht)

theorem hasL2WeakGradient_dataError_closed {u : ℕ → Space → ℝ}
    {v : ℕ → Fin 3 → Space → ℝ} {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hw : ∀ n, HasL2WeakGradient (u n) (v n)) (hf : MemLp f 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume)
    (ht : Tendsto (fun n => dataError (u n) (v n) f g) atTop (𝓝 0)) : HasL2WeakGradient f g :=
  hasL2WeakGradient_L2_closed hw hf hg
    (dataError_value_L2_tendsto (fun n => (hw n).1) hf ht)
    (fun i => dataError_gradient_L2_tendsto i (fun n => ((hw n).2 i).1) (hg i) ht)

theorem inH1ZeroCube_dataError_closed {u : ℕ → Space → ℝ}
    {v : ℕ → Fin 3 → Space → ℝ} {f : Space → ℝ} {g : Fin 3 → Space → ℝ}
    (hw : ∀ n, InH1ZeroCube (u n) (v n)) (hf : MemLp f 2 volume)
    (hg : ∀ i, MemLp (g i) 2 volume)
    (ht : Tendsto (fun n => dataError (u n) (v n) f g) atTop (𝓝 0)) : InH1ZeroCube f g := by
  have hweak := hasL2WeakGradient_dataError_closed (fun n => (hw n).1) hf hg ht
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have htδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hchoose (n : ℕ) : ∃ w : Space → ℝ,
      (ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧ tsupport w ⊆ ConformingVelocityFunction.openCube ∧
        MemLp w 2 volume ∧ ∀ i : Fin 3, MemLp (fun x => fderiv ℝ w x (Pi.single i 1)) 2 volume) ∧
      dataError w (fun i x => fderiv ℝ w x (Pi.single i 1)) (u n) (v n) < δ n := by
    obtain ⟨_, a, ha, hc⟩ := hw n
    obtain ⟨m, hm⟩ := (hc.eventually (gt_mem_nhds (hδ n))).exists
    exact ⟨a m, ha m, hm⟩
  choose w hwprops hwerr using hchoose
  have hb (n : ℕ) : dataError (w n) (fun i x => fderiv ℝ (w n) x (Pi.single i 1)) f g ≤
      2 * (δ n + dataError (u n) (v n) f g) := by
    have hd := dataError_triangle (hwprops n).2.2.2.1 hf (hw n).1.1
      (hwprops n).2.2.2.2 hg (fun i => ((hw n).1.2 i).1)
    rw [dataError_symm f g (u n) (v n)] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (add_le_add (hwerr n).le le_rfl) (by norm_num))
  have hl : Tendsto (fun n => dataError (w n)
      (fun i x => fderiv ℝ (w n) x (Pi.single i 1)) f g) atTop (𝓝 0) :=
    squeeze_zero (fun n => dataError_nonneg _ _ _ _) hb
      (by simpa only [zero_add, mul_zero] using (htδ.add ht).const_mul 2)
  exact ⟨hweak, w, hwprops, hl⟩

end FreudenthalSVLean.H1ZeroL2Closed
