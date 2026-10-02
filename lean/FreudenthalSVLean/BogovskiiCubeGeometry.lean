import FreudenthalSVLean.WeakGradientMollification
import FreudenthalSVLean.ConformingVelocityFunction

/-!
# Actual support geometry for truncated cube Bogovskii integrals

For the continuous inverse in manuscript Lemma `means`, fix one genuine
normalized smooth bump in the central quarter-radius ball. Convex
coordinate bounds prove that a truncated Bogovskii kernel has support
strictly inside the open cube, uniformly over all pressure inputs.
The argument applies to every boundary face, edge and corner without a
boundary catalogue. These are support and normalization theorems only;
the L2 derivative estimate and divergence inversion are separate claims.
The integral geometry is the standard Bogovskii formula (cf. Durán,
arXiv:1103.3718, formula (1.3)), not a mesh-specific lifting identity.
-/

open scoped ContDiff
open MeasureTheory Set Metric
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ConformingVelocityFunction

noncomputable section

namespace FreudenthalSVLean.BogovskiiCubeGeometry

set_option backward.isDefEq.respectTransparency false

def center : Space := fun _ => 1 / 2

def bump : ContDiffBump center where
  rIn := 1 / 8
  rOut := 1 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def rho : Space → ℝ := bump.normed volume

theorem rho_contDiff : ContDiff ℝ ∞ rho := bump.contDiff_normed
theorem rho_compact : HasCompactSupport rho := bump.hasCompactSupport_normed
theorem rho_integral : (∫ x, rho x) = 1 := bump.integral_normed
theorem rho_nonneg (x : Space) : 0 ≤ rho x := bump.nonneg_normed x

def interiorBox (ε : ℝ) : Set Space :=
  Icc (fun _ => ε / 4) (fun _ => 1 - ε / 4)

theorem rho_tsupport_box : tsupport rho ⊆ interiorBox 1 := by
  intro x hx
  have hb : ‖x - center‖ ≤ 1 / 4 := by
    change x ∈ tsupport (bump.normed volume) at hx
    rw [bump.tsupport_normed_eq, mem_closedBall, dist_eq_norm_sub] at hx
    exact hx
  have hc (i : Fin 3) : |x i - 1 / 2| ≤ 1 / 4 :=
    (by simpa only [Real.norm_eq_abs, Pi.sub_apply, center] using
      norm_le_pi_norm (x - center) i : |x i - 1 / 2| ≤ ‖x - center‖).trans hb
  constructor
  · intro i
    have hi := (abs_le.mp (hc i)).1
    change 1 / 4 ≤ x i
    linarith
  · intro i
    have hi := (abs_le.mp (hc i)).2
    change x i ≤ 1 - 1 / 4
    linarith

theorem interiorBox_subset_openCube {ε : ℝ} (hε : 0 < ε) : interiorBox ε ⊆ openCube := by
  intro x hx
  apply (mem_openCube x).mpr
  intro i
  exact ⟨lt_of_lt_of_le (by positivity : 0 < ε / 4) (hx.1 i),
    lt_of_le_of_lt (hx.2 i) (by linarith : 1 - ε / 4 < 1)⟩

theorem rho_tsupport_interior : tsupport rho ⊆ openCube :=
  rho_tsupport_box.trans (interiorBox_subset_openCube (by norm_num))

def mix (t : ℝ) (z y : Space) : Space := t • z + (1 - t) • y

theorem mix_interior {ε t : ℝ} {y z : Space} (hε : 0 < ε) (ht : ε ≤ t)
    (ht1 : t ≤ 1) (hy : y ∈ cube) (hz : z ∈ interiorBox 1) : mix t z y ∈ interiorBox ε := by
  have ht0 : 0 ≤ t := (hε.le.trans ht)
  have h1t : 0 ≤ 1 - t := by linarith
  constructor
  · intro i
    change ε / 4 ≤ t * z i + (1 - t) * y i
    have hzi : 1 / 4 ≤ z i := hz.1 i
    have hyi : 0 ≤ y i := hy.1 i
    have hzmul := mul_le_mul_of_nonneg_left hzi ht0
    have hymul := mul_nonneg h1t hyi
    nlinarith
  · intro i
    change t * z i + (1 - t) * y i ≤ 1 - ε / 4
    have hzi : z i ≤ 1 - 1 / 4 := hz.2 i
    have hyi : y i ≤ 1 := hy.2 i
    have hzmul := mul_le_mul_of_nonneg_left hzi ht0
    have hymul := mul_le_mul_of_nonneg_left hyi h1t
    nlinarith

def kernelArgument (t : ℝ) (x y : Space) : Space := y + t⁻¹ • (x - y)

theorem mix_kernelArgument {t : ℝ} (ht : t ≠ 0) (x y : Space) :
    mix t (kernelArgument t x y) y = x := by
  funext i
  change t * (y i + t⁻¹ * (x i - y i)) + (1 - t) * y i = x i
  field_simp
  ring

theorem kernel_support {ε t : ℝ} {x y : Space} (hε : 0 < ε) (ht : ε ≤ t)
    (ht1 : t ≤ 1) (hy : y ∈ cube) (hr : rho (kernelArgument t x y) ≠ 0) :
    x ∈ interiorBox ε := by
  have hz := rho_tsupport_box (subset_tsupport rho hr)
  have hm := mix_interior hε ht ht1 hy hz
  rwa [mix_kernelArgument (ne_of_gt (hε.trans_le ht)) x y] at hm

theorem kernel_zero_outside {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) (ht1 : t ≤ 1)
    (f : Space → ℝ) (hf : ∀ y : Space, y ∉ cube → f y = 0)
    (x y : Space) (hx : x ∉ interiorBox ε) : rho (kernelArgument t x y) * f y = 0 := by
  by_cases hy : y ∈ cube
  · by_cases hr : rho (kernelArgument t x y) = 0
    · rw [hr, zero_mul]
    · exact False.elim (hx (kernel_support hε ht ht1 hy hr))
  · rw [hf y hy, mul_zero]

end FreudenthalSVLean.BogovskiiCubeGeometry
