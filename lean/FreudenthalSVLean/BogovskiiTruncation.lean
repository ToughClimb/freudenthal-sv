import FreudenthalSVLean.BogovskiiCubeGeometry

/-!
# Actual truncated Bogovskii fields and their interior support

For manuscript Lemma `means`, the truncated velocity is a genuine
iterated Lebesgue integral of the standard Bogovskii kernel. The proved
convex support geometry gives true pointwise zero values outside one
compact box strictly inside the cube, before the pressure input.
A pointwise algebraic decomposition identifies the two scalar kernel
terms needed for the subsequent Fourier derivative estimate. This
module does not yet assert differentiability, inversion or L2 stability.
-/

open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.BogovskiiCubeGeometry

noncomputable section

namespace FreudenthalSVLean.BogovskiiTruncation

set_option backward.isDefEq.respectTransparency false

def kernel (t : ℝ) (x y : Space) (j : Fin 3) : ℝ :=
  (x j - y j) / t ^ 4 * rho (kernelArgument t x y)

def truncated (ε : ℝ) (f : Space → ℝ) (j : Fin 3) (x : Space) : ℝ :=
  ∫ t in Icc ε 1, ∫ y : Space, kernel t x y j * f y

theorem kernel_split {t : ℝ} (ht : t ≠ 0) (x y : Space) (j : Fin 3) :
    kernel t x y j = ((kernelArgument t x y) j * rho (kernelArgument t x y) -
      y j * rho (kernelArgument t x y)) / t ^ 3 := by
  unfold kernel kernelArgument
  change (x j - y j) / t ^ 4 * rho (y + t⁻¹ • (x - y)) =
    ((y j + t⁻¹ * (x j - y j)) * rho (y + t⁻¹ • (x - y)) -
      y j * rho (y + t⁻¹ • (x - y))) / t ^ 3
  field_simp
  ring

theorem kernel_input_zero_outside {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc ε 1)
    (f : Space → ℝ) (hf : ∀ y : Space, y ∉ FreudenthalMesh.cube → f y = 0)
    (j : Fin 3) (x y : Space) (hx : x ∉ interiorBox ε) : kernel t x y j * f y = 0 := by
  have he := kernel_zero_outside hε ht.1 ht.2 f hf x y hx
  unfold kernel
  rw [mul_assoc, he, mul_zero]

theorem truncated_zero_outside {ε : ℝ} (hε : 0 < ε) (f : Space → ℝ)
    (hf : ∀ y : Space, y ∉ FreudenthalMesh.cube → f y = 0)
    (j : Fin 3) (x : Space) (hx : x ∉ interiorBox ε) : truncated ε f j x = 0 := by
  unfold truncated
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (Icc ε (1 : ℝ)))] with t ht
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall (fun y => kernel_input_zero_outside hε ht f hf j x y hx)

theorem truncated_support_box {ε : ℝ} (hε : 0 < ε) (f : Space → ℝ)
    (hf : ∀ y : Space, y ∉ FreudenthalMesh.cube → f y = 0) (j : Fin 3) :
    Function.support (truncated ε f j) ⊆ interiorBox ε := by
  intro x hx
  by_contra hn
  exact hx (truncated_zero_outside hε f hf j x hn)

theorem truncated_hasCompactSupport {ε : ℝ} (hε : 0 < ε) (f : Space → ℝ)
    (hf : ∀ y : Space, y ∉ FreudenthalMesh.cube → f y = 0) (j : Fin 3) :
    HasCompactSupport (truncated ε f j) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (interiorBox ε))
    (truncated_support_box hε f hf j)

theorem truncated_tsupport_interior {ε : ℝ} (hε : 0 < ε) (f : Space → ℝ)
    (hf : ∀ y : Space, y ∉ FreudenthalMesh.cube → f y = 0) (j : Fin 3) :
    tsupport (truncated ε f j) ⊆ openCube :=
  (closure_minimal (truncated_support_box hε f hf j) (isClosed_Icc : IsClosed (interiorBox ε))).trans
    (interiorBox_subset_openCube hε)

end FreudenthalSVLean.BogovskiiTruncation
