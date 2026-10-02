import FreudenthalSVLean.FaceL2MeanEstimate
import FreudenthalSVLean.StableFaceTransfer
import FreudenthalSVLean.FaceFluxNormalization

/-!
# Actual cubic correction of a weak face flux

For manuscript Lemma `means`, a true weak-H1 face flux is lifted by a
fixed linear cubic two-owner field.  Its divergence means are exactly
plus and minus the prescribed flux, every other element mean is zero,
and all nonowner polynomials vanish.  Actual mesh conformity and zero
physical boundary values follow from the established global nodal field.
Its energy is bounded, with one constant before the mesh and face, by
6 h^{-2} times the residual value energy plus the residual gradient energy.
This is the local face-correction estimate used after stable interpolation;
neither that interpolant nor a continuous divergence inverse is assumed
to exist here.
-/

open scoped BigOperators
open MeasureTheory MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.StableFaceTransfer
open FreudenthalSVLean.VelocityEnergy
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.FaceL2MeanEstimate

noncomputable section

namespace FreudenthalSVLean.WeakFaceFluxCorrection

set_option backward.isDefEq.respectTransparency false

def faceCorrection {N : ℕ} (t : Tet N) (r : Fin 4) (δ : ℝ) : BrokenVelocity N :=
  δ • transferField N t r

def correctionLinear {N : ℕ} (t : Tet N) (r : Fin 4) : ℝ →ₗ[ℝ] BrokenVelocity N :=
  LinearMap.toSpanSingleton ℝ (BrokenVelocity N) (transferField N t r)

theorem correctionLinear_apply {N : ℕ} (t : Tet N) (r : Fin 4) (δ : ℝ) :
    correctionLinear t r δ = faceCorrection t r δ := rfl

theorem faceCorrection_mem {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r s : Fin 4) (hr : r ≠ ta.val.2) (hs : s ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 s) (δ : ℝ) :
    faceCorrection ta.val.1 r δ ∈ velocitySpace N 3 :=
  (velocitySpace N 3).smul_mem δ (transfer_mem_velocitySpace hN ta tb r s hr hs hne he)

theorem faceCorrection_mean_scale {N : ℕ} (t v : Tet N) (r : Fin 4) (δ : ℝ) :
    (∫ x in tetrahedron v, eval x (divergence N (faceCorrection t r δ) v)) =
      δ * ∫ x in tetrahedron v, eval x (divergence N (transferField N t r) v) := by
  rw [faceCorrection, map_smul]
  simp only [Pi.smul_apply, smul_eq_C_mul, map_mul, eval_C, integral_const_mul]

theorem faceCorrection_means {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r s : Fin 4) (hr : r ≠ ta.val.2) (hs : s ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 s)
    (δ : ℝ) (v : Tet N) :
    (∫ x in tetrahedron v, eval x (divergence N (faceCorrection ta.val.1 r δ) v)) =
      if v = ta.val.1 then δ else if v = tb.val.1 then -δ else 0 := by
  rw [faceCorrection_mean_scale]
  by_cases hta : v = ta.val.1
  · subst v
    simp only [if_true, transfer_mean_one hN, mul_one]
  · by_cases htb : v = tb.val.1
    · subst v
      simp only [if_neg hta, if_true, transfer_mean_minus_one hN ta tb r s hr hs hne he,
        mul_neg, mul_one]
    · simp only [if_neg hta, if_neg htb,
        transfer_mean_off_pair ta tb r s hr hne he v hta htb, mul_zero]

theorem faceCorrection_zero_off_pair {N : ℕ} {n : GridVertex N}
    (ta tb : VertexStar n) (r s : Fin 4) (hr : r ≠ ta.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 s)
    (δ : ℝ) (v : Tet N) (hta : v ≠ ta.val.1) (htb : v ≠ tb.val.1) :
    faceCorrection ta.val.1 r δ v = 0 := by
  funext j
  simp only [faceCorrection, Pi.smul_apply,
    transfer_zero_off_pair ta tb r s hr hne he v hta htb j, smul_zero, Pi.zero_apply]

def correctionConstant : ℝ := 2 * referenceBound

theorem correctionConstant_pos : 0 < correctionConstant :=
  mul_pos (by norm_num) referenceBound_pos

theorem faceCorrection_energy_bound {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r s : Fin 4) (hr : r ≠ ta.val.2) (hs : s ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 s) (δ : ℝ) :
    velocityEnergy (faceCorrection ta.val.1 r δ) ≤
      correctionConstant * ((meshScale N) ^ 3)⁻¹ * δ ^ 2 := by
  have hscale := meshScale_pos N hN
  rw [faceCorrection, velocityEnergy_smul, transfer_global_energy hN ta tb r s hr hs hne he]
  have hb : referenceEnergy r + referenceEnergy s ≤ correctionConstant := by
    unfold correctionConstant
    linarith [referenceEnergy_le_bound r, referenceEnergy_le_bound s]
  calc
    _ = (((meshScale N) ^ 3)⁻¹ * δ ^ 2) * (referenceEnergy r + referenceEnergy s) := by ring
    _ ≤ (((meshScale N) ^ 3)⁻¹ * δ ^ 2) * correctionConstant :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- One fixed constant works before all actual mesh, face and weak-field
parameters.  The h^{-2} residual term is explicit: an h-order interpolant
error, not a global Poincare estimate, is needed to obtain uniform stability. -/
theorem weak_faceCorrection_energy {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r s : Fin 4) (hr : r ≠ ta.val.2) (hs : s ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 s)
    (f : Fin 3 → Space → ℝ) (g : Fin 3 → Fin 3 → Space → ℝ)
    (hf : ∀ j, ∃ u, SmoothH1Approximation (f j) (g j) u)
    (T : Fin 3 → FaceL2)
    (hT : ∀ j, HasH1FaceTrace (f j) (g j) ta.val.1.2 (cellOrigin ta.val.1.1)
      (meshScale N) r (T j)) :
    velocityEnergy (faceCorrection ta.val.1 r (traceFlux ta.val.1.2 (meshScale N) r T)) ≤
      correctionConstant *
        (6 * ((meshScale N) ^ 2)⁻¹ * (∑ j : Fin 3, ∫ x in tetrahedron ta.val.1, (f j x) ^ 2) +
          ∑ j : Fin 3, ∑ i : Fin 3, ∫ x in tetrahedron ta.val.1, (g j i x) ^ 2) := by
  have ht := weak_traceFlux_scale_bound f g hf ta.val.1.2 (cellOrigin ta.val.1.1)
    (meshScale N) (meshScale_pos N hN) r T hT
  have he' := faceCorrection_energy_bound hN ta tb r s hr hs hne he
    (traceFlux ta.val.1.2 (meshScale N) r T)
  rw [mul_assoc] at he'
  exact he'.trans (mul_le_mul_of_nonneg_left ht correctionConstant_pos.le)

end FreudenthalSVLean.WeakFaceFluxCorrection
