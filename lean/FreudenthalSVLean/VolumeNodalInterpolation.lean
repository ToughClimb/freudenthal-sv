import FreudenthalSVLean.LinearNodalInterpolation
import FreudenthalSVLean.BoundaryHalfBoxGeometry
import FreudenthalSVLean.WeakLinearFaceTrace

/-!
# A fixed linear volume-averaging finite-element interpolant

For the interpolation stage in manuscript Lemma `means` and equation
`SZ`, each actual grid vertex is assigned the genuine volume average
over its symmetric radius-h box.  The fixed homogeneous nodal map sets
boundary coefficients to zero and assembles the actual P1 velocity.
All averages are proved linear on the actual smooth-approximable weak
H1 space, with no input-dependent geometry.  The output has actual
all-point conformity, zero physical boundary values and degree one.
Local interpolation errors and uniform global H1 stability are separate
obligations; neither is inferred merely from this construction.
-/

open scoped BigOperators Topology Classical
open MvPolynomial MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.TranslatedBoxH1Estimate
open FreudenthalSVLean.LinearNodalInterpolation

noncomputable section

namespace FreudenthalSVLean.VolumeNodalInterpolation

set_option backward.isDefEq.respectTransparency false

theorem smoothH1Space_value_memLp (v : smoothH1Space) : MemLp v.val.1 2 volume := by
  obtain ⟨u, hu⟩ := v.property
  exact hu.weak_gradient.1

theorem smoothH1Space_value_integrable_box (v : smoothH1Space) (a b : ℝ) (o : Space) :
    IntegrableOn v.val.1 (translatedBox a b o) := by
  let : IsFiniteMeasure (volume.restrict (translatedBox a b o)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc : IsCompact (translatedBox a b o)).measure_ne_top
  exact ((smoothH1Space_value_memLp v).restrict (translatedBox a b o)).integrable (by norm_num)

def volumeMeanLinear (a b : ℝ) (o : Space) : smoothH1Space →ₗ[ℝ] ℝ where
  toFun v := translatedBoxMean a b o v.val.1
  map_add' v w := by
    change ((b - a)⁻¹) ^ 3 * (∫ x in translatedBox a b o, v.val.1 x + w.val.1 x) =
      ((b - a)⁻¹) ^ 3 * (∫ x in translatedBox a b o, v.val.1 x) +
        ((b - a)⁻¹) ^ 3 * ∫ x in translatedBox a b o, w.val.1 x
    rw [integral_add (smoothH1Space_value_integrable_box v a b o)
      (smoothH1Space_value_integrable_box w a b o), mul_add]
  map_smul' c v := by
    change ((b - a)⁻¹) ^ 3 * (∫ x in translatedBox a b o, c * v.val.1 x) =
      c * (((b - a)⁻¹) ^ 3 * ∫ x in translatedBox a b o, v.val.1 x)
    rw [integral_const_mul]
    ring

def nodalAverages (N : ℕ) : (Fin 3 → smoothH1Space) →ₗ[ℝ] (GridVertex N → Space) where
  toFun v n j := volumeMeanLinear (-(meshScale N)) (meshScale N) (gridPoint n) (v j)
  map_add' v w := by
    funext n j
    exact (volumeMeanLinear (-(meshScale N)) (meshScale N) (gridPoint n)).map_add (v j) (w j)
  map_smul' c v := by
    funext n j
    exact (volumeMeanLinear (-(meshScale N)) (meshScale N) (gridPoint n)).map_smul c (v j)

/-- Geometry and averaging functionals are fixed before the input vector field. -/
def volumeNodalInterpolation {N : ℕ} (hN : 0 < N) :
    (Fin 3 → smoothH1Space) →ₗ[ℝ] velocitySpace N 1 :=
  (homogeneousNodalInterpolation hN).comp (nodalAverages N)

theorem volumeNodalInterpolation_on_element {N : ℕ} (hN : 0 < N)
    (v : Fin 3 → smoothH1Space) (t : Tet N) (j : Fin 3) :
    (volumeNodalInterpolation hN v).val t j = ∑ a : Fin 4,
      C (if interiorNode (gridVertexOfTet t a) then
        translatedBoxMean (-(meshScale N)) (meshScale N)
          (gridPoint (gridVertexOfTet t a)) (v j).val.1 else 0) *
            FreudenthalMesh.barycentric t a := by
  change nodalInterpolation (nodalAverages N v) t j = _
  rw [nodalInterpolation_on_element]
  rfl

end FreudenthalSVLean.VolumeNodalInterpolation
