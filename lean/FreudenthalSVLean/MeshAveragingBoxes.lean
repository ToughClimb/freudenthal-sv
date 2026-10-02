import FreudenthalSVLean.LocalAverageEstimates
import FreudenthalSVLean.MeshSegments

/-!
# Actual mesh-neighborhood geometry for volume interpolation

For the interpolation estimates in manuscript Lemma `means` and equation
`SZ`, each tetrahedron is contained in every radius-h box around one of
its four vertices.  Those four averaging boxes are all contained in a
radius-2h box centered at any chosen vertex of the tetrahedron.  These
statements follow from actual scaled coordinate bounds for every N>0.
A noninterior grid vertex has an actual zero or one coordinate, so the
proved boundary-centered box estimate applies without boundary-state
enumeration.  The genuine averages have scale-correct bounds in this
common neighborhood; the full interpolation and overlap estimates are
not assumed.
-/

open scoped BigOperators Topology Classical
open MeasureTheory Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.MeshSegments
open FreudenthalSVLean.ConformingH1Zero
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.TranslatedBoxH1Estimate
open FreudenthalSVLean.BoundaryHalfBoxGeometry
open FreudenthalSVLean.LocalAverageEstimates
open FreudenthalSVLean.LinearNodalInterpolation

noncomputable section

namespace FreudenthalSVLean.MeshAveragingBoxes

set_option backward.isDefEq.respectTransparency false

def nodeBox {N : ℕ} (n : GridVertex N) : Set Space :=
  translatedBox (-(meshScale N)) (meshScale N) (gridPoint n)

def elementBox {N : ℕ} (t : Tet N) (a : Fin 4) : Set Space :=
  translatedBox (-2 * meshScale N) (2 * meshScale N) (gridPoint (gridVertexOfTet t a))

theorem tetrahedron_coordinate_bounds {N : ℕ} (hN : 0 < N) (t : Tet N)
    {x : Space} (hx : x ∈ tetrahedron t) (j : Fin 3) :
    meshScale N * cellOrigin t.1 j ≤ x j ∧
      x j ≤ meshScale N * cellOrigin t.1 j + meshScale N := by
  have hh := meshScale_pos N hN
  have hb := unitChainSet_coordinate_bounds t.2 (cellOrigin t.1)
    ((meshScale N)⁻¹ • x) hx j
  have hl := mul_nonneg hh.le hb.1
  have hu := mul_le_mul_of_nonneg_left hb.2 hh.le
  simp only [Pi.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc,
    mul_inv_cancel₀ hh.ne', one_mul, mul_one] at hl hu
  constructor <;> linarith

theorem vertex_coordinate_bounds {N : ℕ} (hN : 0 < N) (t : Tet N)
    (a : Fin 4) (j : Fin 3) :
    meshScale N * cellOrigin t.1 j ≤ gridPoint (gridVertexOfTet t a) j ∧
      gridPoint (gridVertexOfTet t a) j ≤ meshScale N * cellOrigin t.1 j + meshScale N := by
  rw [gridVertexOfTet_point]
  exact tetrahedron_coordinate_bounds hN t (vertex_mem_tetrahedron hN t a) j

theorem tetrahedron_subset_nodeBox {N : ℕ} (hN : 0 < N) (t : Tet N) (a : Fin 4) :
    tetrahedron t ⊆ nodeBox (gridVertexOfTet t a) := by
  intro x hx
  constructor
  · intro j
    have hb := tetrahedron_coordinate_bounds hN t hx j
    have hv := vertex_coordinate_bounds hN t a j
    change -meshScale N + gridPoint (gridVertexOfTet t a) j ≤ x j
    linarith
  · intro j
    have hb := tetrahedron_coordinate_bounds hN t hx j
    have hv := vertex_coordinate_bounds hN t a j
    change x j ≤ meshScale N + gridPoint (gridVertexOfTet t a) j
    linarith

theorem nodeBox_subset_elementBox {N : ℕ} (hN : 0 < N) (t : Tet N)
    (a b : Fin 4) : nodeBox (gridVertexOfTet t b) ⊆ elementBox t a := by
  intro x hx
  constructor
  · intro j
    have hv := vertex_coordinate_bounds hN t a j
    have hw := vertex_coordinate_bounds hN t b j
    have hl := hx.1 j
    change -meshScale N + gridPoint (gridVertexOfTet t b) j ≤ x j at hl
    change -2 * meshScale N + gridPoint (gridVertexOfTet t a) j ≤ x j
    linarith
  · intro j
    have hv := vertex_coordinate_bounds hN t a j
    have hw := vertex_coordinate_bounds hN t b j
    have hu := hx.2 j
    change x j ≤ meshScale N + gridPoint (gridVertexOfTet t b) j at hu
    change x j ≤ 2 * meshScale N + gridPoint (gridVertexOfTet t a) j
    linarith

theorem tetrahedron_subset_elementBox {N : ℕ} (hN : 0 < N) (t : Tet N) (a : Fin 4) :
    tetrahedron t ⊆ elementBox t a :=
  (tetrahedron_subset_nodeBox hN t a).trans (nodeBox_subset_elementBox hN t a a)

theorem not_interiorNode_boundary {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (hn : ¬ interiorNode n) : ∃ j : Fin 3, gridPoint n j = 0 ∨ gridPoint n j = 1 := by
  obtain ⟨j, hj⟩ := not_forall.mp hn
  have hbound := (n j).isLt
  have hval : (n j).val = 0 ∨ (n j).val = N := by
    change ¬ (0 < (n j).val ∧ (n j).val < N) at hj
    omega
  refine ⟨j, ?_⟩
  rcases hval with hzero | hupp
  · left
    simp only [gridPoint, Pi.smul_apply, smul_eq_mul, hzero, Nat.cast_zero, mul_zero]
  · right
    simp only [gridPoint, Pi.smul_apply, smul_eq_mul, hupp, meshScale]
    exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')

def nodeMean {N : ℕ} (f : Space → ℝ) (n : GridVertex N) : ℝ :=
  translatedBoxMean (-(meshScale N)) (meshScale N) (gridPoint n) f

def elementMean {N : ℕ} (f : Space → ℝ) (t : Tet N) (a : Fin 4) : ℝ :=
  translatedBoxMean (-2 * meshScale N) (2 * meshScale N) (gridPoint (gridVertexOfTet t a)) f

theorem nodeMean_difference_bound {N : ℕ} (hN : 0 < N) {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} (hf : ∃ u, SmoothH1Approximation f g u)
    (t : Tet N) (a b : Fin 4) :
    meshScale N * (nodeMean f (gridVertexOfTet t b) - elementMean f t a) ^ 2 ≤
      6 * ∑ j : Fin 3, ∫ x in elementBox t a, (g j x) ^ 2 := by
  have hh := meshScale_pos N hN
  have ht := nested_box_mean_bound hf (by linarith : -(meshScale N) < meshScale N)
    (by linarith : -2 * meshScale N < 2 * meshScale N)
    (gridPoint (gridVertexOfTet t b)) (gridPoint (gridVertexOfTet t a))
    (nodeBox_subset_elementBox hN t a b)
  change (meshScale N - -(meshScale N)) ^ 3 *
    (nodeMean f (gridVertexOfTet t b) - elementMean f t a) ^ 2 ≤
      3 * (2 * meshScale N - -2 * meshScale N) ^ 2 *
        ∑ j : Fin 3, ∫ x in elementBox t a, (g j x) ^ 2 at ht
  have hs : (8 * (meshScale N) ^ 2) *
      (meshScale N * (nodeMean f (gridVertexOfTet t b) - elementMean f t a) ^ 2) ≤
      (8 * (meshScale N) ^ 2) *
        (6 * ∑ j : Fin 3, ∫ x in elementBox t a, (g j x) ^ 2) := by
    convert ht using 1 <;> ring
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 8 * (meshScale N) ^ 2)).mp hs

theorem boundary_nodeMean_bound {N : ℕ} (hN : 0 < N) {f : Space → ℝ}
    {g : Fin 3 → Space → ℝ} (hf : InH1ZeroCube f g)
    (t : Tet N) (a b : Fin 4) (ha : ¬ interiorNode (gridVertexOfTet t a)) :
    meshScale N * (nodeMean f (gridVertexOfTet t b)) ^ 2 ≤
      36 * ∑ j : Fin 3, ∫ x in elementBox t a, (g j x) ^ 2 := by
  have hh := meshScale_pos N hN
  have ht := nested_boundary_box_mean_bound hf (by linarith : -(meshScale N) < meshScale N)
    (by positivity : 0 < 2 * meshScale N)
    (gridPoint (gridVertexOfTet t b)) (gridPoint (gridVertexOfTet t a))
    (not_interiorNode_boundary hN ha)
    (by simpa only [nodeBox, elementBox, neg_mul] using nodeBox_subset_elementBox hN t a b)
  simp only [← neg_mul] at ht
  change (meshScale N - -(meshScale N)) ^ 3 * (nodeMean f (gridVertexOfTet t b)) ^ 2 ≤
    72 * (2 * meshScale N) ^ 2 *
      ∑ j : Fin 3, ∫ x in elementBox t a, (g j x) ^ 2 at ht
  have hs : (8 * (meshScale N) ^ 2) *
      (meshScale N * (nodeMean f (gridVertexOfTet t b)) ^ 2) ≤
      (8 * (meshScale N) ^ 2) *
        (36 * ∑ j : Fin 3, ∫ x in elementBox t a, (g j x) ^ 2) := by
    convert ht using 1 <;> ring
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 8 * (meshScale N) ^ 2)).mp hs

end FreudenthalSVLean.MeshAveragingBoxes
