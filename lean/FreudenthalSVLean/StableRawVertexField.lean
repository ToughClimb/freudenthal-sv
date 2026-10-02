import FreudenthalSVLean.RawVertexTrace
import FreudenthalSVLean.StableStarMeanRouting

/-!
# Uniform gradient energy of the actual raw vertex field

For manuscript Lemma `vertex-local`, coordinate permutations and
translations transport each cubic barycentric bubble to one of sixteen
fixed reference polynomials.  Exact derivative-energy scaling gives the
factor `h`.  The full-mesh energy equals the sum on the actual star by the
proved polynomial support.  At most twenty-four star tetrahedra and at
most ninety-six edge descriptions give a common bound before all mesh
and vertex parameters.  The direction set removes repeated descriptions;
the non-sharp bound does not require another enumeration.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ConformingSkeletonBubble
open FreudenthalSVLean.RawVertexField
open FreudenthalSVLean.VelocityEnergy
open FreudenthalSVLean.StableStarMeanRouting
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.PolynomialChainTransport
open FreudenthalSVLean.PolynomialL2

noncomputable section

namespace FreudenthalSVLean.StableRawVertexField

def referenceBubbleEnergy (a b : Vertex) : ℝ :=
  ∑ i : Coordinate, referenceSquareIntegral
    (pderiv i (SkeletonBubble.vertexBubble (Equiv.refl Coordinate) 0 a b))

theorem referenceBubbleEnergy_nonneg (a b : Vertex) : 0 ≤ referenceBubbleEnergy a b := by
  unfold referenceBubbleEnergy referenceSquareIntegral
  exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

def referenceBubbleBound : ℝ := 1 + ∑ a : Vertex, ∑ b : Vertex, referenceBubbleEnergy a b

theorem referenceBubbleBound_pos : 0 < referenceBubbleBound := by
  have hs : 0 ≤ ∑ a : Vertex, ∑ b : Vertex, referenceBubbleEnergy a b :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => referenceBubbleEnergy_nonneg a b))
  unfold referenceBubbleBound
  linarith

theorem referenceBubbleEnergy_le_bound (a b : Vertex) :
    referenceBubbleEnergy a b ≤ referenceBubbleBound := by
  have hb := Finset.single_le_sum
    (fun c (_ : c ∈ (Finset.univ : Finset Vertex)) => referenceBubbleEnergy_nonneg a c)
    (Finset.mem_univ b)
  have ha := Finset.single_le_sum (f := fun c : Vertex => ∑ d : Vertex, referenceBubbleEnergy c d)
    (fun c (_ : c ∈ (Finset.univ : Finset Vertex)) =>
      Finset.sum_nonneg (s := Finset.univ) (fun d _ => referenceBubbleEnergy_nonneg c d)) (Finset.mem_univ a)
  unfold referenceBubbleBound
  linarith

theorem forward_vertexBubble (σ : Equiv.Perm Coordinate) (o : Space) (a b : Vertex) :
    forward σ o (SkeletonBubble.vertexBubble (Equiv.refl Coordinate) 0 a b) =
      SkeletonBubble.vertexBubble σ o a b := by
  unfold SkeletonBubble.vertexBubble
  change forward σ o (_ ^ 2 * _) = _
  rw [show forward σ o (_ ^ 2 * _) =
    (forward σ o (ChainGeometry.barycentric (Equiv.refl Coordinate) 0 a)) ^ 2 *
      forward σ o (ChainGeometry.barycentric (Equiv.refl Coordinate) 0 b) from by
        simp only [forward, map_mul, map_pow]]
  rw [forward_barycentric, forward_barycentric]

theorem unitBubble_energy (σ : Equiv.Perm Coordinate) (o : Space) (a b : Vertex) :
    (∑ i : Coordinate, ∫ x in unitChainSet σ o,
      (eval x (pderiv i (SkeletonBubble.vertexBubble σ o a b))) ^ 2) =
        referenceBubbleEnergy a b := by
  rw [← forward_vertexBubble σ o a b]
  simp only [pderiv_forward, forward_square_integral]
  unfold referenceBubbleEnergy
  exact Equiv.sum_comp σ.symm (fun i : Coordinate => referenceSquareIntegral
    (pderiv i (SkeletonBubble.vertexBubble (Equiv.refl Coordinate) 0 a b)))

theorem scaledBubble_energy {N : ℕ} (hN : 0 < N) (t : Tet N) (a b : Vertex) (s : Space) :
    localEnergy t (fun j => rescale (meshScale N) (s j)
      (SkeletonBubble.vertexBubble t.2 (cellOrigin t.1) a b)) =
        meshScale N * (∑ j : Coordinate, (s j) ^ 2) * referenceBubbleEnergy a b := by
  rw [localEnergy_eq_sum hN]
  simp only [tetrahedron, derivative_energy_scaling t.2 (cellOrigin t.1) (meshScale N)
    (meshScale_pos N hN), ← Finset.mul_sum, unitBubble_energy]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- Support makes the true whole-mesh energy an exact sum on the actual
vertex star, with no mesh-size factor. -/
theorem supported_star_energy {N : ℕ} (n : GridVertex N) (v : BrokenVelocity N)
    (hv : ∀ t : Tet N, (∀ a : Vertex, gridVertexOfTet t a ≠ n) → v t = 0) :
    velocityEnergy v = ∑ ta : VertexStar n, localEnergy ta.val.1 (v ta.val.1) := by
  classical
  let s : Finset (Tet N) := (Finset.univ : Finset (VertexStar n)).image (fun ta => ta.val.1)
  rw [velocityEnergy_eq_sum]
  calc
    _ = ∑ t ∈ s, localEnergy t (v t) := by
      apply (Finset.sum_subset (Finset.subset_univ s) ?_).symm
      intro t _ ht
      have hnot : ∀ a : Vertex, gridVertexOfTet t a ≠ n := by
        intro a he
        exact ht (Finset.mem_image.mpr ⟨⟨(t, a), he⟩, Finset.mem_univ _, rfl⟩)
      rw [hv t hnot, localEnergy_zero]
    _ = _ := by
      exact Finset.sum_image (fun ta _ tb _ he => starTet_injective n he)

theorem cubicEdge_local_energy_bound {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (d : ActiveEdge (boundaryTag n)) (s : Space) (ta : VertexStar n) :
    localEnergy ta.val.1 (edgeBubbleField N 2 (integerGrid n) (endpoint n d) s ta.val.1) ≤
      meshScale N * (∑ j : Coordinate, (s j) ^ 2) * referenceBubbleBound := by
  classical
  by_cases hm : ∃ a : Vertex, catalogRelative (starCatalog ta) a = d.val
  · obtain ⟨a, ha⟩ := hm
    have hn : GridNodalSupport.intPoint (integerGrid n) =
        chainVertex ta.val.1.2 (cellOrigin ta.val.1.1) ta.val.2 :=
      (congrArg (fun m : GridVertex N => GridNodalSupport.intPoint (integerGrid m))
        ta.property).symm.trans (gridVertex_intPoint _ _)
    have he : edgeBubbleField N 2 (integerGrid n) (endpoint n d) s ta.val.1 =
        fun j => rescale (meshScale N) (s j)
          (SkeletonBubble.vertexBubble ta.val.1.2 (cellOrigin ta.val.1.1) ta.val.2 a) := by
      funext j
      exact cubicField_on_incident_tet _ _ _ _ _ _ hn ((endpoint_is_vertex_iff ta d a).mpr ha) j
    rw [he, scaledBubble_energy hN]
    exact mul_le_mul_of_nonneg_left (referenceBubbleEnergy_le_bound _ _)
      (mul_nonneg (meshScale_pos N hN).le (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  · have hz : edgeBubbleField N 2 (integerGrid n) (endpoint n d) s ta.val.1 = 0 := by
      funext j
      apply edgeBubbleField_zero_of_missing_second
      intro a ha
      exact hm ⟨a, (endpoint_is_vertex_iff ta d a).mp ha⟩
    rw [hz, localEnergy_zero]
    exact mul_nonneg
      (mul_nonneg (meshScale_pos N hN).le (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      referenceBubbleBound_pos.le

theorem cubicEdge_global_energy_bound {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (d : ActiveEdge (boundaryTag n)) (s : Space) :
    velocityEnergy (edgeBubbleField N 2 (integerGrid n) (endpoint n d) s) ≤
      24 * meshScale N * (∑ j : Coordinate, (s j) ^ 2) * referenceBubbleBound := by
  classical
  have hs : ∀ t : Tet N, (∀ a : Vertex, gridVertexOfTet t a ≠ n) →
      edgeBubbleField N 2 (integerGrid n) (endpoint n d) s t = 0 := by
    intro t ht
    have hn : n ∉ gridVertices t := by
      intro h
      obtain ⟨a, _, he⟩ := Finset.mem_image.mp h
      exact ht a he
    funext j
    rw [edgeBubbleField, node_polynomial_zero_of_missing t n hn]
    simp
  rw [supported_star_energy n _ hs]
  calc
    _ ≤ ∑ _ta : VertexStar n,
        meshScale N * (∑ j : Coordinate, (s j) ^ 2) * referenceBubbleBound :=
      Finset.sum_le_sum (fun ta _ => cubicEdge_local_energy_bound hN n d s ta)
    _ = (Fintype.card (VertexStar n) : ℝ) *
        (meshScale N * (∑ j : Coordinate, (s j) ^ 2) * referenceBubbleBound) := by simp
    _ ≤ 24 * (meshScale N * (∑ j : Coordinate, (s j) ^ 2) * referenceBubbleBound) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast star_size_bound n)
      exact mul_nonneg
        (mul_nonneg (meshScale_pos N hN).le (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
        referenceBubbleBound_pos.le
    _ = _ := by ring

theorem activeEdge_count_bound (b : BoundaryWord) : Fintype.card (ActiveEdge b) ≤ 96 := by
  classical
  rw [Fintype.card_coe]
  calc
    _ ≤ (catalogEdges b).card := Finset.card_filter_le _ _
    _ ≤ ((Finset.univ : Finset (CatalogState × Vertex)).filter
        (fun sa => catalogAdmissible b sa.1 ∧ sa.2 ≠ sa.1.2)).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (CatalogState × Vertex)).card := Finset.card_filter_le _ _
    _ = 96 := by simp [CatalogState]

theorem jet_component_square_bound (b : BoundaryWord) (x : JetSpace b)
    (d : ActiveEdge b) (j : Coordinate) : (x d j) ^ 2 ≤ ‖x‖ ^ 2 := by
  have h : |x d j| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (x d) j).trans (norm_le_pi_norm x d)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg x)).mpr h

/-- The genuine whole-mesh gradient energy has one constant before `N`,
the marked vertex, and the jet input. -/
theorem rawField_uniform_energy : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (_hN : 0 < N)
    (n : GridVertex N) (x : JetSpace (boundaryTag n)),
    velocityEnergy (rawField n x) ≤ C * meshScale N * ‖x‖ ^ 2 := by
  classical
  refine ⟨96 ^ 2 * 24 * 3 * referenceBubbleBound, by positivity [referenceBubbleBound_pos], ?_⟩
  intro N hN n x
  have he : rawField n x = ∑ d : ActiveEdge (boundaryTag n),
      edgeBubbleField N 2 (integerGrid n) (endpoint n d) (x d) := by
    funext t j
    simpa only [Finset.sum_apply] using rawField_apply n x t j
  have hd : (Fintype.card (ActiveEdge (boundaryTag n)) : ℝ) ≤ 96 := by
    exact_mod_cast activeEdge_count_bound (boundaryTag n)
  have hn : 0 ≤ meshScale N := (meshScale_pos N hN).le
  have hc : 0 ≤ referenceBubbleBound := referenceBubbleBound_pos.le
  have hj (d : ActiveEdge (boundaryTag n)) :
      ∑ j : Coordinate, (x d j) ^ 2 ≤ 3 * ‖x‖ ^ 2 := by
    calc
      _ ≤ ∑ _j : Coordinate, ‖x‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => jet_component_square_bound _ x d j)
      _ = _ := by simp [Coordinate]
  rw [he]
  calc
    _ ≤ (Fintype.card (ActiveEdge (boundaryTag n)) : ℝ) *
        ∑ d : ActiveEdge (boundaryTag n),
          velocityEnergy (edgeBubbleField N 2 (integerGrid n) (endpoint n d) (x d)) := by
      simpa only [Finset.card_univ] using velocityEnergy_sum hN Finset.univ _
    _ ≤ 96 * ∑ d : ActiveEdge (boundaryTag n),
        24 * meshScale N * (∑ j : Coordinate, (x d j) ^ 2) * referenceBubbleBound := by
      apply mul_le_mul hd (Finset.sum_le_sum (fun d _ => cubicEdge_global_energy_bound hN n d (x d)))
        (Finset.sum_nonneg (fun _ _ => velocityEnergy_nonneg _)) (by norm_num)
    _ ≤ 96 * ∑ _d : ActiveEdge (boundaryTag n),
        24 * meshScale N * (3 * ‖x‖ ^ 2) * referenceBubbleBound := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hj d) (by positivity)) hc
    _ = 96 * (Fintype.card (ActiveEdge (boundaryTag n)) : ℝ) *
        (24 * meshScale N * (3 * ‖x‖ ^ 2) * referenceBubbleBound) := by simp; ring
    _ ≤ 96 * 96 * (24 * meshScale N * (3 * ‖x‖ ^ 2) * referenceBubbleBound) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (by positivity)
    _ = _ := by ring

end FreudenthalSVLean.StableRawVertexField
