import FreudenthalSVLean.StableVertexLift
import FreudenthalSVLean.BoundedOverlapEnergy
import FreudenthalSVLean.PressureVertexBound

/-!
# Complete arbitrary-mesh vertex stage with uniform stability

For manuscript Proposition `vertex`, fixed local mean-preserving cubic
lifts are assembled over all grid vertices.  At a tetrahedron only its
four vertices contribute, so the pointwise overlap factor is four.
An explicit equivalence counts every tetrahedron--vertex incidence once.
Together with the proved pressure vertex inverse estimate, this yields a
single fixed linear vertex corrector on every positive-size mesh, with
zero element means and a stability constant independent of `N`.

This is the vertex stage, not the complete divergence right inverse.
Edge correction, mean correction, final global assembly, and the weak
Sobolev interface remain separate obligations.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.RawVertexField
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.MeanPreservingVertexLift
open FreudenthalSVLean.ConformingVertexCompatibility
open FreudenthalSVLean.StableVertexLift
open FreudenthalSVLean.BoundedOverlapEnergy
open FreudenthalSVLean.PressureVertexBound

noncomputable section

namespace FreudenthalSVLean.GlobalVertexLift

abbrev LiftFamily := ∀ b : BoundaryWord, (compatibility b).range →ₗ[ℝ] JetSpace b

def allIncidencesEquiv (N : ℕ) : (Σ n : GridVertex N, VertexStar n) ≃ Tet N × Vertex where
  toFun p := p.2.val
  invFun ta := ⟨gridVertexOfTet ta.1 ta.2, ⟨ta, rfl⟩⟩
  left_inv p := by
    rcases p with ⟨n, ⟨⟨t, a⟩, h⟩⟩
    cases h
    rfl
  right_inv ta := rfl

theorem incidence_sum {M : Type*} [AddCommMonoid M] (N : ℕ) (f : Tet N × Vertex → M) :
    (∑ n : GridVertex N, ∑ ta : VertexStar n, f ta.val) =
      ∑ t : Tet N, ∑ a : Vertex, f (t, a) := by
  calc
    _ = ∑ p : (Σ n : GridVertex N, VertexStar n), f p.2.val := (Fintype.sum_sigma _).symm
    _ = ∑ ta : Tet N × Vertex, f ta := Equiv.sum_comp (allIncidencesEquiv N) f
    _ = _ := Fintype.sum_prod_type f

theorem pressureData_square_sum {N k : ℕ} (hN : 0 < N) (n : GridVertex N)
    (q : pressureSpace N k) :
    (∑ s : Incidence (boundaryTag n), ((pressureCompatibilityData hN n q).val s) ^ 2) =
      ∑ ta : VertexStar n, (eval (vertex ta.val.1 ta.val.2) (q.val ta.val.1)) ^ 2 := by
  rw [← Equiv.sum_comp (catalogIncidenceEquiv hN n)
    (fun s => ((pressureCompatibilityData hN n q).val s) ^ 2)]
  apply Finset.sum_congr rfl
  intro ta _
  change (vertexTrace hN n q.val (catalogIncidenceEquiv hN n ta)) ^ 2 = _
  rw [vertexTrace_incidence]

def vertexCorrection {N k : ℕ} (hN : 0 < N) (J : LiftFamily) :
    pressureSpace N k →ₗ[ℝ] velocitySpace N 3 :=
  ∑ n : GridVertex N, (vertexLift hN n (J (boundaryTag n))).comp (pressureCompatibilityData hN n)

theorem vertexCorrection_apply {N k : ℕ} (hN : 0 < N) (J : LiftFamily)
    (q : pressureSpace N k) :
    (vertexCorrection hN J q).val = ∑ n : GridVertex N,
      (vertexLift hN n (J (boundaryTag n)) (pressureCompatibilityData hN n q)).val := by
  simp only [vertexCorrection, LinearMap.sum_apply, LinearMap.comp_apply, Submodule.coe_sum]

theorem vertexCorrection_mean_zero {N k : ℕ} (hN : 0 < N) (J : LiftFamily)
    (q : pressureSpace N k) (t : Tet N) :
    tetIntegral hN t (divergence N (vertexCorrection hN J q).val t) = 0 := by
  rw [vertexCorrection_apply]
  simp only [map_sum, Finset.sum_apply, vertexLift_mean_zero, Finset.sum_const_zero]

theorem vertexCorrection_vertex_divergence {N k : ℕ} (hN : 0 < N) (J : LiftFamily)
    (hJ : ∀ b (x : (compatibility b).range), compatibility b (J b x) = x.val)
    (q : pressureSpace N k) (t : Tet N) (a : Vertex) :
    eval (vertex t a) (divergence N (vertexCorrection hN J q).val t) =
      eval (vertex t a) (q.val t) := by
  classical
  rw [vertexCorrection_apply]
  simp only [map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single (gridVertexOfTet t a)]
  · let n := gridVertexOfTet t a
    let ta : VertexStar n := ⟨(t, a), rfl⟩
    have he := vertexLift_right_inverse hN n (J (boundaryTag n)) (hJ (boundaryTag n))
      (pressureCompatibilityData hN n q) ta
    change eval _ (divergence N (vertexLift hN n (J (boundaryTag n))
      (pressureCompatibilityData hN n q)).val t) = _
    rw [he]
    change vertexTrace hN n q.val (catalogIncidenceEquiv hN n ta) = _
    exact vertexTrace_incidence hN n q.val ta
  · intro n _ hn
    exact vertexLift_protects_other_vertices hN n (J (boundaryTag n))
      (pressureCompatibilityData hN n q) t a hn.symm
  · simp

theorem vertexCorrection_overlap_energy {N k : ℕ} (hN : 0 < N) (J : LiftFamily)
    (q : pressureSpace N k) :
    velocityEnergy (vertexCorrection hN J q).val ≤ 4 * ∑ n : GridVertex N,
      velocityEnergy (vertexLift hN n (J (boundaryTag n)) (pressureCompatibilityData hN n q)).val := by
  classical
  rw [vertexCorrection_apply]
  apply velocityEnergy_sum_overlap hN Finset.univ _ 4 (by norm_num)
  intro t
  refine ⟨gridVertices t, Finset.subset_univ _, ?_, ?_⟩
  · rw [gridVertices, Finset.card_image_of_injective _ (gridVertexOfTet_injective t)]
    norm_num
  · intro n _ hn
    have hnot : ∀ a : Vertex, gridVertexOfTet t a ≠ n := by
      intro a he
      exact hn (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, he⟩)
    funext j
    exact vertexLift_zero_off_star hN n (J (boundaryTag n)) (pressureCompatibilityData hN n q) t hnot j

/-- Complete vertex-stage stability on the actual finite-element pressure
image.  This does not assert that all remaining pressure residuals vanish. -/
theorem vertex_stage_uniform (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ J : LiftFamily,
      (∀ b (x : (compatibility b).range), compatibility b (J b x) = x.val) ∧
      (∀ (N : ℕ) (hN : 0 < N) (q : pressureSpace N k),
        velocityEnergy (vertexCorrection hN J q).val ≤ C * pressureEnergy q.val) := by
  obtain ⟨CL, hCL, J, hright, hL⟩ := vertexLift_uniform_energy
  obtain ⟨CP, hCP, hP⟩ := pressure_vertex_bound k
  refine ⟨4 * CL * CP, by positivity, J, hright, ?_⟩
  intro N hN q
  calc
    _ ≤ 4 * ∑ n : GridVertex N,
        velocityEnergy (vertexLift hN n (J (boundaryTag n)) (pressureCompatibilityData hN n q)).val :=
      vertexCorrection_overlap_energy hN J q
    _ ≤ 4 * ∑ n : GridVertex N,
        CL * (meshScale N) ^ 3 * ∑ s : Incidence (boundaryTag n),
          ((pressureCompatibilityData hN n q).val s) ^ 2 := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => hL N hN n _)) (by norm_num)
    _ = (4 * CL) * ((meshScale N) ^ 3 *
        (∑ t : Tet N, ∑ a : Vertex, (eval (vertex t a) (q.val t)) ^ 2)) := by
      simp only [pressureData_square_sum, ← Finset.mul_sum]
      rw [incidence_sum N (fun ta => (eval (vertex ta.1 ta.2) (q.val ta.1)) ^ 2)]
      ring
    _ ≤ (4 * CL) * (CP * pressureEnergy q.val) :=
      mul_le_mul_of_nonneg_left (hP N hN q) (by positivity)
    _ = _ := by ring

def degreeInclusion {N k l : ℕ} (hkl : k ≤ l) : velocitySpace N k →ₗ[ℝ] velocitySpace N l :=
  (velocitySpace N k).subtype.codRestrict _ (velocitySpace_degree_mono hkl)

/-- The vertex correction lies in the requested velocity space whenever
`k ≥ 3`, hence in particular for the quartic and quintic theorem. -/
theorem vertex_stage (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (hN : 0 < N),
      ∃ R : pressureSpace N k →ₗ[ℝ] velocitySpace N k,
        (∀ q t a, eval (vertex t a) (divergence N (R q).val t) = eval (vertex t a) (q.val t)) ∧
        (∀ q t, tetIntegral hN t (divergence N (R q).val t) = 0) ∧
        (∀ q, velocityEnergy (R q).val ≤ C * pressureEnergy q.val) := by
  obtain ⟨C, hC, J, hJ, hb⟩ := vertex_stage_uniform k
  refine ⟨C, hC, ?_⟩
  intro N hN
  refine ⟨(degreeInclusion hk).comp (vertexCorrection hN J), ?_, ?_, ?_⟩
  · intro q t a
    exact vertexCorrection_vertex_divergence hN J hJ q t a
  · intro q t
    exact vertexCorrection_mean_zero hN J q t
  · intro q
    exact hb N hN q

end FreudenthalSVLean.GlobalVertexLift
