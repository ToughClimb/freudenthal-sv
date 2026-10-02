import FreudenthalSVLean.EdgeJetContinuity
import FreudenthalSVLean.MeshSegments

/-!
# Actual finite-element traces imply common and boundary-zero edge jets

This module supplies the trace-to-jet part of manuscript Lemma
`vertex-jets` directly for `FreudenthalMesh.velocitySpace`: coincident
geometric edges have common issuing jets, and an edge whose endpoints lie
in the same physical coordinate boundary plane has zero issuing jets.
Closed segment containment is proved in `MeshSegments`; the implication
from values to derivatives is proved in `EdgeJetContinuity`.
The six-state classification and the converse supported lift are not
assumed or asserted by these results.
-/

open scoped BigOperators
open MvPolynomial Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.MeshSegments
open FreudenthalSVLean.EdgeJetContinuity
open FreudenthalSVLean.ScaledChainGeometry

noncomputable section

namespace FreudenthalSVLean.ConformingEdgeJets

theorem common_edge_jet {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (t u : Tet N) (a b c d : Fin 4)
    (ha : vertex t a = vertex u c) (hb : vertex t b = vertex u d) (j : Fin 3) :
    directionalJet (vertex t a) (vertex t b) (v.val t j) =
      directionalJet (vertex u c) (vertex u d) (v.val u j) := by
  rw [← ha, ← hb]
  apply directionalJet_eq_of_trace_eq
  intro s hs
  apply v.property.2.1 t u _ (edge_segment_mem hN t a b s hs) _ j
  simpa only [ha, hb] using edge_segment_mem hN u c d s hs

theorem boundary_plane_segment_mem (x y : Space) (hx : x ∈ cube) (hy : y ∈ cube)
    (j : Fin 3) (r : ℝ) (hr : r = 0 ∨ r = 1) (hxj : x j = r) (hyj : y j = r)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (fun l => (1 - s) * x l + s * y l) ∈ cubeBoundary := by
  refine ⟨?_, j, ?_⟩
  · exact convex_Icc (𝕜 := ℝ) (0 : Space) 1 hx hy
      (sub_nonneg.mpr hs.2) hs.1 (by ring)
  · change (1 - s) * x j + s * y j = 0 ∨ (1 - s) * x j + s * y j = 1
    rw [hxj, hyj]
    rcases hr with rfl | rfl <;> simp

/-- This includes physical corner and boundary-edge endpoints; no
interior-vertex hypothesis is used. -/
theorem boundary_edge_jet_zero {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (t : Tet N) (a b : Fin 4) (j l : Fin 3) (r : ℝ)
    (hr : r = 0 ∨ r = 1) (ha : vertex t a l = r) (hb : vertex t b l = r) :
    directionalJet (vertex t a) (vertex t b) (v.val t j) = 0 := by
  apply directionalJet_zero_of_trace_zero
  intro s hs
  apply v.property.2.2 t _ (edge_segment_mem hN t a b s hs) _ j
  exact boundary_plane_segment_mem _ _
    (tetrahedron_subset_cube hN t (vertex_mem_tetrahedron hN t a))
    (tetrahedron_subset_cube hN t (vertex_mem_tetrahedron hN t b))
    l r hr ha hb s hs

theorem directionalJet_scaled (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ)
    (a b : Fin 4) (p : MvPolynomial (Fin 3) ℝ) :
    directionalJet (scaledVertex σ o h a) (scaledVertex σ o h b) p =
      h * ∑ j : Fin 3, eval (scaledVertex σ o h a) (pderiv j p) *
        VertexJetAlgebra.direction σ o a b j := by
  simp only [directionalJet, scaledVertex, Pi.smul_apply, smul_eq_mul,
    VertexJetAlgebra.direction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Full derivative reconstruction on the physical element, with the
`h` in each edge direction cancelling the `h⁻¹` in each gradient. -/
theorem scaled_derivative_from_edge_jets (σ : Equiv.Perm (Fin 3)) (o : Space)
    (h : ℝ) (hh : h ≠ 0) (a : Fin 4) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    (∑ b : Fin 4, directionalJet (scaledVertex σ o h a) (scaledVertex σ o h b) p *
      eval (scaledVertex σ o h a) (pderiv i (scaledBarycentric σ o h b))) =
        eval (scaledVertex σ o h a) (pderiv i p) := by
  calc
    _ = ∑ b : Fin 4,
        (∑ j : Fin 3, eval (scaledVertex σ o h a) (pderiv j p) *
          VertexJetAlgebra.direction σ o a b j) * ChainGeometry.barycentricGradient σ b i := by
      apply Finset.sum_congr rfl
      intro b _
      rw [directionalJet_scaled, pderiv_scaledBarycentric, eval_C]
      field_simp [hh]
    _ = _ := VertexJetAlgebra.gradient_reconstruction σ o a
      (fun j => eval (scaledVertex σ o h a) (pderiv j p)) i

/-- The vertex-divergence identity `vertex-jet-map` for the actual mesh
polynomials.  Commonness and boundary-zero columns are proved above. -/
theorem divergence_vertex_from_edge_jets {N : ℕ} (hN : 0 < N)
    (v : BrokenVelocity N) (t : Tet N) (a : Fin 4) :
    eval (vertex t a) (divergence N v t) =
      ∑ b : Fin 4, ∑ j : Fin 3,
        directionalJet (vertex t a) (vertex t b) (v t j) *
          eval (vertex t a) (pderiv j (barycentric t b)) := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (scaled_derivative_from_edge_jets t.2 (cellOrigin t.1) (meshScale N)
    (meshScale_pos N hN).ne' a (v t j) j).symm

end FreudenthalSVLean.ConformingEdgeJets
