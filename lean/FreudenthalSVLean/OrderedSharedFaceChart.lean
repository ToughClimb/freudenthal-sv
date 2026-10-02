import FreudenthalSVLean.ActualFaceMean
import FreudenthalSVLean.WeakLinearFaceTrace
import FreudenthalSVLean.FaceL2MeanEstimate

/-!
# Identical ordered charts and opposite weak fluxes on shared faces

For manuscript Lemma `means`, the increasing chain order on each
Freudenthal tetrahedron induces the same order on the three nodes of a
shared face. The exact finite statement concerns integer vertex geometry,
not ranks or Sobolev data. Injective displacement of actual arbitrary-N
vertex stars transports it to every shared mesh face. Consequently the
two actual triangle charts are identical pointwise, their genuine L2
weak traces coincide, and their outward weighted fluxes are opposite.
The trace identity follows from a common genuine smooth approximation;
it is not inferred from volume almost-everywhere equality on a face.
-/

open scoped BigOperators Topology
open MeasureTheory Filter
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexStarConnectivity
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.ScaledFaceGauss
open FreudenthalSVLean.BarycentricFaceGeometry
open FreudenthalSVLean.BarycentricFaceIntegral
open FreudenthalSVLean.TriangleBernsteinIntegral
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.FaceL2MeanEstimate

noncomputable section

namespace FreudenthalSVLean.OrderedSharedFaceChart

set_option backward.isDefEq.respectTransparency false

/-- Exact ordered geometry; no mesh-size or field parameter is sampled. -/
theorem catalog_shared_face_order : ∀ (s t : VertexStarTypes.CatalogState) (r u : Fin 4),
    catalogFace s r = catalogFace t u →
      ∀ i : Fin 3, catalogRelative s (r.succAbove i) = catalogRelative t (u.succAbove i) := by
  decide +kernel

theorem actual_shared_face_order {N : ℕ} {n : GridVertex N}
    (ta tb : VertexStar n) (r s : Fin 4) (he : gridFace ta.val.1 r = gridFace tb.val.1 s)
    (i : Fin 3) :
    gridVertexOfTet ta.val.1 (r.succAbove i) = gridVertexOfTet tb.val.1 (s.succAbove i) := by
  have hcat : catalogFace (starCatalog ta) r = catalogFace (starCatalog tb) s := by
    rw [← displaced_catalogFace, ← displaced_catalogFace, he]
  have ho := catalog_shared_face_order (starCatalog ta) (starCatalog tb) r s hcat i
  funext j
  apply Fin.ext
  have ha := catalog_displacement ta (r.succAbove i) j
  have hb := catalog_displacement tb (s.succAbove i) j
  have hj := congrFun ho j
  omega

theorem scaledFaceChart_ordered_vertices {N : ℕ} (t : Tet N) (r : Fin 4) (x : FacePoint) :
    scaledFaceChart t.2 (cellOrigin t.1) (meshScale N) r x =
      ∑ i : Fin 3, triangleBarycentric x i • vertex t (r.succAbove i) := by
  funext j
  simp only [scaledFaceChart, faceChart, AffineBarycentric.affinePoint,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [Fin.sum_univ_succAbove _ r]
  simp only [faceBarycentric, Fin.insertNth_apply_same, zero_mul, zero_add,
    Fin.insertNth_apply_succAbove, Finset.mul_sum, vertex, ScaledChainGeometry.scaledVertex,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem actual_shared_face_chart {N : ℕ} {n : GridVertex N}
    (ta tb : VertexStar n) (r s : Fin 4) (he : gridFace ta.val.1 r = gridFace tb.val.1 s)
    (x : FacePoint) :
    scaledFaceChart ta.val.1.2 (cellOrigin ta.val.1.1) (meshScale N) r x =
      scaledFaceChart tb.val.1.2 (cellOrigin tb.val.1.1) (meshScale N) s x := by
  rw [scaledFaceChart_ordered_vertices, scaledFaceChart_ordered_vertices]
  apply Finset.sum_congr rfl
  intro i _
  rw [← gridVertexOfTet_point, ← gridVertexOfTet_point, actual_shared_face_order ta tb r s he i]

theorem actual_shared_smooth_trace {N : ℕ} {n : GridVertex N}
    (ta tb : VertexStar n) (r s : Fin 4) (he : gridFace ta.val.1 r = gridFace tb.val.1 s)
    {u : Space → ℝ} (hu : ContDiff ℝ 1 u) :
    smoothFaceL2 hu ta.val.1.2 (cellOrigin ta.val.1.1) (meshScale N) r =
      smoothFaceL2 hu tb.val.1.2 (cellOrigin tb.val.1.1) (meshScale N) s := by
  exact MemLp.toLp_congr
    (smooth_face_memLp hu ta.val.1.2 (cellOrigin ta.val.1.1) (meshScale N) r)
    (smooth_face_memLp hu tb.val.1.2 (cellOrigin tb.val.1.1) (meshScale N) s)
    (Eventually.of_forall (fun x => congrArg u (actual_shared_face_chart ta tb r s he x)))

theorem actual_shared_weak_trace {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r s : Fin 4) (he : gridFace ta.val.1 r = gridFace tb.val.1 s)
    (v : smoothH1Space) :
    traceMap ta.val.1.2 (cellOrigin ta.val.1.1) (meshScale N) (meshScale_pos N hN) r v =
      traceMap tb.val.1.2 (cellOrigin tb.val.1.1) (meshScale N) (meshScale_pos N hN) s v := by
  obtain ⟨u, hu⟩ := v.property
  have ha := trace_spec ta.val.1.2 (cellOrigin ta.val.1.1) (meshScale N)
    (meshScale_pos N hN) r v u hu
  have hb := trace_spec tb.val.1.2 (cellOrigin tb.val.1.1) (meshScale N)
    (meshScale_pos N hN) s v u hu
  exact tendsto_nhds_unique ha (hb.congr' (Eventually.of_forall
    (fun m => (actual_shared_smooth_trace ta tb r s he (hu.smooth m)).symm)))

theorem actual_shared_weak_flux {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta tb : VertexStar n) (r s : Fin 4) (hr : r ≠ ta.val.2) (hs : s ≠ tb.val.2)
    (hne : ta.val.1 ≠ tb.val.1) (he : gridFace ta.val.1 r = gridFace tb.val.1 s)
    (v : Fin 3 → smoothH1Space) :
    traceFlux ta.val.1.2 (meshScale N) r (fun j =>
      traceMap ta.val.1.2 (cellOrigin ta.val.1.1) (meshScale N) (meshScale_pos N hN) r (v j)) =
      -traceFlux tb.val.1.2 (meshScale N) s (fun j =>
        traceMap tb.val.1.2 (cellOrigin tb.val.1.1) (meshScale N) (meshScale_pos N hN) s (v j)) := by
  unfold traceFlux
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [actual_shared_weak_trace hN ta tb r s he]
  simp only [outwardWeight, actual_shared_gradients_opposite ta tb r s hr hs hne he j]
  ring

end FreudenthalSVLean.OrderedSharedFaceChart
