import FreudenthalSVLean.RawVertexTrace
import FreudenthalSVLean.VertexMeanCancellation

/-!
# Zero total mean of actual global vertex corrections

For manuscript equation `vertex-raw-properties`, the true divergence
means of the actual global cubic field are identified with the universal
mean map times `h²/60`.  The exact arbitrary-mesh incidence equivalence
then transfers the proved integer cancellation to every interior and
boundary vertex of every positive `N`.

Consequently the raw mean map takes values in the zero-sum subspace on
which the fixed, supported face-transfer routing operator is defined.
No divergence theorem or zero-total-mean assumption is imported.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.VertexCompatibility
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.ConformingSkeletonBubble
open FreudenthalSVLean.PolynomialScaling
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.StarMeanRouting
open FreudenthalSVLean.MeanRoutingAlgebra
open FreudenthalSVLean.FaceBubbleMean
open FreudenthalSVLean.RawVertexMean
open FreudenthalSVLean.RawVertexField
open FreudenthalSVLean.VertexMeanCancellation

noncomputable section

namespace FreudenthalSVLean.ActualRawVertexMean

theorem scaledBubble_derivative_mean {N : ℕ} (hN : 0 < N) (t : Tet N)
    (a b : Vertex) (hab : a ≠ b) (c : ℝ) (i : Coordinate) :
    tetIntegral hN t (pderiv i (rescale (meshScale N) c
      (SkeletonBubble.vertexBubble t.2 (cellOrigin t.1) a b))) =
        (meshScale N) ^ 2 *
          (c * (barycentricGradient t.2 a i + barycentricGradient t.2 b i) / 60) := by
  change (∫ x in scaledChainSet t.2 (cellOrigin t.1) (meshScale N), eval x
    (pderiv i (rescale (meshScale N) c
      (SkeletonBubble.vertexBubble t.2 (cellOrigin t.1) a b)))) = _
  rw [derivative_mean_scaling t.2 (cellOrigin t.1) (meshScale N) (meshScale_pos N hN)]
  change c * (meshScale N) ^ 2 * unitSpatialIntegral t.2 (cellOrigin t.1)
    (pderiv i (SkeletonBubble.vertexBubble t.2 (cellOrigin t.1) a b)) = _
  rw [vertexBubble_derivative_mean t.2 (cellOrigin t.1) a b hab i]
  ring

theorem cubicEdge_mean_expansion {N : ℕ} (hN : 0 < N) {n : GridVertex N}
    (ta : VertexStar n) (d : ActiveEdge (boundaryTag n)) (s : Space) :
    tetIntegral hN ta.val.1
      (divergence N (edgeBubbleField N 2 (integerGrid n) (endpoint n d) s) ta.val.1) =
        ∑ j : Coordinate, ∑ a : Vertex,
          if catalogRelative (starCatalog ta) a = d.val then
            (meshScale N) ^ 2 * (s j *
              (barycentricGradient ta.val.1.2 ta.val.2 j +
                barycentricGradient ta.val.1.2 a j) / 60)
          else 0 := by
  change tetIntegral hN ta.val.1 (∑ j : Coordinate,
    pderiv j (edgeBubbleField N 2 (integerGrid n) (endpoint n d) s ta.val.1 j)) = _
  simp only [local_cubic_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : catalogRelative (starCatalog ta) a = d.val
  · have hab : ta.val.2 ≠ a := by
      simpa only [starCatalog_cut] using
        (active_other (boundaryTag n) (starCatalog ta) a (he.symm ▸ d.property)).symm
    simp only [if_pos he]
    exact scaledBubble_derivative_mean hN ta.val.1 ta.val.2 a hab (s j) j
  · simp [he]

theorem cubicEdge_mean_entry {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (ta : VertexStar n) (d : ActiveEdge (boundaryTag n)) (s : Space) :
    tetIntegral hN ta.val.1
      (divergence N (edgeBubbleField N 2 (integerGrid n) (endpoint n d) s) ta.val.1) =
        ((meshScale N) ^ 2 / 60) * ∑ j : Coordinate,
          s j * realMeanEntry (boundaryTag n) (catalogIncidenceEquiv hN n ta) d j := by
  rw [cubicEdge_mean_expansion]
  simp only [realMeanEntry, catalogIncidenceEquiv_val, starCatalog_perm,
    starCatalog_cut, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

def rawMeans {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    JetSpace (boundaryTag n) →ₗ[ℝ] (VertexStar n → ℝ) where
  toFun x ta := tetIntegral hN ta.val.1 (divergence N (rawField n x) ta.val.1)
  map_add' x y := by
    funext ta
    simp only [map_add, Pi.add_apply]
  map_smul' c x := by
    funext ta
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem rawMeans_catalog {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) (ta : VertexStar n) :
    rawMeans hN n x ta = ((meshScale N) ^ 2 / 60) *
      localMeanNumerator (boundaryTag n) x (catalogIncidenceEquiv hN n ta) := by
  change tetIntegral hN ta.val.1 (∑ j : Coordinate, pderiv j (rawField n x ta.val.1 j)) = _
  simp only [rawField_apply, map_sum]
  rw [Finset.sum_comm]
  simp only [localMeanNumerator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  have he := cubicEdge_mean_entry hN n ta d (x d)
  change (∑ j : Coordinate, tetIntegral hN ta.val.1
    (pderiv j (edgeBubbleField N 2 (integerGrid n) (endpoint n d) (x d) ta.val.1 j))) = _
  simpa only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    Finset.mul_sum] using he

/-- The true element means have zero total, for arbitrary mesh size and
every boundary vertex configuration. -/
theorem rawMeans_sum_zero {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (x : JetSpace (boundaryTag n)) : ∑ ta : VertexStar n, rawMeans hN n x ta = 0 := by
  calc
    _ = ((meshScale N) ^ 2 / 60) *
        ∑ ta : VertexStar n,
          localMeanNumerator (boundaryTag n) x (catalogIncidenceEquiv hN n ta) := by
      simp only [rawMeans_catalog, Finset.mul_sum]
    _ = ((meshScale N) ^ 2 / 60) *
        ∑ t : Incidence (boundaryTag n), localMeanNumerator (boundaryTag n) x t := by
      rw [Equiv.sum_comp (catalogIncidenceEquiv hN n)]
    _ = 0 := by rw [localMeanNumerator_sum_zero, mul_zero]

def rawMeanZeroSum {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    JetSpace (boundaryTag n) →ₗ[ℝ] zeroSum (V := VertexStar n) :=
  (rawMeans hN n).codRestrict _ (fun x => (mem_zeroSum _).mpr (rawMeans_sum_zero hN n x))

end FreudenthalSVLean.ActualRawVertexMean
