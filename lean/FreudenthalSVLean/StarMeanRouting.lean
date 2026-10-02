import FreudenthalSVLean.ActualFaceMean

/-!
# Fixed linear mean routing by actual supported cubic velocity fields

For manuscript Lemma `vertex-local`, every zero-sum vector of element
means on an actual vertex star is lifted by a fixed linear combination of
the proved conforming face transfers.  The output is an actual cubic
velocity, vanishes on every non-star element, and preserves all mesh
vertex-divergence rows.  The graph, root, and paths are fixed from the mesh
vertex before the mean data arrive.  A path has at most twenty-three edges.
Uniform gradient-energy estimates and the composition with the raw
edge-jet lift are subsequent obligations.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarSymmetry
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceMean
open FreudenthalSVLean.MeanRoutingAlgebra

noncomputable section

namespace FreudenthalSVLean.StarMeanRouting

def tetIntegral {N : ℕ} (hN : 0 < N) (t : Tet N) : MvPolynomial Coordinate ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x in tetrahedron t, eval x p
  map_add' p q := by
    simp only [map_add]
    exact integral_add
      ((continuous_eval p).continuousOn.integrableOn_compact (μ := volume)
        (tetrahedron_isCompact hN t))
      ((continuous_eval q).continuousOn.integrableOn_compact (μ := volume)
        (tetrahedron_isCompact hN t))
  map_smul' c p := by
    simp only [smul_eq_C_mul, map_mul, eval_C, smul_eq_mul]
    exact integral_const_mul c _

def supportedZeroVertexCubic {N : ℕ} (n : GridVertex N) :
    Submodule ℝ (velocitySpace N 3) where
  carrier v :=
    (∀ (t : Tet N) (l : Vertex), eval (vertex t l) (divergence N v.val t) = 0) ∧
    (∀ t : Tet N, (∀ a : Vertex, gridVertexOfTet t a ≠ n) → ∀ j : Coordinate, v.val t j = 0)
  zero_mem' := by
    constructor <;> intros <;> simp
  add_mem' := by
    intro v w hv hw
    constructor
    · intro t l
      simp only [Submodule.coe_add, map_add, Pi.add_apply, (hv.1 t l), (hw.1 t l), add_zero]
    · intro t ht j
      simp only [Submodule.coe_add, Pi.add_apply, hv.2 t ht j, hw.2 t ht j, add_zero]
  smul_mem' := by
    intro c v hv
    constructor
    · intro t l
      simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_C_mul, map_mul,
        eval_C, hv.1 t l, mul_zero]
    · intro t ht j
      simp only [Submodule.coe_smul, Pi.smul_apply, hv.2 t ht j, smul_zero]

def starMeans {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    supportedZeroVertexCubic n →ₗ[ℝ] (VertexStar n → ℝ) where
  toFun v ta := tetIntegral hN ta.val.1 (divergence N v.val.val ta.val.1)
  map_add' v w := by
    funext ta
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' c v := by
    funext ta
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem facePair_exists {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (h : (actualGraph n).Adj ta tb) :
    ∃ p : Vertex × Vertex,
      p.1 ≠ ta.val.2 ∧ p.2 ≠ tb.val.2 ∧ gridFace ta.val.1 p.1 = gridFace tb.val.1 p.2 := by
  obtain ⟨r, u, hr, hu, he⟩ := h.2
  exact ⟨(r, u), hr, hu, he⟩

def facePair {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (h : (actualGraph n).Adj ta tb) : Vertex × Vertex :=
  Classical.choose (facePair_exists ta tb h)

theorem facePair_spec {N : ℕ} {n : GridVertex N} (ta tb : VertexStar n)
    (h : (actualGraph n).Adj ta tb) :
    (facePair ta tb h).1 ≠ ta.val.2 ∧ (facePair ta tb h).2 ≠ tb.val.2 ∧
      gridFace ta.val.1 (facePair ta tb h).1 = gridFace tb.val.1 (facePair ta tb h).2 :=
  Classical.choose_spec (facePair_exists ta tb h)

def orientedTransfer {N : ℕ} (hN : 0 < N) (n : GridVertex N) (ta tb : VertexStar n)
    (h : (actualGraph n).Adj ta tb) : supportedZeroVertexCubic n := by
  let p := facePair ta tb h
  have hf := facePair_spec ta tb h
  refine ⟨⟨transferField N ta.val.1 p.1,
    transfer_mem_velocitySpace hN ta tb p.1 p.2 hf.1 hf.2.1 h.1 hf.2.2⟩, ?_⟩
  constructor
  · intro t l
    change eval (vertex t l) (∑ j : Coordinate,
      pderiv j (transferField N ta.val.1 p.1 t j)) = 0
    simp only [map_sum, transfer_protects_vertices hN ta tb p.1 p.2 hf.1 h.1 hf.2.2,
      Finset.sum_const_zero]
  · intro t ht j
    have hta : t ≠ ta.val.1 := by
      intro heq
      exact ht ta.val.2 (heq ▸ ta.property)
    have htb : t ≠ tb.val.1 := by
      intro heq
      exact ht tb.val.2 (heq ▸ tb.property)
    exact transfer_zero_off_pair ta tb p.1 p.2 hf.1 h.1 hf.2.2 t hta htb j

/-- The actual divergence means of the oriented global field are exactly
the signed graph incidence vector. -/
theorem orientedTransfer_means {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (ta tb : VertexStar n) (h : (actualGraph n).Adj ta tb) :
    starMeans hN n (orientedTransfer hN n ta tb h) = Pi.single ta 1 - Pi.single tb 1 := by
  classical
  let p := facePair ta tb h
  obtain ⟨hr, hu, he⟩ := facePair_spec ta tb h
  have hne : ta ≠ tb := by
    intro heq
    exact h.1 (congrArg (fun x : VertexStar n => x.val.1) heq)
  funext tc
  change (∫ x in tetrahedron tc.val.1,
    eval x (divergence N (transferField N ta.val.1 p.1) tc.val.1)) = _
  by_cases hca : tc = ta
  · subst tc
    rw [transfer_mean_one hN]
    simp [hne]
  · by_cases hcb : tc = tb
    · subst tc
      rw [transfer_mean_minus_one hN ta tb p.1 p.2 hr hu h.1 he]
      simp [hne.symm]
    · have hta : tc.val.1 ≠ ta.val.1 := (starTet_injective n).ne hca
      have htb : tc.val.1 ≠ tb.val.1 := (starTet_injective n).ne hcb
      rw [transfer_mean_off_pair ta tb p.1 p.2 hr h.1 he tc.val.1 hta htb]
      simp [hca, hcb]

def starRoot {N : ℕ} (hN : 0 < N) (n : GridVertex N) : VertexStar n :=
  Classical.choice (actualGraph_connected hN n).nonempty

def starRouting {N : ℕ} (hN : 0 < N) (n : GridVertex N) :
    zeroSum (V := VertexStar n) →ₗ[ℝ] supportedZeroVertexCubic n :=
  routingLinear (actualGraph n) (actualGraph_connected hN n) (starRoot hN n)
    (orientedTransfer hN n)

theorem starRouting_means {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (m : zeroSum (V := VertexStar n)) : starMeans hN n (starRouting hN n m) = m.val := by
  unfold starRouting
  exact routingLinear_means (actualGraph n) (actualGraph_connected hN n) (starRoot hN n)
    (orientedTransfer hN n) (starMeans hN n) (orientedTransfer_means hN n) m

theorem starRouting_protects_vertices {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (m : zeroSum (V := VertexStar n)) (t : Tet N) (l : Vertex) :
    eval (vertex t l) (divergence N (starRouting hN n m).val.val t) = 0 :=
  (starRouting hN n m).property.1 t l

theorem starRouting_zero_off_star {N : ℕ} (hN : 0 < N) (n : GridVertex N)
    (m : zeroSum (V := VertexStar n)) (t : Tet N)
    (ht : ∀ a : Vertex, gridVertexOfTet t a ≠ n) (j : Coordinate) :
    (starRouting hN n m).val.val t j = 0 := (starRouting hN n m).property.2 t ht j

theorem star_path_length_bound {N : ℕ} (hN : 0 < N) (n : GridVertex N) (ta : VertexStar n) :
    (rootPath (actualGraph n) (actualGraph_connected hN n) (starRoot hN n) ta).length ≤ 23 := by
  classical
  have hc : Fintype.card (VertexStar n) ≤ 24 := by
    calc
      _ = Fintype.card {s : State // admissible n s} := Fintype.card_congr (starStateEquiv n)
      _ ≤ Fintype.card State := Fintype.card_subtype_le _
      _ = 24 := state_count
  have hp := rootPath_length_bound (actualGraph n) (actualGraph_connected hN n) (starRoot hN n) ta
  omega

end FreudenthalSVLean.StarMeanRouting
