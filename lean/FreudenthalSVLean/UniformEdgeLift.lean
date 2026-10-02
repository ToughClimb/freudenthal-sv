import FreudenthalSVLean.CanonicalLiftSupport

/-!
# Uniform lifting of every actual edge trace in degrees four and five

For manuscript Lemma `edge-lift`, a single linear operator is chosen from
the geometric edge before its pressure input.  Canonical barycentric
face lifts are transported by proved physical mesh symmetries.  All
interior and boundary configurations are covered for every positive `N`,
including `N=1,2`.  The lift matches the entire edge polynomial, preserves
every vertex gradient and every other edge divergence trace, and has one
mesh-independent integral energy constant.

The statement here is the edge-jet stage before element-mean routing.
It does not assert preservation of element means or a global right inverse.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualEdgeCoverage
open FreudenthalSVLean.CanonicalEdgeCoverage
open FreudenthalSVLean.ActualOrderedEdgeGeometry
open FreudenthalSVLean.CubeMeshSymmetry
open FreudenthalSVLean.CubePolynomialTransport
open FreudenthalSVLean.CanonicalEdgeOrientation
open FreudenthalSVLean.CanonicalPressureLift
open FreudenthalSVLean.CubeTraceTransport
open FreudenthalSVLean.CanonicalLiftSupport
open FreudenthalSVLean.EdgePressureData

noncomputable section

namespace FreudenthalSVLean.UniformEdgeLift

set_option backward.isDefEq.respectTransparency false

structure EdgeLiftSpec {N k : ℕ} (a b : GridVertex N)
    (R : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ) : Prop where
  match_trace : ∀ (q : vertexZeroSpace N k) (x : ActualEdgeStar a b) (s : ℝ),
    pressureTrace a b s (divergence N (R q).val) x = pressureTrace a b s q.val x
  vertex_gradient : ∀ (q : vertexZeroSpace N k) (t : Tet N) (l : Vertex) (i j : Coordinate),
    eval (vertex t l) (pderiv i ((R q).val t j)) = 0
  protect_edges : ∀ (q : vertexZeroSpace N k) (t : Tet N) (l m : Vertex), l ≠ m →
    ({gridVertexOfTet t l, gridVertexOfTet t m} : Finset (GridVertex N)) ≠ {a, b} → ∀ s : ℝ,
      eval (segmentPoint (vertex t l) (vertex t m) s) (divergence N (R q).val t) = 0
  energy_bound : ∀ q : vertexZeroSpace N k,
    velocityEnergy (R q).val ≤ C * starPressureEnergy a b q.val
  off_endpoints : ∀ (q : vertexZeroSpace N k) (t : Tet N),
    (∀ l : Vertex, gridVertexOfTet t l ≠ a ∧ gridVertexOfTet t l ≠ b) → (R q).val t = 0

def transportedQuartic {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (π : Equiv.Perm Coordinate) (flip : Bool)
    (hd : displacement (firstNode π flip a b) (secondNode π flip a b) =
      positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation (firstNode π flip a b) c) :
    vertexZeroSpace N 4 →ₗ[ℝ] velocitySpace N 4 :=
  (velocityMap π.symm flip).comp
    ((quarticMap hN (firstNode π flip a b) (secondNode π flip a b) c hd hl).comp
      (zeroPressureMap hN π flip))

def transportedQuintic {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (π : Equiv.Perm Coordinate) (flip : Bool)
    (hd : displacement (firstNode π flip a b) (secondNode π flip a b) =
      positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation (firstNode π flip a b) c) :
    vertexZeroSpace N 5 →ₗ[ℝ] velocitySpace N 5 :=
  (velocityMap π.symm flip).comp
    ((quinticMap hN (firstNode π flip a b) (secondNode π flip a b) c hd hl).comp
      (zeroPressureMap hN π flip))

theorem transportedQuartic_spec {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (π : Equiv.Perm Coordinate) (flip : Bool)
    (hd : displacement (firstNode π flip a b) (secondNode π flip a b) =
      positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation (firstNode π flip a b) c) (C : ℝ)
    (hC : ∀ q : vertexZeroSpace N 4,
      velocityEnergy (quarticMap hN (firstNode π flip a b) (secondNode π flip a b) c hd hl q).val ≤
        C * starPressureEnergy (firstNode π flip a b) (secondNode π flip a b) q.val) :
    EdgeLiftSpec a b (transportedQuartic hN a b c π flip hd hl) C := by
  constructor
  · intro q x s
    change pressureTrace a b s (divergence N (pushVelocity π.symm flip
      (quarticMap hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
        (zeroPressureMap hN π flip q)).val)) x = _
    rw [pushback_pressure_trace hN, quarticMap_trace]
    exact oriented_pressure_trace hN π flip a b q.val x s
  · intro q t l i j
    exact vertex_derivative_transport hN π.symm flip _
      (quarticMap_vertex hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
        (zeroPressureMap hN π flip q)) t l i j
  · intro q t l m hlm he s
    exact other_edge_transport hN π flip a b _
      (quarticMap_other_edge hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
        (zeroPressureMap hN π flip q)) t l m hlm he s
  · intro q
    change velocityEnergy (pushVelocity π.symm flip
      (quarticMap hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
        (zeroPressureMap hN π flip q)).val) ≤ _
    rw [pushVelocity_energy]
    have hb := hC (zeroPressureMap hN π flip q)
    change _ ≤ C * starPressureEnergy (firstNode π flip a b) (secondNode π flip a b)
      (pushPressure π flip q.val) at hb
    rwa [starPressureEnergy_transport hN] at hb
  · intro q t ht
    exact endpoint_star_transport π flip a b _
      (quarticMap_off_star hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
        (zeroPressureMap hN π flip q)) t ht

theorem transportedQuintic_spec {N : ℕ} (hN : 0 < N) (a b : GridVertex N) (c : Fin 7)
    (π : Equiv.Perm Coordinate) (flip : Bool)
    (hd : displacement (firstNode π flip a b) (secondNode π flip a b) =
      positiveDirection (canonicalDirectionIndex c))
    (hl : CanonicalLocation (firstNode π flip a b) c) (C : ℝ)
    (hC : ∀ q : vertexZeroSpace N 5,
      velocityEnergy (quinticMap hN (firstNode π flip a b) (secondNode π flip a b) c hd hl q).val ≤
        C * starPressureEnergy (firstNode π flip a b) (secondNode π flip a b) q.val) :
    EdgeLiftSpec a b (transportedQuintic hN a b c π flip hd hl) C := by
  constructor
  · intro q x s
    change pressureTrace a b s (divergence N (pushVelocity π.symm flip
      (quinticMap hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
        (zeroPressureMap hN π flip q)).val)) x = _
    rw [pushback_pressure_trace hN, quinticMap_trace]
    exact oriented_pressure_trace hN π flip a b q.val x s
  · intro q t l i j
    exact vertex_derivative_transport hN π.symm flip _
      (quinticMap_vertex hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
        (zeroPressureMap hN π flip q)) t l i j
  · intro q t l m hlm he s
    exact other_edge_transport hN π flip a b _
      (quinticMap_other_edge hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
        (zeroPressureMap hN π flip q)) t l m hlm he s
  · intro q
    change velocityEnergy (pushVelocity π.symm flip
      (quinticMap hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
        (zeroPressureMap hN π flip q)).val) ≤ _
    rw [pushVelocity_energy]
    have hb := hC (zeroPressureMap hN π flip q)
    change _ ≤ C * starPressureEnergy (firstNode π flip a b) (secondNode π flip a b)
      (pushPressure π flip q.val) at hb
    rwa [starPressureEnergy_transport hN] at hb
  · intro q t ht
    exact endpoint_star_transport π flip a b _
      (quinticMap_off_star hN (firstNode π flip a b) (secondNode π flip a b) c hd hl
        (zeroPressureMap hN π flip q)) t ht

/-- Every increasing nontrivial actual edge has quartic and quintic
linear lifts, with one constant preceding all mesh and edge quantifiers. -/
theorem increasing_edge_lifts : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (_hN : 0 < N) (a b : GridVertex N) (_hab : a ≠ b),
      (∀ j, (a j).val ≤ (b j).val) → ActualEdgeStar a b →
      ∃ (R₄ : vertexZeroSpace N 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : vertexZeroSpace N 5 →ₗ[ℝ] velocitySpace N 5),
        EdgeLiftSpec a b R₄ C ∧ EdgeLiftSpec a b R₅ C := by
  obtain ⟨C, hC, hbound⟩ := canonical_pressure_energy
  refine ⟨C, hC, ?_⟩
  intro N hN a b hab horder x
  obtain ⟨d, hd⟩ := increasing_edge_direction a b hab horder x
  obtain ⟨π, flip, hdir, hl⟩ := actual_canonical_orientation hN a b d hd
  let c := incidenceKind (boundaryTag a) d
  have hb := hbound N hN (firstNode π flip a b) (secondNode π flip a b) c hdir hl
  exact ⟨transportedQuartic hN a b c π flip hdir hl,
    transportedQuintic hN a b c π flip hdir hl,
    transportedQuartic_spec hN a b c π flip hdir hl C hb.1,
    transportedQuintic_spec hN a b c π flip hdir hl C hb.2⟩

theorem reverse_pressure_trace {N : ℕ} (a b : GridVertex N) (q : BrokenPressure N)
    (x : ActualEdgeStar a b) (s : ℝ) :
    pressureTrace b a (1 - s) q (reverseEdgeStar a b x) = pressureTrace a b s q x := by
  change eval (segmentPoint (gridPoint b) (gridPoint a) (1 - s)) (q x.val.1.val.1) = _
  have he : segmentPoint (gridPoint b) (gridPoint a) (1 - s) =
      segmentPoint (gridPoint a) (gridPoint b) s := by
    funext j
    simp only [segmentPoint]
    ring
  rw [he]
  rfl

theorem reverse_star_energy {N : ℕ} (a b : GridVertex N) (q : BrokenPressure N) :
    starPressureEnergy b a q = starPressureEnergy a b q := by
  unfold starPressureEnergy
  rw [← (reverseEdgeStar a b).sum_comp]
  rfl

theorem reverse_spec {N k : ℕ} (a b : GridVertex N)
    (R : vertexZeroSpace N k →ₗ[ℝ] velocitySpace N k) (C : ℝ)
    (h : EdgeLiftSpec b a R C) : EdgeLiftSpec a b R C := by
  constructor
  · intro q x s
    have ht := h.match_trace q (reverseEdgeStar a b x) (1 - s)
    rwa [reverse_pressure_trace, reverse_pressure_trace] at ht
  · exact h.vertex_gradient
  · intro q t l m hlm he s
    apply h.protect_edges q t l m hlm _ s
    intro hi
    apply he
    exact hi.trans (Finset.pair_comm b a)
  · intro q
    simpa only [reverse_star_energy] using h.energy_bound q
  · intro q t ht
    exact h.off_endpoints q t (fun l => ⟨(ht l).2, (ht l).1⟩)

/-- Both polynomial degrees, every actual edge orientation and every
interior or boundary location share one physical energy bound. -/
theorem uniform_edge_lifts : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (_hN : 0 < N) (a b : GridVertex N), a ≠ b → ActualEdgeStar a b →
      ∃ (R₄ : vertexZeroSpace N 4 →ₗ[ℝ] velocitySpace N 4)
        (R₅ : vertexZeroSpace N 5 →ₗ[ℝ] velocitySpace N 5),
        EdgeLiftSpec a b R₄ C ∧ EdgeLiftSpec a b R₅ C := by
  obtain ⟨C, hC, hLift⟩ := increasing_edge_lifts
  refine ⟨C, hC, ?_⟩
  intro N hN a b hab x
  rcases edge_endpoints_comparable a b x with horder | horder
  · exact hLift N hN a b hab horder x
  · obtain ⟨R₄, R₅, h₄, h₅⟩ := hLift N hN b a hab.symm horder (reverseEdgeStar a b x)
    exact ⟨R₄, R₅, reverse_spec a b R₄ C h₄, reverse_spec a b R₅ C h₅⟩

end FreudenthalSVLean.UniformEdgeLift
