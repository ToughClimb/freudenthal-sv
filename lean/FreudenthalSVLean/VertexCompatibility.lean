import FreudenthalSVLean.VertexEdgeCoverage
import FreudenthalSVLean.FiniteLinearLifting
import FreudenthalSVLean.SkeletonBubble

/-!
# The actual finite vertex compatibility map

For manuscript equations `vertex-div-map` and `vertex-raw-bubble`, the
source consists of one three-component jet for each active geometric edge,
not one jet for each repeated tetrahedral description of that edge.  The
target is indexed by all admissible tetrahedral incidences.  The map below
is obtained by differentiating the explicit cubic barycentric fields.

Its exact image has a fixed linear right inverse with a common bound over
all twenty-seven boundary words.  The equality of this image with traces
of the global velocity space and assembly on the physical mesh are
separate statements; neither is assumed here.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.VertexEdgeCoverage
open FreudenthalSVLean.FiniteLinearLifting

noncomputable section

namespace FreudenthalSVLean.VertexCompatibility

abbrev BoundaryWord := Coordinate → Fin 3
abbrev Incidence (b : BoundaryWord) := {s : CatalogState // catalogAdmissible b s}
abbrev ActiveEdge (b : BoundaryWord) := {d : Coordinate → ℤ // d ∈ catalogActiveEdges b}
abbrev JetSpace (b : BoundaryWord) := ActiveEdge b → Coordinate → ℝ
abbrev VertexData (b : BoundaryWord) := Incidence b → ℝ

instance (b : BoundaryWord) : Fintype (ActiveEdge b) :=
  inferInstanceAs (Fintype {d // d ∈ catalogActiveEdges b})

theorem catalogRelative_injective : ∀ s : CatalogState,
    Function.Injective (catalogRelative s) := by
  decide +kernel

theorem catalogRelative_self (s : CatalogState) : catalogRelative s s.2 = 0 := by
  funext j
  simp [catalogRelative]

theorem zero_not_edge (b : BoundaryWord) : (0 : Coordinate → ℤ) ∉ catalogEdges b := by
  intro h
  obtain ⟨⟨s, a⟩, hs, ha⟩ := Finset.mem_image.mp h
  have hne := (Finset.mem_filter.mp hs).2.2
  exact hne (catalogRelative_injective s (ha.trans (catalogRelative_self s).symm))

theorem active_other (b : BoundaryWord) (s : CatalogState) (a : Vertex)
    (ha : catalogRelative s a ∈ catalogActiveEdges b) : a ≠ s.2 := by
  intro h
  have he := (Finset.mem_filter.mp ha).1
  rw [h, catalogRelative_self] at he
  exact zero_not_edge b he

def compatibility (b : BoundaryWord) : JetSpace b →ₗ[ℝ] VertexData b := by
  classical
  refine
    { toFun := fun x t => ∑ a : Vertex,
        if ha : catalogRelative t.val a ∈ catalogActiveEdges b then
          ∑ j : Coordinate, barycentricGradient (orderPerm t.val.1) a j *
            x ⟨catalogRelative t.val a, ha⟩ j
        else 0
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    funext t
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
  · intro c x
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp [Finset.mul_sum, mul_left_comm]

/-- The translated unit tetrahedron has the marked vertex at the origin. -/
def unitOrigin (s : CatalogState) : Coordinate → ℝ :=
  fun j => -(catalogPrefix s j : ℝ)

theorem unit_vertex (s : CatalogState) (a : Vertex) :
    chainVertex (orderPerm s.1) (unitOrigin s) a =
      GridNodalSupport.intPoint (catalogRelative s a) := by
  funext j
  simp only [chainVertex, unitOrigin, orderPerm_symm_eq_rank,
    GridNodalSupport.intPoint, catalogRelative, Int.cast_sub, Int.cast_natCast]
  unfold catalogPrefix
  split_ifs <;> norm_num

def rawLocal (b : BoundaryWord) :
    JetSpace b →ₗ[ℝ] (Incidence b → Coordinate → MvPolynomial Coordinate ℝ) := by
  classical
  refine
    { toFun := fun x t j => ∑ a : Vertex,
        if ha : catalogRelative t.val a ∈ catalogActiveEdges b then
          C (x ⟨catalogRelative t.val a, ha⟩ j) *
            SkeletonBubble.vertexBubble (orderPerm t.val.1) (unitOrigin t.val) t.val.2 a
        else 0
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    funext t j
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp [map_add, add_mul]
  · intro c x
    funext t j
    simp [Pi.smul_apply, smul_eq_C_mul, map_mul, Finset.mul_sum, mul_assoc]

/-- Differentiation of actual spatial polynomials gives the declared
compatibility map, with all repeated geometric edge descriptions sharing
the same source coordinate. -/
theorem rawLocal_vertex_derivative (b : BoundaryWord) (x : JetSpace b)
    (t : Incidence b) (l : Vertex) (i j : Coordinate) :
    eval (chainVertex (orderPerm t.val.1) (unitOrigin t.val) l)
      (pderiv i (rawLocal b x t j)) =
        if l = t.val.2 then
          ∑ a : Vertex, if ha : catalogRelative t.val a ∈ catalogActiveEdges b then
            x ⟨catalogRelative t.val a, ha⟩ j *
              barycentricGradient (orderPerm t.val.1) a i else 0
        else 0 := by
  classical
  dsimp only [rawLocal, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sum, map_sum]
  by_cases hl : l = t.val.2
  · rw [if_pos hl]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs with ha
    · rw [pderiv_C_mul, map_mul, eval_C,
        SkeletonBubble.pderiv_vertexBubble_vertex _ _ _ _ _ _
          (active_other b t.val a ha).symm, if_pos hl]
    · simp
  · rw [if_neg hl]
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with ha
    · rw [pderiv_C_mul, map_mul, eval_C,
        SkeletonBubble.pderiv_vertexBubble_vertex _ _ _ _ _ _
          (active_other b t.val a ha).symm, if_neg hl, mul_zero]
    · simp

theorem rawLocal_vertex_divergence (b : BoundaryWord) (x : JetSpace b)
    (t : Incidence b) :
    eval (chainVertex (orderPerm t.val.1) (unitOrigin t.val) t.val.2)
      (∑ j : Coordinate, pderiv j (rawLocal b x t j)) = compatibility b x t := by
  classical
  rw [map_sum]
  simp only [rawLocal_vertex_derivative, ite_true]
  rw [Finset.sum_comm]
  dsimp only [compatibility, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with ha
  · simp only [mul_comm]
  · simp only [Finset.sum_const_zero]

theorem fixed_bounded_compatibility_lifts :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ∀ b : BoundaryWord,
      (compatibility b).range →ₗ[ℝ] JetSpace b,
      (∀ b (x : (compatibility b).range), compatibility b (J b x) = x.val) ∧
      (∀ b (x : (compatibility b).range), ‖J b x‖ ≤ C * ‖x‖) := by
  exact finite_family_range_lifts JetSpace VertexData compatibility

end FreudenthalSVLean.VertexCompatibility
