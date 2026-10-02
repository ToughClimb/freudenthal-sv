import FreudenthalSVLean.ClassicalVelocityGradient
import FreudenthalSVLean.FiniteClosedConvexGluing
import FreudenthalSVLean.MeshSegments

/-!
# Lipschitz zero extensions of actual conforming polynomial velocities

For the manuscript's Sobolev interface, the continuous velocity extension
has a finite closed convex cover consisting of actual tetrahedra and the
six exterior coordinate halfspaces.  On the former it equals its genuine
polynomial and on the latter it is zero.  Compactness bounds each actual
polynomial derivative.  The proved finite closed-convex gluing theorem
therefore gives a global Lipschitz bound, including all boundary points
and lines contained in mesh interfaces.  The Lipschitz constant may depend
on the input velocity and mesh; no uniform inverse estimate is inferred
from this membership argument.  Weak integration by parts and H1_0
identification remain separate obligations.
-/

open scoped BigOperators NNReal
open MvPolynomial Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshCoverage
open FreudenthalSVLean.MeshSegments
open FreudenthalSVLean.ConformingVelocityFunction
open FreudenthalSVLean.PolynomialCalculus

noncomputable section

namespace FreudenthalSVLean.ConformingVelocityLipschitz

set_option backward.isDefEq.respectTransparency false

abbrev CoverIndex (N : ℕ) := Tet N ⊕ (Fin 3 × Bool)

def coverSet (N : ℕ) : CoverIndex N → Set Space
  | .inl t => tetrahedron t
  | .inr (j, false) => {x | x j ≤ 0}
  | .inr (j, true) => {x | 1 ≤ x j}

theorem coverSet_isClosed {N : ℕ} (hN : 0 < N) (i : CoverIndex N) : IsClosed (coverSet N i) := by
  rcases i with t | ⟨j, b⟩
  · exact (tetrahedron_isCompact hN t).isClosed
  · cases b
    · exact isClosed_le (continuous_apply j) continuous_const
    · exact isClosed_le continuous_const (continuous_apply j)

theorem coverSet_convex (N : ℕ) (i : CoverIndex N) : Convex ℝ (coverSet N i) := by
  rcases i with t | ⟨j, b⟩
  · exact scaledChainSet_convex t.2 (cellOrigin t.1) (meshScale N)
  · cases b
    · exact (convex_Iic (𝕜 := ℝ) (0 : ℝ)).linear_preimage (LinearMap.proj j : Space →ₗ[ℝ] ℝ)
    · exact (convex_Ici (𝕜 := ℝ) (1 : ℝ)).linear_preimage (LinearMap.proj j : Space →ₗ[ℝ] ℝ)

theorem coverSet_covers {N : ℕ} (hN : 0 < N) : ⋃ i : CoverIndex N, coverSet N i = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hc : x ∈ cube
  · obtain ⟨t, ht⟩ := cube_covered N hN x hc
    exact mem_iUnion.mpr ⟨.inl t, ht⟩
  · by_cases hl : ∀ j : Fin 3, 0 ≤ x j
    · have hu : ¬ ∀ j : Fin 3, x j ≤ 1 := fun h => hc ⟨hl, h⟩
      obtain ⟨j, hj⟩ := not_forall.mp hu
      exact mem_iUnion.mpr ⟨.inr (j, true), (lt_of_not_ge hj).le⟩
    · obtain ⟨j, hj⟩ := not_forall.mp hl
      exact mem_iUnion.mpr ⟨.inr (j, false), (lt_of_not_ge hj).le⟩

def localFunction {N k : ℕ} (v : velocitySpace N k) (j : Fin 3) : CoverIndex N → Space → ℝ
  | .inl t => fun x => eval x (v.val t j)
  | .inr _ => fun _ => 0

def localDerivative {N k : ℕ} (v : velocitySpace N k) (j : Fin 3) :
    CoverIndex N → Space → Space →L[ℝ] ℝ
  | .inl t => gradientMap (v.val t j)
  | .inr _ => fun _ => 0

theorem localFunction_matches {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (j : Fin 3) (i : CoverIndex N) :
    EqOn (velocityFunction hN v j) (localFunction v j i) (coverSet N i) := by
  rcases i with t | ⟨l, b⟩
  · exact fun x hx => velocityFunction_on_element hN v t x hx j
  · intro x hx
    apply velocityFunction_zero_off_openCube hN v j x
    intro ho
    have hp := (mem_openCube x).mp ho l
    cases b
    · change x l ≤ 0 at hx
      linarith [hp.1]
    · change 1 ≤ x l at hx
      linarith [hp.2]

theorem localFunction_hasFDerivAt {N k : ℕ} (v : velocitySpace N k)
    (j : Fin 3) (i : CoverIndex N) (x : Space) :
    HasFDerivAt (localFunction v j i) (localDerivative v j i x) x := by
  rcases i with t | i
  · exact hasFDerivAt_eval (v.val t j) x
  · exact hasFDerivAt_const (𝕜 := ℝ) 0 x

theorem gradientMap_continuous (p : MvPolynomial (Fin 3) ℝ) : Continuous (gradientMap p) := by
  unfold gradientMap
  exact continuous_finsetSum _ (fun i _ => (continuous_eval (pderiv i p)).smul continuous_const)

theorem localDerivative_uniform_on_cover {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : CoverIndex N) (x : Space), x ∈ coverSet N i →
      ‖localDerivative v j i x‖ ≤ C := by
  classical
  choose K hK using fun t : Tet N => (tetrahedron_isCompact hN t).exists_bound_of_continuousOn
    (gradientMap_continuous (v.val t j)).continuousOn
  let C : ℝ := 1 + ∑ t : Tet N, max 0 (K t)
  have hs : 0 ≤ ∑ t : Tet N, max 0 (K t) :=
    Finset.sum_nonneg (fun t _ => le_max_left _ _)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  rintro (t | i) x hx
  · have ht : max 0 (K t) ≤ ∑ u : Tet N, max 0 (K u) :=
      Finset.single_le_sum (fun u _ => le_max_left _ _) (Finset.mem_univ t)
    exact (hK t x hx).trans (by dsimp [C]; linarith [le_max_right (0 : ℝ) (K t)])
  · change ‖(0 : Space →L[ℝ] ℝ)‖ ≤ C
    simpa only [norm_zero] using hC.le

theorem velocityFunction_norm_difference {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) : ∃ C : ℝ, 0 < C ∧ ∀ x y : Space,
      ‖velocityFunction hN v j y - velocityFunction hN v j x‖ ≤ C * ‖y - x‖ := by
  obtain ⟨C, hC, hb⟩ := localDerivative_uniform_on_cover hN v j
  refine ⟨C, hC, ?_⟩
  intro x y
  exact FiniteClosedConvexGluing.norm_difference_bound (coverSet N) (coverSet_isClosed hN)
    (coverSet_convex N) (coverSet_covers hN) (velocityFunction hN v j)
    (velocityFunction_continuous hN v j) (localFunction v j) (localDerivative v j)
    (localFunction_matches hN v j) (localFunction_hasFDerivAt v j) C hb x y

theorem velocityFunction_lipschitz {N k : ℕ} (hN : 0 < N)
    (v : velocitySpace N k) (j : Fin 3) :
    ∃ C : ℝ≥0, LipschitzWith C (velocityFunction hN v j) := by
  obtain ⟨C, hC, hb⟩ := velocityFunction_norm_difference hN v j
  refine ⟨NNReal.mk C hC.le, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  change ‖velocityFunction hN v j x - velocityFunction hN v j y‖ ≤ C * ‖x - y‖
  exact hb y x

end FreudenthalSVLean.ConformingVelocityLipschitz
