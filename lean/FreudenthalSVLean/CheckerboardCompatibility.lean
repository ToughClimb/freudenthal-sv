import FreudenthalSVLean.FaceJumpCompatibility

/-!
# Analytic four-sector checkerboard compatibility

For manuscript equation `edge-checkerboard`, four conforming polynomial
pieces meeting along an edge have two pairs of opposite face jumps.
If each pair has a common conormal direction and the two directions are
independent, the alternating gradient sum belongs to both one-dimensional
conormal spaces and therefore vanishes.  This module proves the statement
for actual mesh polynomials and actual shared faces, at every common
point, using the already derived trace-to-jump identity.

The geometric conormal and incidence hypotheses are explicit: the result
does not assume a checkerboard relation as input.  Discharging them for
each interior face diagonal is a separate mesh-coverage obligation.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.EdgeJetContinuity
open FreudenthalSVLean.FaceJumpCompatibility

noncomputable section

namespace FreudenthalSVLean.CheckerboardCompatibility

theorem checkerboard_gradient {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (t₀ t₁ t₂ t₃ : Tet N) (r₀₁ s₀₁ r₂₃ s₂₃ r₀₂ s₀₂ r₁₃ s₁₃ : Vertex)
    (h₀₁ : gridFace t₀ r₀₁ = gridFace t₁ s₀₁)
    (h₂₃ : gridFace t₂ r₂₃ = gridFace t₃ s₂₃)
    (h₀₂ : gridFace t₀ r₀₂ = gridFace t₂ s₀₂)
    (h₁₃ : gridFace t₁ r₁₃ = gridFace t₃ s₁₃)
    (n m : Space) (c₀₁ c₂₃ c₀₂ c₁₃ : ℝ)
    (hn₀₁ : ∀ a, barycentricGradient t₀.2 r₀₁ a = c₀₁ * n a)
    (hn₂₃ : ∀ a, barycentricGradient t₂.2 r₂₃ a = c₂₃ * n a)
    (hm₀₂ : ∀ a, barycentricGradient t₀.2 r₀₂ a = c₀₂ * m a)
    (hm₁₃ : ∀ a, barycentricGradient t₁.2 r₁₃ a = c₁₃ * m a)
    (i j : Coordinate) (hminor : n i * m j - n j * m i ≠ 0)
    (x : Space) (h₀ : x ∈ tetrahedron t₀) (h₁ : x ∈ tetrahedron t₁)
    (h₂ : x ∈ tetrahedron t₂) (h₃ : x ∈ tetrahedron t₃) (a b : Coordinate) :
    eval x (pderiv a (v.val t₀ b)) - eval x (pderiv a (v.val t₁ b)) -
      eval x (pderiv a (v.val t₂ b)) + eval x (pderiv a (v.val t₃ b)) = 0 := by
  let J₀₁ := directionalJet x (vertex t₀ r₀₁) (v.val t₀ b - v.val t₁ b)
  let J₂₃ := directionalJet x (vertex t₂ r₂₃) (v.val t₂ b - v.val t₃ b)
  let J₀₂ := directionalJet x (vertex t₀ r₀₂) (v.val t₀ b - v.val t₂ b)
  let J₁₃ := directionalJet x (vertex t₁ r₁₃) (v.val t₁ b - v.val t₃ b)
  let w : Space := fun q => eval x (pderiv q (v.val t₀ b)) -
    eval x (pderiv q (v.val t₁ b)) - eval x (pderiv q (v.val t₂ b)) +
      eval x (pderiv q (v.val t₃ b))
  have hn (q : Coordinate) :
      w q = (J₀₁ * (meshScale N)⁻¹ * c₀₁ - J₂₃ * (meshScale N)⁻¹ * c₂₃) * n q := by
    have hA := scalar_gradient_jump hN v t₀ t₁ r₀₁ s₀₁ h₀₁ x h₀ h₁ q b
    have hB := scalar_gradient_jump hN v t₂ t₃ r₂₃ s₂₃ h₂₃ x h₂ h₃ q b
    rw [hn₀₁ q] at hA
    rw [hn₂₃ q] at hB
    change w q = _
    dsimp [w, J₀₁, J₂₃]
    linear_combination hA - hB
  have hm (q : Coordinate) :
      w q = (J₀₂ * (meshScale N)⁻¹ * c₀₂ - J₁₃ * (meshScale N)⁻¹ * c₁₃) * m q := by
    have hA := scalar_gradient_jump hN v t₀ t₂ r₀₂ s₀₂ h₀₂ x h₀ h₂ q b
    have hB := scalar_gradient_jump hN v t₁ t₃ r₁₃ s₁₃ h₁₃ x h₁ h₃ q b
    rw [hm₀₂ q] at hA
    rw [hm₁₃ q] at hB
    change w q = _
    dsimp [w, J₀₂, J₁₃]
    linear_combination hA - hB
  have hz := conormal_intersection_zero w n m
    (J₀₁ * (meshScale N)⁻¹ * c₀₁ - J₂₃ * (meshScale N)⁻¹ * c₂₃)
    (J₀₂ * (meshScale N)⁻¹ * c₀₂ - J₁₃ * (meshScale N)⁻¹ * c₁₃) i j hn hm hminor
  exact congrFun hz a

theorem checkerboard_divergence {N k : ℕ} (hN : 0 < N) (v : velocitySpace N k)
    (t₀ t₁ t₂ t₃ : Tet N) (r₀₁ s₀₁ r₂₃ s₂₃ r₀₂ s₀₂ r₁₃ s₁₃ : Vertex)
    (h₀₁ : gridFace t₀ r₀₁ = gridFace t₁ s₀₁)
    (h₂₃ : gridFace t₂ r₂₃ = gridFace t₃ s₂₃)
    (h₀₂ : gridFace t₀ r₀₂ = gridFace t₂ s₀₂)
    (h₁₃ : gridFace t₁ r₁₃ = gridFace t₃ s₁₃)
    (n m : Space) (c₀₁ c₂₃ c₀₂ c₁₃ : ℝ)
    (hn₀₁ : ∀ a, barycentricGradient t₀.2 r₀₁ a = c₀₁ * n a)
    (hn₂₃ : ∀ a, barycentricGradient t₂.2 r₂₃ a = c₂₃ * n a)
    (hm₀₂ : ∀ a, barycentricGradient t₀.2 r₀₂ a = c₀₂ * m a)
    (hm₁₃ : ∀ a, barycentricGradient t₁.2 r₁₃ a = c₁₃ * m a)
    (i j : Coordinate) (hminor : n i * m j - n j * m i ≠ 0)
    (x : Space) (h₀ : x ∈ tetrahedron t₀) (h₁ : x ∈ tetrahedron t₁)
    (h₂ : x ∈ tetrahedron t₂) (h₃ : x ∈ tetrahedron t₃) :
    eval x (divergence N v.val t₀) - eval x (divergence N v.val t₁) -
      eval x (divergence N v.val t₂) + eval x (divergence N v.val t₃) = 0 := by
  simp only [divergence, LinearMap.coe_mk, AddHom.coe_mk, map_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  exact checkerboard_gradient hN v t₀ t₁ t₂ t₃ r₀₁ s₀₁ r₂₃ s₂₃ r₀₂ s₀₂ r₁₃ s₁₃
    h₀₁ h₂₃ h₀₂ h₁₃ n m c₀₁ c₂₃ c₀₂ c₁₃ hn₀₁ hn₂₃ hm₀₂ hm₁₃
    i j hminor x h₀ h₁ h₂ h₃ b b

end FreudenthalSVLean.CheckerboardCompatibility
