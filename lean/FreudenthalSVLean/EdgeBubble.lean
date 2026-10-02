import FreudenthalSVLean.SkeletonBubble

/-!
# Endpoint and middle edge modes

The manuscript's analytic edge-lift lemma uses
`λ_a^(k-2) λ_b λ_c z` for the endpoint modes, and
`λ_a^2 λ_b^2 λ_c z` for the middle quintic mode.  This module proves their
actual local derivative traces on a coordinate-chain tetrahedron.

The endpoint formula applies to every integer exponent `r ≥ 2`, including
the quartic and quintic choices `r=2,3`.  The middle bubble has a derivative
trace only on its designated edge.  Constant vector components can be
combined linearly with these scalar identities.

Incidence-space spanning, borrowed-face constructions, global conformity,
and norm estimates are not asserted by these local identities alone.
-/

open MvPolynomial
open FreudenthalSVLean.ChainGeometry

noncomputable section

namespace FreudenthalSVLean.EdgeBubble

variable {R : Type*} [CommRing R]

def endpointBubble (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (r : ℕ) (a b c : Vertex) : MvPolynomial Coordinate R :=
  barycentric σ o a ^ r * barycentric σ o b * barycentric σ o c

/-- Setting the opposite face coordinate to zero leaves exactly the desired
edge factor multiplying its gradient. -/
theorem pderiv_endpointBubble_on_face (σ : Equiv.Perm Coordinate)
    (o x : Coordinate → R) (r : ℕ) (a b c : Vertex) (j : Coordinate)
    (hc : eval x (barycentric σ o c) = 0) :
    eval x (pderiv j (endpointBubble σ o r a b c)) =
      eval x (barycentric σ o a) ^ r * eval x (barycentric σ o b) *
        barycentricGradient σ c j := by
  simp [endpointBubble, pderiv_barycentric, hc]

/-- The repeated endpoint factor protects every edge not containing `a`. -/
theorem pderiv_endpointBubble_zero_of_a_zero (σ : Equiv.Perm Coordinate)
    (o x : Coordinate → R) (r : ℕ) (hr : 2 ≤ r) (a b c : Vertex) (j : Coordinate)
    (ha : eval x (barycentric σ o a) = 0) :
    eval x (pderiv j (endpointBubble σ o r a b c)) = 0 := by
  have h₀ : r ≠ 0 := by omega
  have h₁ : r - 1 ≠ 0 := by omega
  simp [endpointBubble, pderiv_barycentric, ha, h₀, h₁]

/-- Two other missing factors protect edges containing `a` but neither
remaining face vertex. -/
theorem pderiv_endpointBubble_zero_of_b_c_zero (σ : Equiv.Perm Coordinate)
    (o x : Coordinate → R) (r : ℕ) (a b c : Vertex) (j : Coordinate)
    (hb : eval x (barycentric σ o b) = 0)
    (hc : eval x (barycentric σ o c) = 0) :
    eval x (pderiv j (endpointBubble σ o r a b c)) = 0 := by
  simp [endpointBubble, pderiv_barycentric, hb, hc]

/-- Endpoint incidence trace on the actual parametrized edge `[a,b]`. -/
theorem pderiv_endpointBubble_edge (σ : Equiv.Perm Coordinate)
    (o : Coordinate → R) (r : ℕ) (a b c : Vertex) (j : Coordinate) (s : R)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    eval (segmentPoint (chainVertex σ o a) (chainVertex σ o b) s)
      (pderiv j (endpointBubble σ o r a b c)) =
      (1 - s) ^ r * s * barycentricGradient σ c j := by
  rw [pderiv_endpointBubble_on_face]
  · simp [barycentric_edge, hab, Ne.symm hab]
  · simp [barycentric_edge, Ne.symm hac, Ne.symm hbc]

def middleBubble (σ : Equiv.Perm Coordinate) (o : Coordinate → R)
    (a b c : Vertex) : MvPolynomial Coordinate R :=
  barycentric σ o a ^ 2 * barycentric σ o b ^ 2 * barycentric σ o c

/-- Middle quintic incidence trace on the designated edge. -/
theorem pderiv_middleBubble_edge (σ : Equiv.Perm Coordinate)
    (o : Coordinate → R) (a b c : Vertex) (j : Coordinate) (s : R)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    eval (segmentPoint (chainVertex σ o a) (chainVertex σ o b) s)
      (pderiv j (middleBubble σ o a b c)) =
      (1 - s) ^ 2 * s ^ 2 * barycentricGradient σ c j := by
  simp [middleBubble, pderiv_barycentric,
    barycentric_edge, hab, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

/-- Missing either repeated endpoint annihilates every derivative of the
middle bubble, so all other edges are protected. -/
theorem pderiv_middleBubble_zero_of_endpoint_zero (σ : Equiv.Perm Coordinate)
    (o x : Coordinate → R) (a b c : Vertex) (j : Coordinate)
    (h : eval x (barycentric σ o a) = 0 ∨ eval x (barycentric σ o b) = 0) :
    eval x (pderiv j (middleBubble σ o a b c)) = 0 := by
  rcases h with ha | hb <;>
    simp [middleBubble, pderiv_barycentric, *]

end FreudenthalSVLean.EdgeBubble
