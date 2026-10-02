import FreudenthalSVLean.MeshIntersectionFaces
import FreudenthalSVLean.StableElementBubbleLift
import FreudenthalSVLean.VelocityEnergy

/-!
# Global assembly of genuine zero-face element bubbles

For manuscript Lemma `bubble` and the final local correction, any fixed
family of linear polynomial lifts with zero actual barycentric-face values
assembles into the defined homogeneous conforming velocity space.  Common
points and physical-boundary points are treated by the proved mesh face
containment theorems.  The global energy is the exact sum of local energies;
there is no mesh-dependent overlap factor.  This module does not assume
that polynomial face vanishing implies conformity.
-/

open scoped BigOperators
open MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MeshIntersectionFaces
open FreudenthalSVLean.VelocityEnergy

noncomputable section

namespace FreudenthalSVLean.ElementBubbleAssembly

set_option backward.isDefEq.respectTransparency false

abbrev Poly := MvPolynomial (Fin 3) ℝ
abbrev VectorPoly := Fin 3 → Poly
abbrev LocalFamily (N : ℕ) := Tet N → Poly →ₗ[ℝ] VectorPoly

def assemble {N : ℕ} (J : LocalFamily N) : BrokenPressure N →ₗ[ℝ] BrokenVelocity N :=
  LinearMap.pi (fun t => (J t).comp (LinearMap.proj t))

theorem assemble_apply {N : ℕ} (J : LocalFamily N) (q : BrokenPressure N)
    (t : Tet N) : assemble J q t = J t (q t) := rfl

def FaceZero {N : ℕ} (J : LocalFamily N) : Prop :=
  ∀ t p x a, eval x (barycentric t a) = 0 → ∀ j, eval x (J t p j) = 0

theorem assemble_conforming {N : ℕ} (J : LocalFamily N) (hJ : FaceZero J)
    (q : BrokenPressure N) (t u : Tet N) (x : Space)
    (ht : x ∈ tetrahedron t) (hu : x ∈ tetrahedron u) (j : Fin 3) :
    eval x (assemble J q t j) = eval x (assemble J q u j) := by
  by_cases he : t = u
  · rw [he]
  · obtain ⟨a, ha⟩ := common_point_face t u he x ht hu
    obtain ⟨b, hb⟩ := common_point_face u t (Ne.symm he) x hu ht
    rw [assemble_apply, assemble_apply, hJ t (q t) x a ha j,
      hJ u (q u) x b hb j]

theorem assemble_boundary_zero {N : ℕ} (hN : 0 < N)
    (J : LocalFamily N) (hJ : FaceZero J) (q : BrokenPressure N)
    (t : Tet N) (x : Space) (ht : x ∈ tetrahedron t)
    (hx : x ∈ cubeBoundary) (j : Fin 3) : eval x (assemble J q t j) = 0 := by
  obtain ⟨a, ha⟩ := boundary_point_face hN t x ht hx
  exact hJ t (q t) x a ha j

theorem assemble_mem {N k : ℕ} (hN : 0 < N) (J : LocalFamily N)
    (hdeg : ∀ t p j, (J t p j).totalDegree ≤ k) (hface : FaceZero J)
    (q : BrokenPressure N) : assemble J q ∈ velocitySpace N k :=
  ⟨fun t j => hdeg t (q t) j, assemble_conforming J hface q,
    assemble_boundary_zero hN J hface q⟩

/-- The local maps and geometric hypotheses are fixed before the pressure
input.  The codomain is the actual all-point conforming velocity space. -/
def assembleVelocity {N k : ℕ} (hN : 0 < N) (J : LocalFamily N)
    (hdeg : ∀ t p j, (J t p j).totalDegree ≤ k) (hface : FaceZero J) :
    BrokenPressure N →ₗ[ℝ] velocitySpace N k :=
  (assemble J).codRestrict (velocitySpace N k) (assemble_mem hN J hdeg hface)

theorem assembleVelocity_val {N k : ℕ} (hN : 0 < N) (J : LocalFamily N)
    (hdeg : ∀ t p j, (J t p j).totalDegree ≤ k) (hface : FaceZero J)
    (q : BrokenPressure N) : (assembleVelocity hN J hdeg hface q).val = assemble J q := rfl

theorem assemble_energy {N : ℕ} (J : LocalFamily N) (q : BrokenPressure N) :
    velocityEnergy (assemble J q) = ∑ t : Tet N, localEnergy t (J t (q t)) := by
  rw [velocityEnergy_eq_sum]
  rfl

theorem assemble_energy_bound {N : ℕ} (J : LocalFamily N) (d : ℕ) (C : ℝ)
    (hJ : ∀ t p, p.totalDegree ≤ d → localEnergy t (J t p) ≤
      C * ∫ x in tetrahedron t, (eval x p) ^ 2)
    (q : BrokenPressure N) (hq : ∀ t, (q t).totalDegree ≤ d) :
    velocityEnergy (assemble J q) ≤ C * pressureEnergy q := by
  rw [assemble_energy, pressureEnergy, Finset.mul_sum]
  exact Finset.sum_le_sum (fun t _ => hJ t (q t) (hq t))

end FreudenthalSVLean.ElementBubbleAssembly
