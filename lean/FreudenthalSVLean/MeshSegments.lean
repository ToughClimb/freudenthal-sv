import FreudenthalSVLean.MeshCoverage
import Mathlib.Analysis.Convex.Basic

/-!
# Closed edge segments in the actual Freudenthal tetrahedra

Manuscript Lemma `vertex-jets` uses common traces on every geometric edge,
including its endpoints and physical-boundary edges.  This module proves
convexity of the actual tetrahedron sets, membership of their actual
vertices, and containment of the entire segment between any two vertices.
These statements hold for every mesh size, not just reference states.
-/

open scoped BigOperators
open Set
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.ScaledChainGeometry
open FreudenthalSVLean.FreudenthalMesh

noncomputable section

namespace FreudenthalSVLean.MeshSegments

theorem coordinateChainSet_convex : Convex ℝ coordinateChainSet := by
  let P (j : Fin 3) : Space →ₗ[ℝ] ℝ := LinearMap.proj j
  have h0 := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).linear_preimage (P 0)
  have h1 := (convex_Ici (𝕜 := ℝ) (0 : ℝ)).linear_preimage (P 1)
  have h10 := (convex_Iic (𝕜 := ℝ) (0 : ℝ)).linear_preimage (P 1 - P 0)
  have h2 := (convex_Ici (𝕜 := ℝ) (0 : ℝ)).linear_preimage (P 2)
  have h21 := (convex_Iic (𝕜 := ℝ) (0 : ℝ)).linear_preimage (P 2 - P 1)
  have he : coordinateChainSet =
      (P 0 ⁻¹' Icc 0 1) ∩ ((P 1 ⁻¹' Ici 0) ∩
        (((P 1 - P 0) ⁻¹' Iic 0) ∩ ((P 2 ⁻¹' Ici 0) ∩ ((P 2 - P 1) ⁻¹' Iic 0)))) := by
    ext x
    simp [coordinateChainSet_mem, P, and_assoc]
  rw [he]
  exact h0.inter (h1.inter (h10.inter (h2.inter h21)))

theorem unitChainSet_convex (σ : Equiv.Perm (Fin 3)) (o : Space) :
    Convex ℝ (unitChainSet σ o) := by
  let L : Space →ₗ[ℝ] Space := LinearMap.pi (fun r => LinearMap.proj (σ r))
  have he : unitChainSet σ o = (fun x => x + -o) ⁻¹' (L ⁻¹' coordinateChainSet) := by
    ext x
    change unitNormalize σ o x ∈ coordinateChainSet ↔ L (x + -o) ∈ coordinateChainSet
    have hp : unitNormalize σ o x = L (x + -o) := by
      funext r
      simp [unitNormalize_apply, L, sub_eq_add_neg]
    rw [hp]
  rw [he]
  exact (coordinateChainSet_convex.linear_preimage L).translate_preimage_left (-o)

theorem scaledChainSet_convex (σ : Equiv.Perm (Fin 3)) (o : Space) (h : ℝ) :
    Convex ℝ (scaledChainSet σ o h) :=
  (unitChainSet_convex σ o).smul_preimage h⁻¹

theorem chainVertex_mem_unitChainSet (σ : Equiv.Perm (Fin 3)) (o : Space) (a : Fin 4) :
    ChainGeometry.chainVertex σ o a ∈ unitChainSet σ o := by
  apply (coordinateChainSet_mem _).mpr
  simp only [unitNormalize_apply, ChainGeometry.chainVertex, Equiv.symm_apply_apply,
    add_sub_cancel_left]
  fin_cases a <;> norm_num

theorem vertex_mem_tetrahedron {N : ℕ} (hN : 0 < N) (t : Tet N) (a : Fin 4) :
    vertex t a ∈ tetrahedron t := by
  change (meshScale N)⁻¹ • (meshScale N • ChainGeometry.chainVertex t.2
    (cellOrigin t.1) a) ∈ unitChainSet t.2 (cellOrigin t.1)
  rw [smul_smul, inv_mul_cancel₀ (meshScale_pos N hN).ne', one_smul]
  exact chainVertex_mem_unitChainSet t.2 (cellOrigin t.1) a

theorem tetrahedron_segment_mem {N : ℕ} (t : Tet N) (x y : Space)
    (hx : x ∈ tetrahedron t) (hy : y ∈ tetrahedron t)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (fun j => (1 - s) * x j + s * y j) ∈ tetrahedron t := by
  exact scaledChainSet_convex t.2 (cellOrigin t.1) (meshScale N) hx hy
    (sub_nonneg.mpr hs.2) hs.1 (by ring)

theorem edge_segment_mem {N : ℕ} (hN : 0 < N) (t : Tet N) (a b : Fin 4)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (fun j => (1 - s) * vertex t a j + s * vertex t b j) ∈ tetrahedron t :=
  tetrahedron_segment_mem t _ _ (vertex_mem_tetrahedron hN t a)
    (vertex_mem_tetrahedron hN t b) s hs

end FreudenthalSVLean.MeshSegments
