import FreudenthalSVLean.MacroMeanTransfer

/-!
# Fixed finite cube clusters and their element routing graphs

For manuscript Lemma `routing`, a face-connected cluster of `L` cubes
has a connected element graph with precisely `6 L` vertices.  Graph edges
join tetrahedra in the same cube or in face-neighbor cubes.  Each admits
an actual quartic macro transfer whose support lies in the cluster's
one-cube face neighborhood.  Geometry and graph choices precede all mean
inputs.
-/

open SimpleGraph
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.MacroPatchAdjacency

noncomputable section

namespace FreudenthalSVLean.CubeClusterGraph

abbrev ClusterCell {N : ℕ} (C : Finset (Cell N)) := {c : Cell N // c ∈ C}
abbrev ClusterTet {N : ℕ} (C : Finset (Cell N)) := {t : Tet N // t.1 ∈ C}

def cubeGraph {N : ℕ} (C : Finset (Cell N)) : SimpleGraph (ClusterCell C) where
  Adj c d := FaceAdjacent c.val d.val
  symm := ⟨fun _ _ h => faceAdjacent_symm h⟩
  loopless := ⟨fun _ h => faceAdjacent_ne h rfl⟩

def elementGraph {N : ℕ} (C : Finset (Cell N)) : SimpleGraph (ClusterTet C) where
  Adj t u := t ≠ u ∧ (t.val.1 = u.val.1 ∨ FaceAdjacent t.val.1 u.val.1)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun he => Or.inl he.symm)
    (fun ha => Or.inr (faceAdjacent_symm ha))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def clusterTetEquiv {N : ℕ} (C : Finset (Cell N)) :
    ClusterTet C ≃ ClusterCell C × Equiv.Perm Coordinate where
  toFun t := (⟨t.val.1, t.property⟩, t.val.2)
  invFun c := ⟨(c.1.val, c.2), c.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem clusterTet_card {N : ℕ} (C : Finset (Cell N)) :
    Fintype.card (ClusterTet C) = 6 * C.card := by
  classical
  rw [Fintype.card_congr (clusterTetEquiv C), Fintype.card_prod,
    Fintype.card_coe, Fintype.card_perm, Fintype.card_fin]
  norm_num
  omega

def anchor {N : ℕ} (C : Finset (Cell N)) (c : ClusterCell C) : ClusterTet C :=
  ⟨(c.val, Equiv.refl _), c.property⟩

def anchorHom {N : ℕ} (C : Finset (Cell N)) : cubeGraph C →g elementGraph C where
  toFun := anchor C
  map_rel' {c d} h := by
    refine ⟨?_, Or.inr h⟩
    intro he
    exact faceAdjacent_ne h (congrArg (fun t : ClusterTet C => t.val.1) he)

theorem same_cube_reachable {N : ℕ} (C : Finset (Cell N)) (t u : ClusterTet C)
    (h : t.val.1 = u.val.1) : (elementGraph C).Reachable t u := by
  by_cases he : t = u
  · subst u; exact Reachable.rfl
  · exact (show (elementGraph C).Adj t u from ⟨he, Or.inl h⟩).reachable

/-- Face connectivity of the cubes implies connectivity of all their
actual tetrahedra, with no restriction on local coordinate orders. -/
theorem elementGraph_connected {N : ℕ} (C : Finset (Cell N))
    (hC : (cubeGraph C).Connected) : (elementGraph C).Connected := by
  let : Nonempty (ClusterTet C) := hC.nonempty.map (anchor C)
  refine ⟨?_⟩
  intro t u
  let c : ClusterCell C := ⟨t.val.1, t.property⟩
  let d : ClusterCell C := ⟨u.val.1, u.property⟩
  exact (same_cube_reachable C t (anchor C c) rfl).trans
    (((hC c d).map (anchorHom C)).trans (same_cube_reachable C (anchor C d) u rfl))

/-- Support neighborhood needed only for same-cube companion patches. -/
def nearCluster {N : ℕ} (C : Finset (Cell N)) (t : Tet N) : Prop :=
  ∃ c ∈ C, t.1 = c ∨ FaceAdjacent c t.1

structure PairPatch {N : ℕ} (t u : Tet N) where
  permutation : Equiv.Perm Coordinate
  origin : Coordinate → ℤ
  fits : PhysicalMacroFields.patchFits N permutation origin
  first : QuarticPatchCoverage.inPatch permutation origin t
  second : QuarticPatchCoverage.inPatch permutation origin u
  support : ∀ v : Tet N, QuarticPatchCoverage.inPatch permutation origin v →
    v.1 = t.1 ∨ FaceAdjacent t.1 v.1

def pairPatch {N : ℕ} (hN : 2 ≤ N) (t u : Tet N)
    (h : t.1 = u.1 ∨ FaceAdjacent t.1 u.1) : PairPatch t u := by
  have hp : Nonempty (PairPatch t u) := by
    obtain ⟨π, o, hf, ht, hu, hs⟩ := local_pair_patch hN t u h
    exact ⟨⟨π, o, hf, ht, hu, hs⟩⟩
  exact Classical.choice hp

/-- The patch depends only on the fixed graph edge. -/
def graphTransfer {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (t u : ClusterTet C) (h : (elementGraph C).Adj t u) : velocitySpace N 4 :=
  let p := pairPatch hN t.val u.val h.2
  MacroMeanTransfer.transfer (by omega) p.permutation p.origin p.fits
    t.val p.first u.val p.second

theorem graphTransfer_means {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (t u : ClusterTet C) (h : (elementGraph C).Adj t u) :
    MacroMeanTransfer.elementMeans (by omega) 4 (graphTransfer hN C t u h) =
      Pi.single t.val 1 - Pi.single u.val 1 := by
  exact MacroMeanTransfer.transfer_means _ _ _ _ _ _ _ _

theorem graphTransfer_support {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (t u : ClusterTet C) (h : (elementGraph C).Adj t u) (v : Tet N)
    (hv : ¬ nearCluster C v) : (graphTransfer hN C t u h).val v = 0 := by
  let p := pairPatch hN t.val u.val h.2
  apply MacroMeanTransfer.transfer_zero_off_patch
  intro hp
  exact hv ⟨t.val.1, t.property, p.support v hp⟩

theorem graphTransfer_zero_edges {N : ℕ} (hN : 2 ≤ N) (C : Finset (Cell N))
    (t u : ClusterTet C) (h : (elementGraph C).Adj t u) (v : Tet N)
    (a b : Fin 4) (s : ℝ) :
    MvPolynomial.eval (ChainGeometry.segmentPoint (vertex v a) (vertex v b) s)
      (divergence N (graphTransfer hN C t u h).val v) = 0 := by
  exact MacroMeanTransfer.transfer_zero_edges _ _ _ _ _ _ _ _ v a b s

theorem graphTransfer_uniform_energy : ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (hN : 2 ≤ N)
    (C : Finset (Cell N)) (t u : ClusterTet C) (h : (elementGraph C).Adj t u),
    velocityEnergy (graphTransfer hN C t u h).val ≤ A * ((meshScale N) ^ 3)⁻¹ := by
  obtain ⟨A, hA, hE⟩ := MacroMeanTransfer.transfer_uniform_energy
  refine ⟨A, hA, ?_⟩
  intro N hN C t u h
  exact hE _ _ _ _ _ _ _ _ _

end FreudenthalSVLean.CubeClusterGraph
