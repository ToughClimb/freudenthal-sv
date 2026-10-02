import FreudenthalSVLean.InteriorFaceCoverage
import FreudenthalSVLean.VelocityH1Representation

/-!
# A fixed involution pairing the two oriented incidences of each interior face

For the assembly in manuscript Lemma `means`, each interior mesh face
has a unique second owner and omitted-vertex index. These are chosen
from geometry alone, before the weak input field. The resulting partner
map is an involution on all oriented mesh faces; boundary incidences are
fixed. Opposite weak fluxes and an eight-incidence support count follow
on every N>0. This count is local and independent of the number of faces.
-/

open scoped BigOperators
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.ActualVertexStarGraph
open FreudenthalSVLean.ActualFaceSupport
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.InteriorFaceCoverage
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.VelocityH1Representation
open FreudenthalSVLean.OrderedSharedFaceChart

noncomputable section

namespace FreudenthalSVLean.FacePartner

open Classical
set_option backward.isDefEq.respectTransparency false

abbrev FaceIndex (N : ℕ) := Tet N × Fin 4

structure Neighbor {N : ℕ} (t : Tet N) (r : Fin 4) where
  star : VertexStar (faceAnchor t r)
  index : Fin 4
  owner_ne : t ≠ star.val.1
  omitted_ne : index ≠ star.val.2
  shared : gridFace t r = gridFace star.val.1 index

def faceNeighbor {N : ℕ} (hN : 0 < N) (t : Tet N) (r : Fin 4)
    (ha : activeGridFace t r) : Neighbor t r :=
  let H := activeGridFace_has_star_neighbor hN t r ha
  let tb := Classical.choose H
  let Hs := Classical.choose_spec H
  let s := Classical.choose Hs
  let Hp := Classical.choose_spec Hs
  ⟨tb, s, Hp.1, Hp.2.1, Hp.2.2⟩

def partner {N : ℕ} (hN : 0 < N) (f : FaceIndex N) : FaceIndex N :=
  if ha : activeGridFace f.1 f.2 then
    ((faceNeighbor hN f.1 f.2 ha).star.val.1, (faceNeighbor hN f.1 f.2 ha).index)
  else f

theorem partner_of_active {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (ha : activeGridFace f.1 f.2) :
    partner hN f =
      ((faceNeighbor hN f.1 f.2 ha).star.val.1, (faceNeighbor hN f.1 f.2 ha).index) := by
  rw [partner, dif_pos ha]

theorem partner_of_inactive {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (ha : ¬ activeGridFace f.1 f.2) : partner hN f = f := by
  rw [partner, dif_neg ha]

theorem partner_shared {N : ℕ} (hN : 0 < N) (f : FaceIndex N) :
    gridFace f.1 f.2 = gridFace (partner hN f).1 (partner hN f).2 := by
  by_cases ha : activeGridFace f.1 f.2
  · rw [partner_of_active hN f ha]
    exact (faceNeighbor hN f.1 f.2 ha).shared
  · rw [partner_of_inactive hN f ha]

theorem partner_owner_ne {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (ha : activeGridFace f.1 f.2) : f.1 ≠ (partner hN f).1 := by
  rw [partner_of_active hN f ha]
  exact (faceNeighbor hN f.1 f.2 ha).owner_ne

theorem partner_active {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (ha : activeGridFace f.1 f.2) : activeGridFace (partner hN f).1 (partner hN f).2 := by
  rw [partner_of_active hN f ha]
  let b := faceNeighbor hN f.1 f.2 ha
  exact shared_face_active hN b.star (anchoredOwner f.1 f.2) b.index f.2 b.omitted_ne
    (anchoredOwner_omitted_ne f.1 f.2) b.owner_ne.symm b.shared.symm

theorem partner_involutive {N : ℕ} (hN : 0 < N) : Function.Involutive (partner hN) := by
  intro f
  by_cases ha : activeGridFace f.1 f.2
  · have hb := partner_active hN f ha
    have hu := other_owner_unique hN (partner hN f).1 (partner hN f).2 hb
      (partner hN (partner hN f)).1 f.1 (partner hN (partner hN f)).2 f.2
      (partner_owner_ne hN (partner hN f) hb) (partner_owner_ne hN f ha).symm
      (partner_shared hN (partner hN f)) (partner_shared hN f).symm
    exact Prod.ext hu.1 hu.2
  · rw [partner_of_inactive hN f ha, partner_of_inactive hN f ha]

def partnerEquiv {N : ℕ} (hN : 0 < N) : FaceIndex N ≃ FaceIndex N :=
  Function.Involutive.toPerm (partner hN) (partner_involutive hN)

theorem meshFlux_partner {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (ha : activeGridFace f.1 f.2) (v : Fin 3 → smoothH1Space) :
    meshFluxLinear hN f.1 f.2 v =
      -meshFluxLinear hN (partner hN f).1 (partner hN f).2 v := by
  rw [partner_of_active hN f ha, meshFluxLinear_apply, meshFluxLinear_apply]
  let b := faceNeighbor hN f.1 f.2 ha
  exact actual_shared_weak_flux hN (anchoredOwner f.1 f.2) b.star f.2 b.index
    (anchoredOwner_omitted_ne f.1 f.2) b.omitted_ne b.owner_ne b.shared v

def elementIncidences {N : ℕ} (hN : 0 < N) (t : Tet N) : Finset (FaceIndex N) :=
  (Finset.univ.image (fun r : Fin 4 => (t, r))) ∪
    (Finset.univ.image (fun r : Fin 4 => partner hN (t, r)))

theorem elementIncidences_card {N : ℕ} (hN : 0 < N) (t : Tet N) :
    (elementIncidences hN t).card ≤ 8 := by
  calc
    _ ≤ (Finset.univ.image (fun r : Fin 4 => (t, r))).card +
        (Finset.univ.image (fun r : Fin 4 => partner hN (t, r))).card := Finset.card_union_le _ _
    _ ≤ (Finset.univ : Finset (Fin 4)).card + (Finset.univ : Finset (Fin 4)).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = 8 := by simp

theorem not_elementIncidences {N : ℕ} (hN : 0 < N) (t : Tet N) (f : FaceIndex N)
    (hf : f ∉ elementIncidences hN t) : t ≠ f.1 ∧ t ≠ (partner hN f).1 := by
  constructor
  · intro he
    apply hf
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨f.2, Finset.mem_univ _, by exact Prod.ext he rfl⟩
  · intro he
    apply hf
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(partner hN f).2, Finset.mem_univ _, ?_⟩
    have hp : (t, (partner hN f).2) = partner hN f := Prod.ext he rfl
    rw [hp, partner_involutive hN f]

end FreudenthalSVLean.FacePartner
