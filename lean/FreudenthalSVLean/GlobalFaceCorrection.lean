import FreudenthalSVLean.FacePartner
import FreudenthalSVLean.WeakFaceFluxCorrection
import FreudenthalSVLean.BoundedOverlapEnergy
import FreudenthalSVLean.StarMeanRouting

/-!
# Fixed linear global cubic correction of interior weak face fluxes

For manuscript Lemma `means`, summing one half of each oriented
interior-face correction gives a fixed linear map to the actual
homogeneous conforming cubic velocity space. The partner involution
and opposite actual weak fluxes show that its element divergence means
are precisely the sum of the interior face fluxes. Boundary faces are
omitted by a geometry-only condition. Actual two-owner polynomial
support gives at most eight oriented incidences on each element, and
therefore an N-independent global energy estimate by local weak-H1
residual energies. No continuous divergence inverse is assumed here.
-/

open scoped BigOperators
open Classical MvPolynomial MeasureTheory
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.ActualFaceConformity
open FreudenthalSVLean.InteriorFaceCoverage
open FreudenthalSVLean.FacePartner
open FreudenthalSVLean.WeakLinearFaceTrace
open FreudenthalSVLean.WeakFaceTrace
open FreudenthalSVLean.VelocityH1Representation
open FreudenthalSVLean.WeakFaceFluxCorrection
open FreudenthalSVLean.VelocityEnergy
open FreudenthalSVLean.BoundedOverlapEnergy
open FreudenthalSVLean.StarMeanRouting

noncomputable section

namespace FreudenthalSVLean.GlobalFaceCorrection

set_option backward.isDefEq.respectTransparency false

def orientedFluxLinear {N : ℕ} (hN : 0 < N) (f : FaceIndex N) :
    (Fin 3 → smoothH1Space) →ₗ[ℝ] ℝ :=
  if activeGridFace f.1 f.2 then (1 / 2 : ℝ) • meshFluxLinear hN f.1 f.2 else 0

theorem orientedFlux_partner {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (v : Fin 3 → smoothH1Space) :
    orientedFluxLinear hN (partner hN f) v = -orientedFluxLinear hN f v := by
  by_cases ha : activeGridFace f.1 f.2
  · simp only [orientedFluxLinear, if_pos ha, if_pos (partner_active hN f ha),
      LinearMap.smul_apply, smul_eq_mul]
    have he := meshFlux_partner hN f ha v
    linarith
  · rw [partner_of_inactive hN f ha]
    simp only [orientedFluxLinear, if_neg ha, LinearMap.zero_apply, neg_zero]

def localCorrectionLinear {N : ℕ} (hN : 0 < N) (f : FaceIndex N) :
    (Fin 3 → smoothH1Space) →ₗ[ℝ] BrokenVelocity N :=
  (correctionLinear f.1 f.2).comp (orientedFluxLinear hN f)

theorem localCorrection_inactive {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (ha : ¬ activeGridFace f.1 f.2) (v : Fin 3 → smoothH1Space) :
    localCorrectionLinear hN f v = 0 := by
  simp only [localCorrectionLinear, LinearMap.comp_apply, orientedFluxLinear, if_neg ha,
    LinearMap.zero_apply, map_zero]

theorem localCorrection_mem {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (v : Fin 3 → smoothH1Space) : localCorrectionLinear hN f v ∈ velocitySpace N 3 := by
  by_cases ha : activeGridFace f.1 f.2
  · let b := faceNeighbor hN f.1 f.2 ha
    exact faceCorrection_mem hN (anchoredOwner f.1 f.2) b.star f.2 b.index
      (anchoredOwner_omitted_ne f.1 f.2) b.omitted_ne b.owner_ne b.shared _
  · rw [localCorrection_inactive hN f ha v]
    exact (velocitySpace N 3).zero_mem

def globalCorrectionLinear {N : ℕ} (hN : 0 < N) :
    (Fin 3 → smoothH1Space) →ₗ[ℝ] velocitySpace N 3 :=
  (∑ f : FaceIndex N, localCorrectionLinear hN f).codRestrict _ (fun v => by
    simp only [LinearMap.sum_apply]
    exact (velocitySpace N 3).sum_mem (fun f _ => localCorrection_mem hN f v))

theorem globalCorrection_apply {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) :
    (globalCorrectionLinear hN v).val = ∑ f : FaceIndex N, localCorrectionLinear hN f v := by
  simp only [globalCorrectionLinear, LinearMap.codRestrict_apply, LinearMap.sum_apply]

theorem localCorrection_mean {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (v : Fin 3 → smoothH1Space) (t : Tet N) :
    tetIntegral hN t (divergence N (localCorrectionLinear hN f v) t) =
      (if f.1 = t then orientedFluxLinear hN f v else 0) -
        (if (partner hN f).1 = t then orientedFluxLinear hN f v else 0) := by
  by_cases ha : activeGridFace f.1 f.2
  · let b := faceNeighbor hN f.1 f.2 ha
    have hm := faceCorrection_means hN (anchoredOwner f.1 f.2) b.star f.2 b.index
      (anchoredOwner_omitted_ne f.1 f.2) b.omitted_ne b.owner_ne b.shared
      (orientedFluxLinear hN f v) t
    dsimp only [anchoredOwner] at hm
    change (∫ x in tetrahedron t, eval x (divergence N
      (faceCorrection f.1 f.2 (orientedFluxLinear hN f v)) t)) = _
    rw [hm, partner_of_active hN f ha]
    change (if t = f.1 then orientedFluxLinear hN f v else
      if t = b.star.val.1 then -orientedFluxLinear hN f v else 0) =
        (if f.1 = t then orientedFluxLinear hN f v else 0) -
          (if b.star.val.1 = t then orientedFluxLinear hN f v else 0)
    by_cases ht : f.1 = t
    · have hb : b.star.val.1 ≠ t := by rw [← ht]; exact b.owner_ne.symm
      simp only [if_pos ht, if_neg hb, if_pos ht.symm, sub_zero]
    · by_cases hb : b.star.val.1 = t
      · simp only [if_neg ht, if_neg (Ne.symm ht), if_pos hb, if_pos hb.symm, zero_sub]
      · simp only [if_neg ht, if_neg (Ne.symm ht), if_neg hb, if_neg (Ne.symm hb), sub_self]
  · rw [localCorrection_inactive hN f ha v]
    simp only [map_zero, Pi.zero_apply, orientedFluxLinear, if_neg ha, LinearMap.zero_apply,
      ite_self, sub_self]

theorem globalCorrection_means {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) (t : Tet N) :
    tetIntegral hN t (divergence N (globalCorrectionLinear hN v).val t) =
      ∑ r : Fin 4, if activeGridFace t r then meshFluxLinear hN t r v else 0 := by
  rw [globalCorrection_apply, map_sum]
  simp only [Finset.sum_apply, map_sum, localCorrection_mean, Finset.sum_sub_distrib]
  have he : (∑ f : FaceIndex N, if (partner hN f).1 = t then orientedFluxLinear hN f v else 0) =
      -(∑ f : FaceIndex N, if f.1 = t then orientedFluxLinear hN f v else 0) := by
    have hs := (partnerEquiv hN).sum_comp
      (fun f : FaceIndex N => if f.1 = t then orientedFluxLinear hN (partner hN f) v else 0)
    change (∑ f : FaceIndex N, if (partner hN f).1 = t then
      orientedFluxLinear hN (partner hN (partner hN f)) v else 0) =
        ∑ f : FaceIndex N, if f.1 = t then orientedFluxLinear hN (partner hN f) v else 0 at hs
    have hinv (f : FaceIndex N) : partner hN (partner hN f) = f := partner_involutive hN f
    simp only [hinv] at hs
    rw [hs, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro f _
    rw [orientedFlux_partner hN f v]
    split_ifs <;> simp only [neg_zero]
  rw [he, sub_neg_eq_add, Fintype.sum_prod_type]
  have hsum : (∑ u : Tet N, ∑ r : Fin 4,
      if u = t then orientedFluxLinear hN (u, r) v else 0) =
        ∑ r : Fin 4, orientedFluxLinear hN (t, r) v := by
    simp
  rw [hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases ha : activeGridFace t r
  · simp only [orientedFluxLinear, if_pos ha, LinearMap.smul_apply, smul_eq_mul]
    ring
  · simp only [orientedFluxLinear, if_neg ha, LinearMap.zero_apply, zero_add]

theorem localCorrection_zero_off_pair {N : ℕ} (hN : 0 < N) (f : FaceIndex N)
    (v : Fin 3 → smoothH1Space) (t : Tet N) (ht : t ≠ f.1) (hp : t ≠ (partner hN f).1) :
    localCorrectionLinear hN f v t = 0 := by
  by_cases ha : activeGridFace f.1 f.2
  · rw [partner_of_active hN f ha] at hp
    let b := faceNeighbor hN f.1 f.2 ha
    exact faceCorrection_zero_off_pair (anchoredOwner f.1 f.2) b.star f.2 b.index
      (anchoredOwner_omitted_ne f.1 f.2) b.owner_ne b.shared _ t ht hp
  · rw [localCorrection_inactive hN f ha v]
    rfl

theorem globalCorrection_overlap_energy {N : ℕ} (hN : 0 < N) (v : Fin 3 → smoothH1Space) :
    velocityEnergy (globalCorrectionLinear hN v).val ≤
      8 * ∑ f : FaceIndex N, velocityEnergy (localCorrectionLinear hN f v) := by
  rw [globalCorrection_apply]
  apply velocityEnergy_sum_overlap hN Finset.univ _ 8 (by norm_num)
  intro t
  refine ⟨elementIncidences hN t, Finset.subset_univ _, ?_, ?_⟩
  · exact_mod_cast elementIncidences_card hN t
  · intro f _ hf
    have ht := not_elementIncidences hN t f hf
    exact localCorrection_zero_off_pair hN f v t ht.1 ht.2

end FreudenthalSVLean.GlobalFaceCorrection
