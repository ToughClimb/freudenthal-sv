import FreudenthalSVLean.QuarticSpatial
import FreudenthalSVLean.GridNodalSupport

/-!
# Global nodal-product realization of the quartic macro coefficients

For manuscript Lemma `macro` and its eleven displayed Bernstein fields,
each control point is realized by a fixed product of globally continuous
lattice-node hats.  The finite identity below identifies that product on
all twelve actual tetrahedra with the corresponding normalized Bernstein
monomial, including zero on every nonowner.  After scalar extension and
affine barycentric substitution, the identity concerns actual spatial
polynomials.  Thus conformity is obtained from one global function,
rather than assumed from the control-point labels.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.ChainMeasureTransport
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.QuarticPolynomial
open FreudenthalSVLean.BernsteinPolynomial
open FreudenthalSVLean.GridNodalSupport

noncomputable section

namespace FreudenthalSVLean.QuarticNodalRealization

def integerCorner (t : TetIndex) : SpatialIndex → ℤ :=
  fun j => if j = 0 ∧ 6 ≤ t.val then 1 else 0

def referenceNode (t : TetIndex) (a : LocalVertex) : ScaledPoint := fun j =>
  integerCorner t j + ∑ r : SpatialIndex,
    if r.val < a.val ∧ tetPermutation t r = j then 1 else 0

/-- A fixed owner, chosen from the actual displayed control point. -/
def hostTet : FieldIndex → TermIndex → TetIndex :=
  ![![0, 0, 1], ![0, 0, 1], ![0, 0, 2], ![0, 2, 3],
    ![1, 1, 4], ![6, 6, 7], ![6, 6, 8], ![0, 0, 8],
    ![0, 6, 8], ![6, 7, 10], ![1, 1, 10]]

theorem host_valid : ∀ (w : FieldIndex) (r : TermIndex),
    pointInTet (hostTet w r) (macroTerms w r).point = true := by
  decide +kernel

def hostExponent (w : FieldIndex) (r : TermIndex) : LocalVertex →₀ ℕ :=
  integerExponent (scaledBarycentric (hostTet w r) (macroTerms w r).point)

theorem host_degree (w : FieldIndex) (r : TermIndex) : (hostExponent w r).degree = 4 :=
  integerExponent_degree _ _ (host_valid w r)

def nodeVariable (t : TetIndex) (n : ScaledPoint) : MvPolynomial LocalVertex ℚ :=
  ∑ a : LocalVertex, if referenceNode t a = n then X a else 0

def localNodalProduct (t : TetIndex) (w : FieldIndex) (r : TermIndex) :
    MvPolynomial LocalVertex ℚ :=
  C (normalization 4 (hostExponent w r)) *
    ∏ a : LocalVertex, nodeVariable t (referenceNode (hostTet w r) a) ^ hostExponent w r a

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Finite geometric identification: a containing tetrahedron permutes
the positive-exponent physical vertices; a nonowner misses at least one
such vertex.  Only integer nodes and natural exponents are compared. -/
theorem local_node_certificate : ∀ (t : TetIndex) (w : FieldIndex) (r : TermIndex),
    if pointInTet t (macroTerms w r).point = true then
      ∃ p : LocalVertex → LocalVertex, Function.Bijective p ∧
        (∀ a, 0 < (scaledBarycentric (hostTet w r) (macroTerms w r).point a).toNat →
          referenceNode t (p a) = referenceNode (hostTet w r) a) ∧
        (∀ a, (scaledBarycentric t (macroTerms w r).point (p a)).toNat =
          (scaledBarycentric (hostTet w r) (macroTerms w r).point a).toNat)
    else ∃ a, 0 < (scaledBarycentric (hostTet w r) (macroTerms w r).point a).toNat ∧
      ∀ b, referenceNode t b ≠ referenceNode (hostTet w r) a := by
  decide +kernel

theorem referenceNode_injective (t : TetIndex) : Function.Injective (referenceNode t) := by
  have h : ∀ t : TetIndex, Function.Injective (referenceNode t) := by decide +kernel
  exact h t

/-- Integer coordinates of every reference vertex lie in the rectangle. -/
theorem reference_node_bounds : ∀ (t : TetIndex) (a : LocalVertex) (j : SpatialIndex),
    0 ≤ referenceNode t a j ∧ referenceNode t a j ≤ (if j = 0 then 2 else 1) := by
  decide +kernel

theorem reference_corner_bounds : ∀ (t : TetIndex) (j : SpatialIndex),
    0 ≤ integerCorner t j ∧ integerCorner t j < (if j = 0 then 2 else 1) := by
  decide +kernel

/-- The two integer cube origins and six actual coordinate orders identify
all twelve reference tetrahedra without ambiguity. -/
theorem reference_label_injective : Function.Injective (fun t : TetIndex =>
    (integerCorner t, tetPermutation t)) := by
  decide +kernel

theorem nodeVariable_eq_X (t : TetIndex) (b : LocalVertex) :
    nodeVariable t (referenceNode t b) = X b := by
  classical
  simp only [nodeVariable, (referenceNode_injective t).eq_iff]
  simp

theorem nodeVariable_eq_zero (t : TetIndex) (n : ScaledPoint)
    (hn : ∀ b, referenceNode t b ≠ n) : nodeVariable t n = 0 := by
  simp [nodeVariable, hn]

set_option maxHeartbeats 2000000 in
/-- Exact polynomial identity follows from the node certificate and the
generic monomial product formula; no polynomial equality oracle is used. -/
theorem local_product_identity (t : TetIndex) (w : FieldIndex) (r : TermIndex) :
    localNodalProduct t w r =
      if pointInTet t (macroTerms w r).point = true then
        bernstein 4 (integerExponent (scaledBarycentric t (macroTerms w r).point)) else 0 := by
  classical
  have hc := local_node_certificate t w r
  by_cases hp : pointInTet t (macroTerms w r).point = true
  · simp only [hp, if_true] at hc ⊢
    obtain ⟨p, hbij, hn, he⟩ := hc
    let e : LocalVertex ≃ LocalVertex := Equiv.ofBijective p hbij
    let β := integerExponent (scaledBarycentric t (macroTerms w r).point)
    have hα : ∀ a, β (e a) = hostExponent w r a := by
      intro a
      exact he a
    have hprod : (∏ a : LocalVertex,
        nodeVariable t (referenceNode (hostTet w r) a) ^ hostExponent w r a) =
        ∏ b : LocalVertex, (X b : MvPolynomial LocalVertex ℚ) ^ β b := by
      calc
        _ = ∏ a : LocalVertex, (X (e a) : MvPolynomial LocalVertex ℚ) ^ β (e a) := by
          apply Finset.prod_congr rfl
          intro a _
          rw [hα a]
          by_cases hz : hostExponent w r a = 0
          · simp [hz]
          · have hpos : 0 < (scaledBarycentric (hostTet w r) (macroTerms w r).point a).toNat :=
              Nat.pos_of_ne_zero hz
            rw [← hn a hpos, nodeVariable_eq_X]
            rfl
        _ = _ := e.prod_comp (fun b => (X b : MvPolynomial LocalVertex ℚ) ^ β b)
    have hfactor : factorialProduct (R := ℚ) (hostExponent w r) = factorialProduct β := by
      unfold factorialProduct
      calc
        _ = ∏ a : LocalVertex, (Nat.factorial (β (e a)) : ℚ) := by simp only [hα]
        _ = _ := e.prod_comp (fun b => (Nat.factorial (β b) : ℚ))
    unfold localNodalProduct bernstein
    rw [hprod, monomial_eq, β.prod_fintype _ (fun _ => pow_zero _)]
    simp only [normalization, hfactor, β]
  · simp only [hp] at hc
    obtain ⟨a, ha, hn⟩ := hc
    unfold localNodalProduct
    have hz : (∏ b : LocalVertex,
        nodeVariable t (referenceNode (hostTet w r) b) ^ hostExponent w r b) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      rw [nodeVariable_eq_zero t _ hn]
      exact zero_pow (Nat.ne_of_gt ha)
    rw [hz, mul_zero]
    simp [hp]

theorem integerCorner_cast (t : TetIndex) :
    intPoint (integerCorner t) = QuarticSpatial.realCellCorner t := by
  funext j
  simp only [intPoint, integerCorner, QuarticSpatial.realCellCorner,
    QuarticSpatial.cellCorner, scaledCellCorner]
  split_ifs <;> norm_num

theorem referenceNode_cast (t : TetIndex) (a : LocalVertex) :
    intPoint (referenceNode t a) = ChainGeometry.chainVertex (QuarticSpatial.tetEquiv t)
      (QuarticSpatial.realCellCorner t) a := by
  funext j
  have hs : (∑ r : SpatialIndex, if r.val < a.val ∧ tetPermutation t r = j then (1 : ℤ) else 0) =
      if ((QuarticSpatial.tetEquiv t).symm j).val < a.val then 1 else 0 := by
    rw [Finset.sum_eq_single ((QuarticSpatial.tetEquiv t).symm j)]
    · have he : tetPermutation t ((QuarticSpatial.tetEquiv t).symm j) = j :=
        (QuarticSpatial.tetEquiv t).apply_symm_apply j
      simp [he]
    · intro r _ hr
      have he : tetPermutation t r ≠ j := by
        intro he
        exact hr ((QuarticSpatial.tetEquiv t).injective (he.trans
          ((QuarticSpatial.tetEquiv t).apply_symm_apply j).symm))
      simp [he]
    · simp
  change (((integerCorner t j + ∑ r : SpatialIndex,
    if r.val < a.val ∧ tetPermutation t r = j then (1 : ℤ) else 0) : ℤ) : ℝ) = _
  rw [Int.cast_add, hs]
  have hc := congrFun (integerCorner_cast t) j
  simp only [intPoint] at hc
  rw [hc]
  simp only [ChainGeometry.chainVertex]
  split_ifs <;> norm_num

theorem intPoint_injective : Function.Injective intPoint := by
  intro n m he
  funext j
  have hj := congrFun he j
  change (n j : ℝ) = (m j : ℝ) at hj
  exact_mod_cast hj

theorem nodeVariable_spatial (t : TetIndex) (n : ScaledPoint) :
    eval₂Hom C (ChainGeometry.barycentric (QuarticSpatial.tetEquiv t)
      (QuarticSpatial.realCellCorner t)) (map (Rat.castHom ℝ) (nodeVariable t n)) =
      nodalPolynomial (QuarticSpatial.tetEquiv t) (integerCorner t) n := by
  simp only [nodeVariable, map_sum, nodalPolynomial]
  apply Finset.sum_congr rfl
  intro a _
  have he : referenceNode t a = n ↔ intPoint n =
      ChainGeometry.chainVertex (QuarticSpatial.tetEquiv t) (intPoint (integerCorner t)) a := by
    rw [integerCorner_cast, ← referenceNode_cast]
    exact (intPoint_injective.eq_iff).symm.trans eq_comm
  by_cases ha : referenceNode t a = n
  · simp [ha, he.mp ha, integerCorner_cast]
  · have hn : ¬ intPoint n = ChainGeometry.chainVertex (QuarticSpatial.tetEquiv t)
        (intPoint (integerCorner t)) a := fun h => ha (he.mpr h)
    simp [ha, hn]

def nodalProduct (w : FieldIndex) (r : TermIndex) (σ : Equiv.Perm SpatialIndex)
    (c : ScaledPoint) : MvPolynomial SpatialIndex ℝ :=
  C ((normalization (R := ℚ) 4 (hostExponent w r) : ℚ) : ℝ) *
    ∏ a : LocalVertex, nodalPolynomial σ c (referenceNode (hostTet w r) a) ^ hostExponent w r a

theorem nodalProduct_spatial (t : TetIndex) (w : FieldIndex) (r : TermIndex) :
    nodalProduct w r (QuarticSpatial.tetEquiv t) (integerCorner t) =
      eval₂Hom C (ChainGeometry.barycentric (QuarticSpatial.tetEquiv t)
        (QuarticSpatial.realCellCorner t)) (map (Rat.castHom ℝ) (localNodalProduct t w r)) := by
  simp only [localNodalProduct, map_mul, map_C, map_prod, map_pow,
    eval₂Hom_C, nodeVariable_spatial, nodalProduct]
  rfl

def globalProduct (w : FieldIndex) (r : TermIndex) (x : Space) : ℝ :=
  ((normalization (R := ℚ) 4 (hostExponent w r) : ℚ) : ℝ) *
    ∏ a : LocalVertex, GridNodal.nodal (intPoint (referenceNode (hostTet w r) a)) x ^ hostExponent w r a

theorem nodalProduct_eval (w : FieldIndex) (r : TermIndex) (σ : Equiv.Perm SpatialIndex)
    (c : ScaledPoint) (x : Space) (hx : x ∈ unitChainSet σ (intPoint c)) :
    eval x (nodalProduct w r σ c) = globalProduct w r x := by
  simp only [nodalProduct, map_mul, eval_C, map_prod, map_pow,
    nodalPolynomial_eval σ c _ x hx, globalProduct]

end FreudenthalSVLean.QuarticNodalRealization
