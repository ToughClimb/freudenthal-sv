import FreudenthalSVLean.QuarticBernstein
import FreudenthalSVLean.BernsteinPolynomial
import FreudenthalSVLean.ChainGeometry
import FreudenthalSVLean.PolynomialSkeletonTrace

/-!
# Polynomial semantics of the eleven quartic macro fields

This module connects the control points encoded in `QuarticBernstein.lean`
to actual normalized barycentric monomials, and derives their divergence
coefficients using the generic polynomial-calculus theorem.  The source is
the manuscript's quartic two-cube lemma and equations
`bernstein-divergence` and `quartic-mean-matrix`.

The scalar field in this module is `ℚ`.  Real analytic transport,
piecewise conformity, and volume integration are distinct obligations.
-/

open scoped BigOperators
open MvPolynomial
open FreudenthalSVLean.QuarticBernstein
open FreudenthalSVLean.BernsteinPolynomial

noncomputable section

namespace FreudenthalSVLean.QuarticPolynomial

/-- Natural multi-index associated with a nonnegative integer multi-index.
Negative input components are truncated, so membership in the tetrahedron
is checked separately before a Bernstein term is used. -/
def integerExponent (α : LocalVertex → ℤ) : LocalVertex →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (α i).toNat)

def cubicExponent (β : CubicMultiIndex) : LocalVertex →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (β i).val)

theorem scaledBarycentric_sum (t : TetIndex) (p : ScaledPoint) :
    ∑ i : LocalVertex, scaledBarycentric t p i = 4 := by
  simp [scaledBarycentric, Fin.sum_univ_succ]

theorem integerExponent_degree (t : TetIndex) (p : ScaledPoint)
    (hp : pointInTet t p = true) :
    (integerExponent (scaledBarycentric t p)).degree = 4 := by
  have hn : ∀ i, 0 ≤ scaledBarycentric t p i := by simpa [pointInTet] using hp
  rw [Finsupp.degree_eq_sum]
  change (∑ i : LocalVertex, (scaledBarycentric t p i).toNat) = 4
  have he : (∑ i : LocalVertex, ((scaledBarycentric t p i).toNat : ℤ)) = 4 := by
    simp_rw [Int.toNat_of_nonneg (hn _)]
    exact scaledBarycentric_sum t p
  exact_mod_cast he

theorem integerExponent_eq_raised_iff (α : LocalVertex → ℤ)
    (hα : ∀ j, 0 ≤ α j) (β : CubicMultiIndex) (i : LocalVertex) :
    integerExponent α = cubicExponent β + Finsupp.single i 1 ↔
      ∀ j, α j = raisedIndex β i j := by
  constructor
  · intro h j
    have hj := congrArg (fun e : LocalVertex →₀ ℕ => (e j : ℤ)) h
    simpa [integerExponent, cubicExponent, raisedIndex,
      Int.toNat_of_nonneg (hα j), Finsupp.single_apply, eq_comm] using hj
  · intro h
    ext j
    have hj := h j
    simp only [integerExponent, cubicExponent, Finsupp.add_apply,
      Finsupp.single_apply, Finsupp.coe_equivFunOnFinite_symm]
    rw [hj]
    by_cases hij : i = j
    · simp [raisedIndex, hij]
    · simp [raisedIndex, hij, Ne.symm hij]

/-- Actual vector polynomials in four independent barycentric variables,
built from the displayed physical control points. -/
def localVectorPolynomial (t : TetIndex) (w : FieldIndex)
    (component : SpatialIndex) : MvPolynomial LocalVertex ℚ :=
  ∑ r : TermIndex,
    if pointInTet t (macroTerms w r).point = true ∧
        (macroTerms w r).component = component then
      (macroTerms w r).coefficient • bernstein 4
        (integerExponent (scaledBarycentric t (macroTerms w r).point))
    else 0

theorem localVectorPolynomial_homogeneous (t : TetIndex) (w : FieldIndex)
    (component : SpatialIndex) : IsHomogeneous (localVectorPolynomial t w component) 4 := by
  unfold localVectorPolynomial
  apply IsHomogeneous.sum
  intro r _
  split_ifs with h
  · rw [smul_eq_C_mul]
    exact (bernstein_isHomogeneous 4 _ (integerExponent_degree t _ h.1)).C_mul _
  · exact isHomogeneous_zero _ ℚ 4

/-- The coefficients of the actual polynomial vector fields agree with the
original exact input objects used by the certificate. -/
theorem localVectorPolynomial_coefficient (t : TetIndex) (w : FieldIndex)
    (β : CubicMultiIndex) (i : LocalVertex) (component : SpatialIndex) :
    bernsteinCoefficient 4 (cubicExponent β + Finsupp.single i 1)
      (localVectorPolynomial t w component) =
        localVectorCoefficient t w (raisedIndex β i) component := by
  rw [localVectorPolynomial, bernsteinCoefficient_sum]
  unfold localVectorCoefficient
  apply Finset.sum_congr rfl
  intro r _
  by_cases hp : pointInTet t (macroTerms w r).point = true
  · have hnonneg : ∀ j, 0 ≤ scaledBarycentric t (macroTerms w r).point j := by
      simpa [pointInTet] using hp
    have heq := integerExponent_eq_raised_iff
      (scaledBarycentric t (macroTerms w r).point) hnonneg β i
    by_cases hc : (macroTerms w r).component = component
    · simp [hp, hc, bernsteinCoefficient_basis, heq, sameLocalIndex]
    · simp [hp, hc, bernsteinCoefficient, sameLocalIndex]
  · have hnoeq : ¬ ∀ j, scaledBarycentric t (macroTerms w r).point j =
        raisedIndex β i j := by
      intro heq
      apply hp
      unfold pointInTet
      simp only [decide_eq_true_eq]
      intro j
      rw [heq j]
      unfold raisedIndex
      positivity
    simp [hp, hnoeq, sameLocalIndex, bernsteinCoefficient]

/-- The divergence polynomial before barycentric substitution. -/
def localDivergencePolynomial (t : TetIndex) (w : FieldIndex) :
    MvPolynomial LocalVertex ℚ :=
  barycentricDivergence (barycentricGradient t) (localVectorPolynomial t w)

theorem localDivergencePolynomial_homogeneous (t : TetIndex) (w : FieldIndex) :
    IsHomogeneous (localDivergencePolynomial t w) 3 := by
  unfold localDivergencePolynomial barycentricDivergence
  apply IsHomogeneous.sum
  intro component _
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_pderiv 3 _ (localVectorPolynomial_homogeneous t w component) i).C_mul _

/-- The certificate's divergence coefficients are coefficients of the actual
polynomial derivative, by a generic theorem rather than a repeated finite
calculation. -/
theorem localDivergencePolynomial_coefficient (t : TetIndex) (w : FieldIndex)
    (β : CubicMultiIndex) :
    bernsteinCoefficient 3 (cubicExponent β) (localDivergencePolynomial t w) =
      divergenceCoefficient t w β := by
  rw [localDivergencePolynomial, bernsteinCoefficient_divergence]
  simp only [show 3 + 1 = 4 from rfl, localVectorPolynomial_coefficient]
  norm_num [divergenceCoefficient]

/-- All certified edge-carried coefficients vanish for the actual
barycentric divergence polynomial. -/
theorem localDivergencePolynomial_edge_coefficients_zero (t : TetIndex)
    (w : FieldIndex) (β : CubicMultiIndex) (hβ : IsEdgeCubicIndex β) :
    bernsteinCoefficient 3 (cubicExponent β) (localDivergencePolynomial t w) = 0 := by
  rw [localDivergencePolynomial_coefficient]
  exact displayedFields_all_edge_coefficients_zero t w β hβ

/-- No degree-three multi-index with at most two nonzero entries is omitted
when bounded indices are used in the exact certificate. -/
theorem localDivergencePolynomial_edge_monomial_coefficients_zero (t : TetIndex)
    (w : FieldIndex) (α : LocalVertex →₀ ℕ) (hd : α.degree = 3)
    (hs : α.support.card ≤ 2) : coeff α (localDivergencePolynomial t w) = 0 := by
  let β : CubicMultiIndex := fun i => ⟨α i, by
    have h := Finsupp.le_degree i α
    omega⟩
  have hβα : cubicExponent β = α := by
    ext i
    simp [cubicExponent, β]
  have hdegree : cubicDegree β = 3 := by
    simpa [cubicDegree, β, Finsupp.degree_eq_sum] using hd
  have hsupport : cubicSupportSize β = α.support.card := by
    unfold cubicSupportSize
    have hfun : (fun i : LocalVertex => if β i = 0 then 0 else 1) =
        (fun i : LocalVertex => if i ∈ α.support then 1 else 0) := by
      funext i
      by_cases h : α i = 0 <;> simp [β, h, Finsupp.mem_support_iff]
    rw [hfun]
    have hfilter : Finset.univ.filter (fun i : LocalVertex => i ∈ α.support) =
        α.support := by ext i; simp
    rw [← Finset.sum_filter]
    rw [hfilter]
    simp
  have hc := localDivergencePolynomial_edge_coefficients_zero t w β
    ⟨hdegree, hsupport ▸ hs⟩
  rw [hβα] at hc
  exact (div_eq_zero_iff.mp hc).resolve_right (normalization_ne_zero 3 α)

/-- Actual evaluation of every displayed divergence polynomial vanishes on
every edge, with an arbitrary real-algebraic edge parameter over `ℚ`. -/
theorem localDivergencePolynomial_eval_zero_on_edge (t : TetIndex)
    (w : FieldIndex) (s : Finset LocalVertex) (hs : s.card ≤ 2)
    (x : LocalVertex → ℚ) (hx : ∀ j, j ∉ s → x j = 0) :
    eval x (localDivergencePolynomial t w) = 0 := by
  apply PolynomialSkeletonTrace.eval_zero_on_edge _ 3
    (localDivergencePolynomial_homogeneous t w) s hs x hx
  exact localDivergencePolynomial_edge_monomial_coefficients_zero t w

end FreudenthalSVLean.QuarticPolynomial
