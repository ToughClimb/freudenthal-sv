import FreudenthalSVLean.VertexStarTypes
import FreudenthalSVLean.ConformingSkeletonBubble

/-!
# Geometric symmetries of the arbitrary-mesh vertex-star model

For manuscript Lemma `vertex-coverage`, the boundary-word classification
must describe the actual local geometry and active edges, not just its
cardinality.  Coordinates relative to the central vertex are prefix-mask
differences.  Relabeling coordinates permutes these differences; reversing
the chain and its marked position negates them.  The active-edge condition
is precisely nonzero displacement in each physical boundary coordinate.
-/

open FreudenthalSVLean.ChainGeometry
open FreudenthalSVLean.FreudenthalMesh
open FreudenthalSVLean.VertexStarCoverage
open FreudenthalSVLean.VertexStarTypes
open FreudenthalSVLean.MeshCoverage

noncomputable section

namespace FreudenthalSVLean.VertexStarSymmetry

def relativeVertex (s : State) (a : Vertex) (j : Coordinate) : ℤ :=
  (prefixMask (s.1, a) j : ℤ) - (prefixMask s j : ℤ)

def relabelState (π : Equiv.Perm Coordinate) (s : State) : State :=
  (s.1.trans π, s.2)

def relabelTags (π : Equiv.Perm Coordinate) (b : Coordinate → Fin 3) :
    Coordinate → Fin 3 := fun j => b (π.symm j)

theorem relabel_prefix (π : Equiv.Perm Coordinate) (s : State) (j : Coordinate) :
    prefixMask (relabelState π s) j = prefixMask s (π.symm j) := rfl

theorem relabel_relativeVertex (π : Equiv.Perm Coordinate) (s : State) (a : Vertex)
    (j : Coordinate) :
    relativeVertex (relabelState π s) a j = relativeVertex s a (π.symm j) := rfl

theorem relabel_admissible_iff (π : Equiv.Perm Coordinate)
    (b : Coordinate → Fin 3) (s : State) :
    tagAdmissible (relabelTags π b) (relabelState π s) ↔ tagAdmissible b s := by
  constructor
  · intro h j
    simpa only [relabelTags, relabel_prefix, Equiv.symm_apply_apply] using h (π j)
  · intro h j
    exact h (π.symm j)

def relabelEquiv (π : Equiv.Perm Coordinate) : State ≃ State where
  toFun := relabelState π
  invFun := relabelState π.symm
  left_inv s := by
    apply Prod.ext
    · ext i
      simp [relabelState]
    · rfl
  right_inv s := by
    apply Prod.ext
    · ext i
      simp [relabelState]
    · rfl

def reverseCoordinate : Equiv.Perm Coordinate where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

def reverseState (s : State) : State :=
  (reverseCoordinate.trans s.1, Fin.rev s.2)

def reverseTags (b : Coordinate → Fin 3) : Coordinate → Fin 3 :=
  fun j => Fin.rev (b j)

theorem reverse_prefix (s : State) (j : Coordinate) :
    prefixMask (reverseState s) j = 1 - prefixMask s j := by
  have hr := (s.1.symm j).isLt
  have ha := s.2.isLt
  change (if (Fin.rev (s.1.symm j)).val < (Fin.rev s.2).val then 1 else 0) = _
  unfold prefixMask
  simp only [Fin.val_rev]
  split_ifs <;> omega

theorem reverseState_involutive : Function.Involutive reverseState := by
  intro s
  apply Prod.ext
  · ext i
    simp [reverseState, reverseCoordinate]
  · exact Fin.rev_rev _

def reverseEquiv : State ≃ State :=
  Function.Involutive.toPerm reverseState reverseState_involutive

theorem reverse_relativeVertex (s : State) (a : Vertex) (j : Coordinate) :
    relativeVertex (reverseState s) (Fin.rev a) j = -relativeVertex s a j := by
  have hp := prefix_le_one s j
  have hq := prefix_le_one (s.1, a) j
  change (prefixMask (reverseState (s.1, a)) j : ℤ) -
    (prefixMask (reverseState s) j : ℤ) = _
  rw [reverse_prefix, reverse_prefix]
  unfold relativeVertex
  omega

theorem reverse_tag_zero (b : Coordinate → Fin 3) (j : Coordinate) :
    reverseTags b j = 0 ↔ b j = 2 := by
  generalize hb : b j = v
  fin_cases v <;> simp [reverseTags, hb]

theorem reverse_tag_upper (b : Coordinate → Fin 3) (j : Coordinate) :
    reverseTags b j = 2 ↔ b j = 0 := by
  generalize hb : b j = v
  fin_cases v <;> simp [reverseTags, hb]

theorem reverse_admissible_iff (b : Coordinate → Fin 3) (s : State) :
    tagAdmissible (reverseTags b) (reverseState s) ↔ tagAdmissible b s := by
  have hp (j) := prefix_le_one s j
  simp only [tagAdmissible, reverse_tag_zero, reverse_tag_upper, reverse_prefix]
  constructor
  · intro h j
    constructor
    · intro hz
      have he := (h j).2 hz
      have := hp j
      omega
    · intro hu
      have he := (h j).1 hu
      have := hp j
      omega
  · intro h j
    constructor
    · intro hu
      rw [(h j).2 hu]
    · intro hz
      rw [(h j).1 hz]

/-- An incident edge is active iff it moves in every coordinate in which
the central vertex lies on the physical boundary. -/
def activeDirection (b : Coordinate → Fin 3) (d : Coordinate → ℤ) : Prop :=
  ∀ j : Coordinate, b j ≠ 1 → d j ≠ 0

theorem relabel_active_iff (π : Equiv.Perm Coordinate) (b : Coordinate → Fin 3)
    (d : Coordinate → ℤ) :
    activeDirection (relabelTags π b) (fun j => d (π.symm j)) ↔ activeDirection b d := by
  constructor
  · intro h j
    simpa only [relabelTags, Equiv.symm_apply_apply] using h (π j)
  · intro h j
    exact h (π.symm j)

theorem reverse_active_iff (b : Coordinate → Fin 3) (d : Coordinate → ℤ) :
    activeDirection (reverseTags b) (-d) ↔ activeDirection b d := by
  have htag (j : Coordinate) : reverseTags b j ≠ 1 ↔ b j ≠ 1 := by
    generalize hb : b j = v
    fin_cases v <;> simp [reverseTags, hb]
  simp only [activeDirection, htag, Pi.neg_apply, neg_ne_zero]

/-- Each relative vertex is the actual integer displacement from the
marked grid vertex, including all boundary configurations. -/
theorem grid_displacement {N : ℕ} (n : GridVertex N) (ta : VertexStar n)
    (a : Vertex) (j : Coordinate) :
    ((gridVertexOfTet ta.val.1 a j).val : ℤ) - (n j).val =
      relativeVertex (ta.val.1.2, ta.val.2) a j := by
  have hn := star_cell_equation n ta j
  change (((ta.val.1.1 j).val + prefixMask (ta.val.1.2, a) j : ℕ) : ℤ) -
    ((n j).val : ℤ) = _
  simp only [Nat.cast_add]
  unfold relativeVertex
  rw [hn]
  push_cast
  ring

def integerGrid {N : ℕ} (n : GridVertex N) : Coordinate → ℤ :=
  fun j => (n j).val

/-- The tag-based condition is exactly the physical-boundary condition
used for the conforming nodal bubbles. -/
theorem activeDirection_iff_activePair {N : ℕ} (hN : 0 < N)
    (n m : GridVertex N) :
    activeDirection (boundaryTag n) (integerGrid m - integerGrid n) ↔
      ConformingSkeletonBubble.activePair N (integerGrid n) (integerGrid m) := by
  constructor
  · intro h j
    constructor
    · by_cases hn : (n j).val = 0
      · right
        have ht : boundaryTag n j ≠ 1 := by
          rw [(boundaryTag_zero_iff n j).mpr hn]
          decide
        have hd := h j ht
        simp only [Pi.sub_apply, integerGrid] at hd ⊢
        omega
      · left
        change ((n j).val : ℤ) ≠ 0
        exact_mod_cast hn
    · by_cases hn : (n j).val = N
      · right
        have ht : boundaryTag n j ≠ 1 := by
          rw [(boundaryTag_upper_iff hN n j).mpr hn]
          decide
        have hd := h j ht
        simp only [Pi.sub_apply, integerGrid] at hd ⊢
        omega
      · left
        change ((n j).val : ℤ) ≠ (N : ℤ)
        exact_mod_cast hn
  · intro h j ht
    by_cases hz : (n j).val = 0
    · have hm := (h j).1
      simp only [Pi.sub_apply, integerGrid] at hm ⊢
      omega
    · by_cases hu : (n j).val = N
      · have hm := (h j).2
        simp only [Pi.sub_apply, integerGrid] at hm ⊢
        omega
      · exact False.elim (ht (by simp [boundaryTag, hz, hu]))

def transformState (π : Equiv.Perm Coordinate) (flip : Bool) (s : State) : State :=
  if flip then reverseState (relabelState π s) else relabelState π s

def transformTags (π : Equiv.Perm Coordinate) (flip : Bool) (b : Coordinate → Fin 3) :
    Coordinate → Fin 3 :=
  if flip then reverseTags (relabelTags π b) else relabelTags π b

def transformVertex (flip : Bool) (a : Vertex) : Vertex := if flip then Fin.rev a else a

def transformDirection (π : Equiv.Perm Coordinate) (flip : Bool) (d : Coordinate → ℤ) :
    Coordinate → ℤ := if flip then -(fun j => d (π.symm j)) else fun j => d (π.symm j)

def transformEquiv (π : Equiv.Perm Coordinate) (flip : Bool) : State ≃ State :=
  if flip then (relabelEquiv π).trans reverseEquiv else relabelEquiv π

theorem transformEquiv_apply (π : Equiv.Perm Coordinate) (flip : Bool) (s : State) :
    transformEquiv π flip s = transformState π flip s := by
  cases flip <;> rfl

theorem transform_admissible_iff (π : Equiv.Perm Coordinate) (flip : Bool)
    (b : Coordinate → Fin 3) (s : State) :
    tagAdmissible (transformTags π flip b) (transformState π flip s) ↔
      tagAdmissible b s := by
  cases flip
  · exact relabel_admissible_iff π b s
  · exact (reverse_admissible_iff _ _).trans (relabel_admissible_iff π b s)

def transformAdmissibleEquiv (π : Equiv.Perm Coordinate) (flip : Bool)
    (b : Coordinate → Fin 3) :
    {s : State // tagAdmissible b s} ≃
      {s : State // tagAdmissible (transformTags π flip b) s} :=
  (transformEquiv π flip).subtypeEquiv (by
    intro s
    rw [transformEquiv_apply]
    exact (transform_admissible_iff π flip b s).symm)

theorem transform_relativeVertex (π : Equiv.Perm Coordinate) (flip : Bool) (s : State)
    (a : Vertex) :
    relativeVertex (transformState π flip s) (transformVertex flip a) =
      transformDirection π flip (relativeVertex s a) := by
  cases flip
  · rfl
  · funext j
    exact reverse_relativeVertex (relabelState π s) a j

theorem transform_active_iff (π : Equiv.Perm Coordinate) (flip : Bool)
    (b : Coordinate → Fin 3) (d : Coordinate → ℤ) :
    activeDirection (transformTags π flip b) (transformDirection π flip d) ↔
      activeDirection b d := by
  cases flip
  · exact relabel_active_iff π b d
  · exact (reverse_active_iff _ _).trans (relabel_active_iff π b d)

theorem tagTransform_eq_transformTags (b : Coordinate → Fin 3) (r : Fin 6) (flip : Bool) :
    tagTransform b r flip = transformTags (orderPerm r).symm flip b := by
  cases flip <;> rfl

/-- Fixing one coordinate symmetry of the boundary word gives a bijection
of all incident tetrahedra, with the vertex and active-edge transformation
specified by `transform_relativeVertex` and `transform_active_iff`. -/
theorem canonical_star_symmetry (b : Coordinate → Fin 3) :
    ∃ (c r : Fin 6) (flip : Bool),
      transformTags (orderPerm r).symm flip b = canonicalTags c ∧
      ∀ s : State,
        tagAdmissible (canonicalTags c) (transformState (orderPerm r).symm flip s) ↔
          tagAdmissible b s := by
  obtain ⟨c, r, flip, h⟩ := tag_words_covered b
  rw [tagTransform_eq_transformTags] at h
  exact ⟨c, r, flip, h, fun s => h ▸ transform_admissible_iff _ _ _ s⟩

end FreudenthalSVLean.VertexStarSymmetry
