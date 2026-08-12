import LastLib.Book03RamificationTheory.Chapter02.Section05ActionOnFinitePrecisionAndUnits
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

namespace LastLib.Book03RamificationTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

universe u

/-! ## 2.6. Breaks and the shape of a filtration -/

/-- The set of lower breaks of a finite lower filtration. -/
def chapter02LowerBreakSet
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) : Set ℕ :=
  {n | chapter02LowerBreak F n}

/-- A finite filtration has finitely many lower breaks. -/
theorem chapter02_lower_breaks_finite
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    (chapter02LowerBreakSet F).Finite := by
  sorry

/-- The break at zero is exactly the nontrivial tame layer. -/
theorem chapter02_lower_break_zero_iff_tame_layer_nontrivial
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    chapter02LowerBreak F 0 ↔ Nontrivial (chapter02TameLayer F) := by
  sorry

/-- Positive breaks occur in the wild part of the filtration. -/
theorem chapter02_positive_lower_break_is_wild
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) {n : ℕ}
    (hn : 1 ≤ n) (hbreak : chapter02LowerBreak F n) :
    F.group n ≤ chapter02WildGroup F := by
  sorry

/-- The exact lower levels occupied by an inertial element. -/
theorem chapter02_inertial_membership_range
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (σ : G) (hσ : σ ≠ 1)
    (hI : σ ∈ F.group 0)
    (d : ℕ) (hd : F.displacement σ = (d : WithTop ℤ)) :
    ∀ n : ℕ, σ ∈ F.group n ↔ n < d := by
  sorry

/-- The filtration and displacement determine one another. -/
theorem chapter02_same_filtration_same_displacement
    {G : Type u} [Group G] [Finite G]
    (F F' : Chapter02LowerFiltration G)
    (hgroup : ∀ n : ℕ, F.group n = F'.group n) :
    ∀ σ : G, F.displacement σ = F'.displacement σ := by
  sorry

theorem chapter02_same_displacement_same_filtration
    {G : Type u} [Group G] [Finite G]
    (F F' : Chapter02LowerFiltration G)
    (hdisp : ∀ σ : G, F.displacement σ = F'.displacement σ) :
    ∀ n : ℕ, F.group n = F'.group n := by
  sorry

/-- The finite list of lower levels at which a nonidentity element is visible. -/
def chapter02VisibleLowerLevels
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (N : ℕ) (σ : G) : Finset ℕ :=
  by
    classical
    exact (Finset.range N).filter (fun n => σ ≠ 1 ∧ σ ∈ F.group n)

theorem chapter02_visible_lower_levels_card_eq_displacement
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (σ : G) (hσ : σ ≠ 1)
    (d N : ℕ) (hd : F.displacement σ = (d : WithTop ℤ))
    (hN : d ≤ N) :
    (chapter02VisibleLowerLevels F N σ).card = d := by
  sorry

/--
The elementary double-counting identity behind Hilbert's different formula:
the sum of the nonidentity lower-group sizes equals the sum of the visible
lower levels of the nonidentity automorphisms.
-/
theorem chapter02_lower_cardinality_sum_eq_visible_depth_sum
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → F.group n = ⊥) :
    (Finset.sum (Finset.range N) (fun n => Nat.card (F.group n) - 1)) =
      ∑ σ : G, (chapter02VisibleLowerLevels F N σ).card := by
  sorry

/-- A profile records equal inertia degree but a possible mismatch of breaks. -/
def chapter02SameDegreeDifferentDepth
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (F : Chapter02LowerFiltration G)
    (F' : Chapter02LowerFiltration H) : Prop :=
  F.group 0 = ⊤ ∧ F'.group 0 = ⊤ ∧
    IsCyclic G ∧ IsCyclic H ∧ Nat.card G = Nat.card H ∧
    ∃ n : ℕ, chapter02LowerBreak F n ∧
      ¬chapter02LowerBreak F' n

/- The preceding predicate is intentionally not reduced to degree data: equal
   inertia order does not determine the lower-depth profile. -/

end

end LastLib.Book03RamificationTheory.Chapter02
