import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Index
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace LastLib.Book03RamificationTheory.Chapter04

noncomputable section

open scoped BigOperators Pointwise

/-!
Shared interfaces for Chapter 4.

The preceding chapters of Book 3 are drafted independently in this workspace.  The
integer filtration below is therefore the small, book-facing interface needed by
the subgroup and Herbrand statements.  The valuation-ring constructor at the end
of this file connects it to the canonical Book 2 congruence filtration.

DEPENDENCY_GUESS: If the reconciled Chapter02/Chapter03 drafts expose a canonical
integer lower-filtration structure, this local `Chapter04LowerFiltration` should
be replaced by that earlier interface; the subgroup and Herbrand declarations
depend only on the fields and monotonicity recorded here.
-/

universe u v

/-- A finite-indexed lower ramification filtration, with the `-1` level equal to
the ambient group and the nonnegative levels supplied by `lower`. -/
structure Chapter04LowerFiltration (G : Type u) [Group G] where
  lower : ℕ → Subgroup G
  descending : ∀ n : ℕ, lower (n + 1) ≤ lower n

@[ext]
theorem Chapter04LowerFiltration.ext {G : Type u} [Group G]
    {F F' : Chapter04LowerFiltration G}
    (h : ∀ n : ℕ, F.lower n = F'.lower n) : F = F' := by
  sorry

/-- The integer-indexed lower group associated to a nonnegative filtration.
All negative indices are sent to the `-1` level, as in the book. -/
def chapter04LowerGroup {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (i : ℤ) : Subgroup G :=
  if i < 0 then ⊤ else F.lower i.toNat

@[simp]
theorem chapter04LowerGroup_neg_one {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) :
    chapter04LowerGroup F (-1) = ⊤ := by
  sorry

theorem chapter04LowerGroup_of_nonnegative {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) {i : ℤ} (hi : 0 ≤ i) :
    chapter04LowerGroup F i = F.lower i.toNat := by
  sorry

theorem chapter04LowerGroup_succ_le {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (i : ℤ) (hi : -1 ≤ i) :
    chapter04LowerGroup F (i + 1) ≤ chapter04LowerGroup F i := by
  sorry

theorem chapter04LowerGroup_mono_anti {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) {i j : ℤ}
    (hi : -1 ≤ i) (hij : i ≤ j) :
    chapter04LowerGroup F j ≤ chapter04LowerGroup F i := by
  sorry

/-- A jump of the integer lower filtration. -/
def chapter04LowerBreak {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (i : ℤ) : Prop :=
  0 ≤ i ∧ chapter04LowerGroup F i ≠ chapter04LowerGroup F (i + 1)

/-- Restrict a lower filtration to a subgroup.  The resulting groups are
subgroups of the subgroup type, while `map subtype` recovers their ambient
intersection. -/
def chapter04SubgroupLowerFiltration {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) :
    Chapter04LowerFiltration H where
  lower n := (F.lower n).comap H.subtype
  descending := by
    intro n
    exact Subgroup.comap_mono (F.descending n)

theorem chapter04SubgroupLowerGroup_mem_iff {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (i : ℤ) (σ : H) :
    σ ∈ chapter04LowerGroup (chapter04SubgroupLowerFiltration F H) i ↔
      (σ : G) ∈ chapter04LowerGroup F i := by
  sorry

theorem chapter04SubgroupLowerGroup_map_eq_inf {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (i : ℤ) :
    (chapter04LowerGroup (chapter04SubgroupLowerFiltration F H) i).map H.subtype =
      H ⊓ chapter04LowerGroup F i := by
  sorry

theorem chapter04SubgroupLowerBreak_implies_lowerBreak {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (i : ℤ)
    (hbreak : chapter04LowerBreak (chapter04SubgroupLowerFiltration F H) i) :
    chapter04LowerBreak F i := by
  sorry

/-- A break can disappear after restriction: the trivial subgroup sees no
nontrivial lower jump. -/
theorem chapter04LowerBreak_can_disappear {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (i : ℤ)
    (hbreak : chapter04LowerBreak F i) :
    ∃ H : Subgroup G,
      ¬ chapter04LowerBreak (chapter04SubgroupLowerFiltration F H) i := by
  sorry

/-- The lower cardinality profile, useful for comparing conjugate filtrations. -/
def chapter04LowerCardinalityProfile {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) : ℕ → ℕ :=
  fun n => Nat.card (F.lower n)

def chapter04SubgroupLowerCardinalityProfile {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) : ℕ → ℕ :=
  fun n => Nat.card ((F.lower n).comap H.subtype)

def chapter04ConjugateSubgroup {G : Type u} [Group G]
    (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

theorem chapter04_conjugate_subgroups_have_identical_lower_cardinality_profile
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (g : G)
    (hconj : ∀ n : ℕ,
      (F.lower n).map (MulAut.conj g).toMonoidHom = F.lower n) :
    chapter04SubgroupLowerCardinalityProfile F
        (chapter04ConjugateSubgroup H g) =
      chapter04SubgroupLowerCardinalityProfile F H := by
  sorry

/-- Conjugation transports a filtration by a group automorphism. -/
def chapter04ConjugateLowerFiltration {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (g : G) :
    Chapter04LowerFiltration G where
  lower n := (F.lower n).map (MulAut.conj g).toMonoidHom
  descending := by
    intro n
    exact Subgroup.map_mono (F.descending n)

theorem chapter04ConjugateLowerCardinalityProfile_eq
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (g : G) :
    chapter04LowerCardinalityProfile (chapter04ConjugateLowerFiltration F g) =
      chapter04LowerCardinalityProfile F := by
  sorry

theorem chapter04ConjugateLowerBreak_iff
    {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (g : G) (i : ℤ) :
    chapter04LowerBreak (chapter04ConjugateLowerFiltration F g) i ↔
      chapter04LowerBreak F i := by
  sorry

/-- The real lower-index convention from §4.3: ceiling on nonnegative
indices, and the `-1` group on the negative interval. -/
def chapter04RealLowerGroup {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (u : ℝ) : Subgroup G :=
  if u < 0 then ⊤ else F.lower (Int.ceil u).toNat

theorem chapter04RealLowerGroup_zero {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) :
    chapter04RealLowerGroup F 0 = F.lower 0 := by
  sorry

theorem chapter04RealLowerGroup_neg {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) {u : ℝ}
    (hu : -1 ≤ u) (hu0 : u < 0) :
    chapter04RealLowerGroup F u = ⊤ := by
  sorry

theorem chapter04RealLowerGroup_on_right_closed_unit_interval
    {G : Type u} [Group G] (F : Chapter04LowerFiltration G) (m : ℕ)
    {x : ℝ} (hm : (m : ℝ) < x) (hm' : x ≤ (m + 1 : ℕ)) :
    chapter04RealLowerGroup F x = F.lower (m + 1) := by
  sorry

/-- The alternative floor convention, recorded so endpoint choices are
explicit rather than silently mixed. -/
def chapter04FloorRealLowerGroup {G : Type u} [Group G]
    (F : Chapter04LowerFiltration G) (u : ℝ) : Subgroup G :=
  if u < 0 then ⊤ else F.lower (Int.floor u).toNat

theorem chapter04FloorRealLowerGroup_on_left_closed_unit_interval
    {G : Type u} [Group G] (F : Chapter04LowerFiltration G) (m : ℕ)
    {x : ℝ} (hm : (m : ℝ) ≤ x) (hm' : x < (m + 1 : ℕ)) :
    chapter04FloorRealLowerGroup F x = F.lower m := by
  sorry

theorem chapter04RealLowerGroup_at_integer
    {G : Type u} [Group G] (F : Chapter04LowerFiltration G) (m : ℕ) :
    chapter04RealLowerGroup F m = F.lower m := by
  sorry

/-- The reciprocal index appearing in Herbrand's integral. -/
def chapter04HerbrandIntegrand
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (u : ℝ) : ℝ :=
  ((chapter04RealLowerGroup F u).relIndex (F.lower 0) : ℝ)⁻¹

/-- The Herbrand function on all real indices, with the identity extension on
negative indices.  Its ramification-theoretic domain is `[-1, ∞)`. -/
def chapter04HerbrandFunction
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (u : ℝ) : ℝ :=
  if 0 ≤ u then
    ∫ t in (0 : ℝ)..u, chapter04HerbrandIntegrand F t
  else u

theorem chapter04HerbrandFunction_of_nonpositive
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {u : ℝ} (hu : u ≤ 0) :
    chapter04HerbrandFunction F u = u := by
  sorry

theorem chapter04HerbrandFunction_zero
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    chapter04HerbrandFunction F 0 = 0 := by
  sorry

/-- The book's inverse notation, defined after the homeomorphism theorem. -/
noncomputable def chapter04HerbrandInverse
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) : ℝ → ℝ :=
  Function.invFun (chapter04HerbrandFunction F)

/-- A piecewise-linear value used for the closed formula in §4.4. -/
def chapter04HerbrandPiecewiseValue
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (m : ℕ) (u : ℝ) : ℝ :=
  (1 / (Nat.card (F.lower 0) : ℝ)) *
    (Finset.sum (Finset.Icc 1 m) (fun j => (Nat.card (F.lower j) : ℝ)) +
      (u - m) * Nat.card (F.lower (m + 1)))

def chapter04HerbrandSlope
    {G : Type u} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (m : ℕ) : ℝ :=
  (Nat.card (F.lower (m + 1)) : ℝ) / Nat.card (F.lower 0)

/-- The valuation-ring realization of the lower filtration.  Book 2's group
`n` is the congruence modulo the `n`th maximal-ideal power, hence it is the
`(n + 1)`st lower group in the convention of this chapter. -/
def chapter04ValuationLowerFiltration
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    Chapter04LowerFiltration
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A) where
  lower n :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup K A (n + 1)
  descending := by
    intro n
    sorry

theorem chapter04ValuationLowerFiltration_zero_eq_inertia
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    (chapter04ValuationLowerFiltration K A).lower 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup K A := by
  sorry

/-- The same valuation filtration transported into the ambient Galois group.
When the chosen valuation branch is unique, the decomposition subgroup is all
of `Gal(L / K)`, so this is exactly the source notation `Gᵢ`. -/
def chapter04GaloisLowerFiltration
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) : Chapter04LowerFiltration (Gal(L / K)) where
  lower n :=
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
      K A (n + 1)).map
      (Subgroup.subtype
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
          K A))
  descending := by
    intro n
    sorry

theorem chapter04GaloisLowerFiltration_zero_eq_inertia
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    (chapter04GaloisLowerFiltration K A).lower 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG K A := by
  sorry

/-- A branch preserved by every Galois automorphism has full decomposition
group, the field-theoretic hypothesis under which the ambient filtration really
has `G = Gal(L / K)` at level `-1`. -/
theorem chapter04_decomposition_group_eq_top_of_branch_preserved
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
    (hA : ∀ σ : Gal(L / K), σ • A = A) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K A = ⊤ := by
  sorry

theorem chapter04ValuationLowerFiltration_neg_one_eq_top
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    chapter04LowerGroup (chapter04ValuationLowerFiltration K A) (-1) = ⊤ := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter04
