import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open scoped BigOperators Pointwise

universe u v

/-!
Shared interfaces for Chapter 3.

The checkout does not yet contain the preceding Book 3 chapters.  The
displacement-filtration structure below is therefore a deliberately small
book-facing bridge: it records the lower-numbering shift and the membership
test used by every calculation in this chapter, without assuming any of the
calculations themselves.  The valuation-ring definitions are connected to
Book 2's canonical congruence groups.
-/

/- LOCAL_DEPENDENCY_GUESS: In the reconciled pass this structure should be
   replaced by the canonical lower-filtration interface from Book 3,
   Chapters 1--2.  Its only required fields are the displayed lower-group
   convention and the displacement membership equivalence. -/

/- The lower group attached to a chosen valuation branch.

The Book 2 congruence group at level `n` is the group `G_(n-1)` in the
source's convention, so the nonnegative branch uses `n + 1`; the `-1` group
is the full decomposition group. -/
def chapter03ValuationLowerGroup
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (i : ℤ) :
    Subgroup
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        F A) :=
  if i < 0 then ⊤ else
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
      F A (i.toNat + 1)

@[simp]
theorem chapter03ValuationLowerGroup_neg_one
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter03ValuationLowerGroup F A (-1) = ⊤ := by
  sorry

theorem chapter03ValuationLowerGroup_of_nonnegative
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) {i : ℤ} (hi : 0 ≤ i) :
    chapter03ValuationLowerGroup F A i =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
        F A (i.toNat + 1) := by
  sorry

theorem chapter03ValuationLowerGroup_mem_iff_of_nonnegative
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) {i : ℤ} (hi : 0 ≤ i)
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      F A) :
    σ ∈ chapter03ValuationLowerGroup F A i ↔
      σ ∈
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
          F A (i.toNat + 1) := by
  sorry

theorem chapter03ValuationLowerGroup_zero_eq_inertia
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter03ValuationLowerGroup F A 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup F A := by
  sorry

theorem chapter03ValuationLowerGroup_succ_le
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (i : ℕ) :
    chapter03ValuationLowerGroup F A (i + 1) ≤
      chapter03ValuationLowerGroup F A i := by
  sorry

/- The same lower group viewed in the ambient Galois group. -/
def chapter03GaloisLowerGroup
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (i : ℤ) : Subgroup (Gal(E / F)) :=
  if i < 0 then ⊤ else
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
      F A (i.toNat + 1)).map (Subgroup.subtype _)

@[simp]
theorem chapter03GaloisLowerGroup_neg_one
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter03GaloisLowerGroup F A (-1) = ⊤ := by
  sorry

theorem chapter03GaloisLowerGroup_zero_eq_inertia
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter03GaloisLowerGroup F A 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG
        F A := by
  sorry

theorem chapter03GaloisLowerGroup_succ_le
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (i : ℕ) :
    chapter03GaloisLowerGroup F A (i + 1) ≤
      chapter03GaloisLowerGroup F A i := by
  sorry

/- The valuation of a displacement of an integral element. -/
def chapter03DisplacementValue
    {L Γ : Type*} [Field L] [LinearOrderedAddCommGroupWithTop Γ]
    (vL : AddValuation L Γ) (σ : L ≃+* L) (x : L) : Γ :=
  vL (σ x - x)

/- The same displacement with a Galois automorphism as the acting element. -/
def chapter03GaloisDisplacementValue
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedAddCommGroupWithTop Γ]
    (vL : AddValuation L Γ) (σ : Gal(L / K)) (x : L) : Γ :=
  chapter03DisplacementValue vL σ.toRingEquiv x

/- The set of displacement values on a chosen integral set. -/
def chapter03DisplacementValues
    {L : Type*} [Field L] (vL : AddValuation L (WithTop ℤ))
    (B : Set L) (σ : L ≃+* L) : Set (WithTop ℤ) :=
  {r | ∃ x : L, x ∈ B ∧ r = chapter03DisplacementValue vL σ x}

/- The minimum-displacement definition of `i_G(σ)`, with `+∞` for the
identity when every tested displacement is zero. -/
noncomputable def chapter03DisplacementIndex
    {L : Type*} [Field L] (vL : AddValuation L (WithTop ℤ))
    (B : Set L) (σ : L ≃+* L) : WithTop ℤ :=
  sInf (chapter03DisplacementValues vL B σ)

theorem chapter03DisplacementIndex_le
    {L : Type*} [Field L] (vL : AddValuation L (WithTop ℤ))
    (B : Set L) (σ : L ≃+* L) {x : L} (hx : x ∈ B) :
    chapter03DisplacementIndex vL B σ ≤
      chapter03DisplacementValue vL σ x := by
  sorry

theorem chapter03DisplacementIndex_one
    {L : Type*} [Field L] (vL : AddValuation L (WithTop ℤ))
    (B : Set L) :
    chapter03DisplacementIndex vL B (1 : L ≃+* L) = ⊤ := by
  sorry

@[simp]
theorem chapter03DisplacementValue_apply
    {L Γ : Type*} [Field L] [LinearOrderedAddCommGroupWithTop Γ]
    (vL : AddValuation L Γ) (σ : L ≃+* L) (x : L) :
    chapter03DisplacementValue vL σ x = vL (σ x - x) := rfl

/-
The finite lower filtration interface used by the explicit calculations.
The identity automorphism is intentionally excluded from the finite
displacement test, matching the source convention `i_G(1) = +∞`.
-/
structure Chapter03LowerDisplacementFiltration
    (G : Type u) [Group G] [Finite G] where
  lower : ℤ → Subgroup G
  displacement : G → ℕ
  lower_neg_one : lower (-1) = ⊤
  lower_nat_mem_iff :
    ∀ {σ : G}, σ ≠ 1 → ∀ n : ℕ,
      σ ∈ lower (n : ℤ) ↔ n + 1 ≤ displacement σ

namespace Chapter03LowerDisplacementFiltration

variable {G : Type u} [Group G] [Finite G]

@[ext]
theorem ext {F F' : Chapter03LowerDisplacementFiltration G}
    (hlower : F.lower = F'.lower)
    (hdisplacement : F.displacement = F'.displacement) :
    F = F' := by
  cases F
  cases F'
  cases hlower
  cases hdisplacement
  rfl

end Chapter03LowerDisplacementFiltration

/- A nonnegative lower jump in the source's integer convention. -/
def chapter03LowerBreak
    {G : Type u} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) (m : ℕ) : Prop :=
  F.lower (m : ℤ) ≠ F.lower (m + 1 : ℕ)

/- The full-through-`m`, trivial-after-`m` one-break profile. -/
def chapter03OneBreakProfile
    {G : Type u} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) (m : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ m → F.lower (n : ℤ) = ⊤) ∧
    (∀ n : ℕ, m + 1 ≤ n → F.lower (n : ℤ) = ⊥)

theorem chapter03_one_break_profile_of_constant_displacement
    {G : Type u} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) (m : ℕ)
    (hdisp : ∀ {σ : G}, σ ≠ 1 → F.displacement σ = m + 1) :
    chapter03OneBreakProfile F m := by
  sorry

theorem chapter03_one_break_is_unique
    {G : Type u} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) (m : ℕ)
    (hdisp : ∀ {σ : G}, σ ≠ 1 → F.displacement σ = m + 1)
    (hnontrivial : ∃ σ : G, σ ≠ 1) :
    chapter03LowerBreak F m := by
  sorry

/-
The tame profile allows non-inertial elements to have displacement zero.
It is the group-theoretic form of `G_0 = H` and `G_1 = 1`.
-/
theorem chapter03_tame_profile_of_inertia_displacement
    {G : Type u} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) (H : Subgroup G)
    (hinside : ∀ {σ : G}, σ ∈ H → σ ≠ 1 → F.displacement σ = 1)
    (houtside : ∀ {σ : G}, σ ∉ H → F.displacement σ = 0) :
    F.lower 0 = H ∧ F.lower 1 = ⊥ := by
  sorry

theorem chapter03_lower_filtration_eventually_trivial
    {G : Type u} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → F.lower (n : ℤ) = ⊥ := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter03
