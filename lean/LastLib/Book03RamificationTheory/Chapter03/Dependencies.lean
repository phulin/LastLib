import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary
import LastLib.Book03RamificationTheory.Chapter02.Section06BreaksAndShapeOfFiltration
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open scoped BigOperators Pointwise

universe u v

/-!
Shared interfaces for Chapter 3.

Chapters 1--2 already expose the canonical valuation lower groups and the
full lower-filtration interface.  The finite-depth structure below is kept as
a small calculation-facing bridge for the explicit examples: it uses natural
number displacement values away from the identity, while the valuation-ring
definitions remain connected to Book 2's canonical congruence groups.
-/

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
  simp [chapter03ValuationLowerGroup]

theorem chapter03ValuationLowerGroup_of_nonnegative
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) {i : ℤ} (hi : 0 ≤ i) :
    chapter03ValuationLowerGroup F A i =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
        F A (i.toNat + 1) := by
  simp [chapter03ValuationLowerGroup, not_lt.mpr hi]

theorem chapter03ValuationLowerGroup_mem_iff_of_nonnegative
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) {i : ℤ} (hi : 0 ≤ i)
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      F A) :
    σ ∈ chapter03ValuationLowerGroup F A i ↔
      σ ∈
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
          F A (i.toNat + 1) := by
  rw [chapter03ValuationLowerGroup_of_nonnegative F A hi]

theorem chapter03ValuationLowerGroup_zero_eq_inertia
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter03ValuationLowerGroup F A 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroup F A := by
  rw [chapter03ValuationLowerGroup_of_nonnegative F A (i := 0) (by norm_num)]
  simpa using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FirstRamificationGroup_eq_inertia
      (A := A))

theorem chapter03ValuationLowerGroup_succ_le
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (i : ℕ) :
    chapter03ValuationLowerGroup F A (i + 1) ≤
      chapter03ValuationLowerGroup F A i := by
  rw [chapter03ValuationLowerGroup, if_neg (by omega),
    chapter03ValuationLowerGroup, if_neg (by omega)]
  simpa using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup_succ_le
      A (i + 1))

/- The same lower group viewed in the ambient Galois group. -/
def chapter03GaloisLowerGroup
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (i : ℤ) : Subgroup (Gal(E / F)) :=
  if i < 0 then
    (⊤ : Subgroup
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        F A)).map (Subgroup.subtype _)
  else
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
      F A (i.toNat + 1)).map (Subgroup.subtype _)

@[simp]
theorem chapter03GaloisLowerGroup_neg_one
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E)
    (hdecomp :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
          F A = ⊤) :
    chapter03GaloisLowerGroup F A (-1) = ⊤ := by
  rw [chapter03GaloisLowerGroup, if_pos (by norm_num)]
  apply le_antisymm le_top
  intro σ _
  have hσ : σ ∈
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        F A := by
    rw [hdecomp]
    trivial
  refine ⟨⟨σ, hσ⟩, ?_⟩
  simp

theorem chapter03GaloisLowerGroup_zero_eq_inertia
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter03GaloisLowerGroup F A 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG
        F A := by
  rw [chapter03GaloisLowerGroup, if_neg (by norm_num)]
  simpa [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG] using congrArg
    (fun H : Subgroup
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
          F A) => H.map (Subgroup.subtype _))
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FirstRamificationGroup_eq_inertia
      (A := A))

theorem chapter03GaloisLowerGroup_succ_le
    (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (i : ℕ) :
    chapter03GaloisLowerGroup F A (i + 1) ≤
      chapter03GaloisLowerGroup F A i := by
  rw [chapter03GaloisLowerGroup, if_neg (by omega),
    chapter03GaloisLowerGroup, if_neg (by omega)]
  apply Subgroup.map_mono
  simpa using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup_succ_le
      A (i + 1))

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

@[simp]
theorem chapter03DisplacementValue_apply
    {L Γ : Type*} [Field L] [LinearOrderedAddCommGroupWithTop Γ]
    (vL : AddValuation L Γ) (σ : L ≃+* L) (x : L) :
    chapter03DisplacementValue vL σ x = vL (σ x - x) := rfl

/- Chapter 2 already provides the canonical finite lower filtration,
   including normality, descent, eventual triviality, and the `+∞` value for
   the identity.  Chapter 3 uses that interface directly. -/

/- The full-through-`m`, trivial-after-`m` one-break profile. -/
def chapter03OneBreakProfile
    {G : Type u} [Group G] [Finite G]
    (F : LastLib.Book03RamificationTheory.Chapter02.Chapter02LowerFiltration G)
    (m : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ m → F.group n = ⊤) ∧
    (∀ n : ℕ, m + 1 ≤ n → F.group n = ⊥)

theorem chapter03_one_break_profile_of_constant_displacement
    {G : Type u} [Group G] [Finite G]
    (F : LastLib.Book03RamificationTheory.Chapter02.Chapter02LowerFiltration G)
    (m : ℕ)
    (hdisp : ∀ {σ : G}, σ ≠ 1 →
      F.displacement σ = ((m + 1 : ℕ) : WithTop ℤ)) :
    chapter03OneBreakProfile F m := by
  constructor
  · intro n hn
    apply le_antisymm le_top
    intro σ _
    by_cases hσ : σ = 1
    · subst σ
      exact (F.group n).one_mem
    · apply (F.lower_mem_iff hσ n).2
      rw [hdisp hσ]
      exact_mod_cast Nat.succ_le_succ hn
  · intro n hmn
    apply le_antisymm
    · intro σ hσmem
      by_cases hσ : σ = 1
      · subst σ
        exact (⊥ : Subgroup G).one_mem
      · have hle := (F.lower_mem_iff hσ n).1 hσmem
        rw [hdisp hσ] at hle
        have hle' : n + 1 ≤ m + 1 := by exact_mod_cast hle
        exact False.elim ((Nat.not_succ_le_self n) (hle'.trans hmn))
    · exact bot_le

theorem chapter03_one_break_is_unique
    {G : Type u} [Group G] [Finite G]
    (F : LastLib.Book03RamificationTheory.Chapter02.Chapter02LowerFiltration G)
    (m : ℕ)
    (hdisp : ∀ {σ : G}, σ ≠ 1 →
      F.displacement σ = ((m + 1 : ℕ) : WithTop ℤ))
    (hnontrivial : ∃ σ : G, σ ≠ 1) :
    LastLib.Book03RamificationTheory.Chapter02.chapter02LowerBreak F m := by
  intro hEq
  obtain ⟨σ, hσ⟩ := hnontrivial
  have hmem : σ ∈ F.group m := by
    rw [(chapter03_one_break_profile_of_constant_displacement F m hdisp).1 m le_rfl]
    trivial
  rw [hEq, (chapter03_one_break_profile_of_constant_displacement F m hdisp).2
    (m + 1) le_rfl] at hmem
  exact hσ (by simpa using hmem)

/-
The tame profile allows non-inertial elements to have displacement zero.
It is the group-theoretic form of `G_0 = H` and `G_1 = 1`.
-/
theorem chapter03_tame_profile_of_inertia_displacement
    {G : Type u} [Group G] [Finite G]
    (F : LastLib.Book03RamificationTheory.Chapter02.Chapter02LowerFiltration G)
    (H : Subgroup G)
    (hinside : ∀ {σ : G}, σ ∈ H → σ ≠ 1 →
      F.displacement σ = (1 : WithTop ℤ))
    (houtside : ∀ {σ : G}, σ ∉ H →
      F.displacement σ = (0 : WithTop ℤ)) :
    F.group 0 = H ∧ F.group 1 = ⊥ := by
  constructor
  · apply le_antisymm
    · intro σ hσmem
      by_cases hσ : σ = 1
      · subst σ
        exact H.one_mem
      · by_cases hH : σ ∈ H
        · exact hH
        · have hle := (F.lower_mem_iff hσ 0).1 hσmem
          have hle' : (1 : WithTop ℤ) ≤ 0 := by
            simpa [houtside hH] using hle
          exact False.elim
            ((not_le_of_gt (by norm_num : (0 : WithTop ℤ) < 1)) hle')
    · intro σ hH
      by_cases hσ : σ = 1
      · subst σ
        exact (F.group 0).one_mem
      · apply (F.lower_mem_iff hσ 0).2
        rw [hinside hH hσ]
        norm_num
  · apply le_antisymm
    · intro σ hσmem
      by_cases hσ : σ = 1
      · subst σ
        exact (⊥ : Subgroup G).one_mem
      · have hle := (F.lower_mem_iff hσ 1).1 hσmem
        by_cases hH : σ ∈ H
        · have hle' : (2 : WithTop ℤ) ≤ 1 := by
            simp [hinside hH hσ] at hle
          norm_num at hle'
        · have hle' : (2 : WithTop ℤ) ≤ 0 := by
            simpa [houtside hH] using hle
          exact False.elim
            ((not_le_of_gt (by norm_num : (0 : WithTop ℤ) < 2)) hle')
    · exact bot_le

end
end LastLib.Book03RamificationTheory.Chapter03
