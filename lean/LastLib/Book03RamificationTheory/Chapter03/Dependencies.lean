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
  by
    classical
    exact if σ = 1 then ⊤ else sInf (chapter03DisplacementValues vL B σ)

theorem chapter03DisplacementIndex_le
    {L : Type*} [Field L] (vL : AddValuation L (WithTop ℤ))
    (B : Set L) (σ : L ≃+* L) (hσ : σ ≠ 1)
    (hbounded : BddBelow (chapter03DisplacementValues vL B σ))
    {x : L} (hx : x ∈ B) :
    chapter03DisplacementIndex vL B σ ≤
    chapter03DisplacementValue vL σ x := by
  unfold chapter03DisplacementIndex
  rw [if_neg hσ]
  apply csInf_le hbounded
  exact ⟨x, hx, rfl⟩

theorem chapter03DisplacementIndex_one
    {L : Type*} [Field L] (vL : AddValuation L (WithTop ℤ))
    (B : Set L) :
    chapter03DisplacementIndex vL B (1 : L ≃+* L) = ⊤ := by
  simp [chapter03DisplacementIndex]

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
  constructor
  · intro n hn
    apply le_antisymm le_top
    intro σ _
    by_cases hσ : σ = 1
    · subst σ
      exact (F.lower (n : ℤ)).one_mem
    · apply (F.lower_nat_mem_iff hσ n).2
      simpa [hdisp hσ] using Nat.succ_le_succ hn
  · intro n hmn
    apply le_antisymm
    · intro σ hσmem
      by_cases hσ : σ = 1
      · subst σ
        exact (⊥ : Subgroup G).one_mem
      · have hle := (F.lower_nat_mem_iff hσ n).1 hσmem
        have hle' : n + 1 ≤ m + 1 := by
          simpa [hdisp hσ] using hle
        exact False.elim ((Nat.not_succ_le_self n) (hle'.trans hmn))
    · exact bot_le

theorem chapter03_one_break_is_unique
    {G : Type u} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) (m : ℕ)
    (hdisp : ∀ {σ : G}, σ ≠ 1 → F.displacement σ = m + 1)
    (hnontrivial : ∃ σ : G, σ ≠ 1) :
    chapter03LowerBreak F m := by
  unfold chapter03LowerBreak
  intro hEq
  obtain ⟨σ, hσ⟩ := hnontrivial
  have hmem : σ ∈ F.lower (m : ℤ) := by
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
    (F : Chapter03LowerDisplacementFiltration G) (H : Subgroup G)
    (hinside : ∀ {σ : G}, σ ∈ H → σ ≠ 1 → F.displacement σ = 1)
    (houtside : ∀ {σ : G}, σ ∉ H → F.displacement σ = 0) :
    F.lower 0 = H ∧ F.lower 1 = ⊥ := by
  constructor
  · apply le_antisymm
    · intro σ hσmem
      by_cases hσ : σ = 1
      · subst σ
        exact H.one_mem
      · by_cases hH : σ ∈ H
        · exact hH
        · have hle := (F.lower_nat_mem_iff hσ 0).1 hσmem
          rw [houtside hH] at hle
          exact False.elim (by omega)
    · intro σ hH
      by_cases hσ : σ = 1
      · subst σ
        exact (F.lower 0).one_mem
      · apply (F.lower_nat_mem_iff hσ 0).2
        simp [hinside hH hσ]
  · apply le_antisymm
    · intro σ hσmem
      by_cases hσ : σ = 1
      · subst σ
        exact (⊥ : Subgroup G).one_mem
      · have hle := (F.lower_nat_mem_iff hσ 1).1 hσmem
        by_cases hH : σ ∈ H
        · rw [hinside hH hσ] at hle
          omega
        · rw [houtside hH] at hle
          omega
    · exact bot_le

theorem chapter03_lower_filtration_eventually_trivial
    {G : Type u} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → F.lower (n : ℤ) = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨σ₀, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset G) F.displacement
      Finset.univ_nonempty
  refine ⟨F.displacement σ₀, ?_⟩
  intro n hn
  apply le_antisymm
  · intro σ hσmem
    by_cases hσ : σ = 1
    · subst σ
      exact (⊥ : Subgroup G).one_mem
    · have hle := (F.lower_nat_mem_iff hσ n).1 hσmem
      have hbound := hmax σ (Finset.mem_univ σ)
      omega
  · exact bot_le

end
end LastLib.Book03RamificationTheory.Chapter03
