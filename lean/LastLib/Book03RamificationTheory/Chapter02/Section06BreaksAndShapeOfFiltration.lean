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
  obtain ⟨N, hN⟩ := F.eventually_trivial
  refine (Finset.finite_toSet (Finset.range N)).subset ?_
  intro n hn
  change chapter02LowerBreak F n at hn
  have hnlt : n < N := by
    by_contra hnot
    have hnN : N ≤ n := by omega
    have hgn : F.group n = ⊥ := hN n hnN
    have hgn1 : F.group (n + 1) = ⊥ := hN (n + 1) (by omega)
    apply hn
    simp [hgn, hgn1]
  simpa using hnlt

/-- The break at zero is exactly the nontrivial tame layer. -/
theorem chapter02_lower_break_zero_iff_tame_layer_nontrivial
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    chapter02LowerBreak F 0 ↔ Nontrivial (chapter02TameLayer F) := by
  let N := (F.group 1).subgroupOf (F.group 0)
  let : N.Normal := chapter02_lower_layer_normal F 0
  change F.group 0 ≠ F.group 1 ↔ Nontrivial (F.group 0 ⧸ N)
  rw [QuotientGroup.nontrivial_iff]
  constructor
  · intro hbreak htop
    apply hbreak
    apply le_antisymm
    · intro x hx
      have hx' : (⟨x, hx⟩ : F.group 0) ∈ N := by
        rw [htop]
        trivial
      exact hx'
    · exact F.descending 0
  · intro hN heq
    apply hN
    apply top_unique
    intro x hx
    have hx0 : (x : G) ∈ F.group 0 := x.property
    have hx1 : (x : G) ∈ F.group 1 := by
      rw [← heq]
      exact hx0
    exact hx1

/-- Positive breaks occur in the wild part of the filtration. -/
theorem chapter02_positive_lower_break_is_wild
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) {n : ℕ}
    (hn : 1 ≤ n) :
    F.group n ≤ chapter02WildGroup F := by
  change F.group n ≤ F.group 1
  induction hn with
  | refl => exact le_rfl
  | @step n hn ih => exact (F.descending n).trans ih

/-- The exact lower levels occupied by an inertial element. -/
theorem chapter02_inertial_membership_range
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (σ : G) (hσ : σ ≠ 1)
    (_hI : σ ∈ F.group 0)
    (d : ℕ) (hd : F.displacement σ = (d : WithTop ℤ)) :
    ∀ n : ℕ, σ ∈ F.group n ↔ n < d := by
  intro n
  rw [F.lower_mem_iff hσ n, hd]
  constructor
  · intro h
    have h' : ((n + 1 : ℕ) : ℤ) ≤ d :=
      WithTop.coe_le_coe.mp h
    omega
  · intro h
    apply WithTop.coe_le_coe.mpr
    exact_mod_cast (Nat.succ_le_iff.mpr h)

/-- The filtration and displacement determine one another. -/
theorem chapter02_same_filtration_same_displacement
    {G : Type u} [Group G] [Finite G]
    (F F' : Chapter02LowerFiltration G)
    (hgroup : ∀ n : ℕ, F.group n = F'.group n) :
    ∀ σ : G, F.displacement σ = F'.displacement σ := by
  intro σ
  by_cases hσ : σ = 1
  · simp [hσ, F.displacement_one, F'.displacement_one]
  · have hfinite : ∀ H : Chapter02LowerFiltration G, H.displacement σ ≠ ⊤ := by
      intro H htop
      obtain ⟨N, hN⟩ := H.eventually_trivial
      have hmem : σ ∈ H.group N := by
        apply (H.lower_mem_iff hσ N).2
        rw [htop]
        exact le_top
      rw [hN N le_rfl] at hmem
      have : σ = 1 := by simpa using hmem
      exact hσ this
    obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (hfinite F)
    obtain ⟨d', hd'⟩ := WithTop.ne_top_iff_exists.mp (hfinite F')
    have hnonneg_d : (0 : ℤ) ≤ d := by
      apply WithTop.coe_le_coe.mp
      rw [hd]
      exact F.displacement_nonnegative σ
    have hnonneg_d' : (0 : ℤ) ≤ d' := by
      apply WithTop.coe_le_coe.mp
      rw [hd']
      exact F'.displacement_nonnegative σ
    have hcutTop (n : ℕ) :
        ((n + 1 : ℕ) : WithTop ℤ) ≤ (d : WithTop ℤ) ↔
          ((n + 1 : ℕ) : WithTop ℤ) ≤ (d' : WithTop ℤ) := by
      rw [hd, hd', ← F.lower_mem_iff hσ n, ← F'.lower_mem_iff hσ n,
        hgroup n]
    have hcut (n : ℕ) :
      ((n + 1 : ℕ) : ℤ) ≤ d ↔ ((n + 1 : ℕ) : ℤ) ≤ d' := by
      have hcut' := hcutTop n
      rw [← WithTop.coe_natCast] at hcut'
      simpa only [WithTop.coe_le_coe] using hcut'
    have hdd' : d ≤ d' := by
      by_contra hnot
      have hlt : d' < d := lt_of_not_ge hnot
      let n : ℕ := d'.toNat
      have hnval : (n : ℤ) = d' := by
        dsimp [n]
        exact Int.toNat_of_nonneg hnonneg_d'
      have hleft : ((n + 1 : ℕ) : ℤ) ≤ d := by
        omega
      have hright := (hcut n).mp hleft
      omega
    have hd'd : d' ≤ d := by
      by_contra hnot
      have hlt : d < d' := lt_of_not_ge hnot
      let n : ℕ := d.toNat
      have hnval : (n : ℤ) = d := by
        dsimp [n]
        exact Int.toNat_of_nonneg hnonneg_d
      have hleft : ((n + 1 : ℕ) : ℤ) ≤ d' := by
        omega
      have hright := (hcut n).mpr hleft
      omega
    apply le_antisymm
    · rw [← hd, ← hd']
      exact WithTop.coe_le_coe.mpr hdd'
    · rw [← hd, ← hd']
      exact WithTop.coe_le_coe.mpr hd'd

theorem chapter02_same_displacement_same_filtration
    {G : Type u} [Group G] [Finite G]
    (F F' : Chapter02LowerFiltration G)
    (hdisp : ∀ σ : G, F.displacement σ = F'.displacement σ) :
    ∀ n : ℕ, F.group n = F'.group n := by
  intro n
  ext σ
  by_cases hσ : σ = 1
  · simp [hσ]
  · rw [F.lower_mem_iff hσ n, F'.lower_mem_iff hσ n, hdisp σ]

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
  classical
  by_cases hd0 : d = 0
  · subst d
    have hset : chapter02VisibleLowerLevels F N σ = ∅ := by
      ext n
      constructor
      · intro hn
        change n ∈ (Finset.range N).filter
          (fun m => σ ≠ 1 ∧ σ ∈ F.group m) at hn
        have hmem : σ ∈ F.group n := (Finset.mem_filter.mp hn).2.2
        have hle := (F.lower_mem_iff hσ n).1 hmem
        rw [hd] at hle
        have hpos : (0 : WithTop ℤ) < ((n + 1 : ℕ) : WithTop ℤ) := by
          rw [← WithTop.coe_natCast]
          apply WithTop.coe_lt_coe.mpr
          exact_mod_cast (Nat.succ_pos n)
        exact (not_le_of_gt hpos hle).elim
      · intro hn
        simp at hn
    rw [hset]
    simp
  · have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hI : σ ∈ F.group 0 := by
      apply (F.lower_mem_iff hσ 0).2
      rw [hd]
      change ((1 : ℕ) : WithTop ℤ) ≤ (d : WithTop ℤ)
      rw [← WithTop.coe_natCast]
      apply WithTop.coe_le_coe.mpr
      exact_mod_cast hdpos
    have hset : chapter02VisibleLowerLevels F N σ = Finset.range d := by
      ext n
      simp only [chapter02VisibleLowerLevels, Finset.mem_filter, Finset.mem_range]
      rw [chapter02_inertial_membership_range F σ hσ hI d hd n]
      constructor
      · rintro ⟨hnN, _, hn⟩
        exact hn
      · intro hn
        exact ⟨by omega, hσ, hn⟩
    rw [hset, Finset.card_range]

/--
The elementary double-counting identity behind Hilbert's different formula:
the sum of the nonidentity lower-group sizes equals the sum of the visible
lower levels of the nonidentity automorphisms.
-/
theorem chapter02_lower_cardinality_sum_eq_visible_depth_sum
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (N : ℕ)
    (_hN : ∀ n : ℕ, N ≤ n → F.group n = ⊥) :
    (Finset.sum (Finset.range N) (fun n => Nat.card (F.group n) - 1)) =
      ∑ σ : G, (chapter02VisibleLowerLevels F N σ).card := by
  classical
  have hvisible (σ : G) :
      (chapter02VisibleLowerLevels F N σ).card =
        ∑ n ∈ Finset.range N,
          if σ ≠ 1 ∧ σ ∈ F.group n then 1 else 0 := by
    simp [chapter02VisibleLowerLevels]
  have hinner (n : ℕ) :
      (∑ σ : G, if σ ≠ 1 ∧ σ ∈ F.group n then 1 else 0) =
        Nat.card (F.group n) - 1 := by
    let H := F.group n
    let p : G → Prop := fun σ => σ ≠ 1 ∧ σ ∈ H
    let e : {σ : G // p σ} ≃ {x : H // x ≠ 1} :=
      { toFun := fun x =>
          ⟨⟨x.1, x.2.2⟩, by
            intro hx
            apply x.2.1
            exact congrArg Subtype.val hx⟩
        invFun := fun x =>
          ⟨x.1.1, by
            refine ⟨?_, x.1.2⟩
            intro hx
            apply x.2
            apply Subtype.ext
            exact hx
          ⟩
        left_inv := by
          intro x
          rfl
        right_inv := by
          intro x
          rfl }
    have hcard_nonidentity :
        Fintype.card {x : H // x ≠ 1} = Nat.card H - 1 := by
      rw [Nat.card_eq_fintype_card]
      rw [Fintype.card_subtype_compl]
      simp
    calc
      (∑ σ : G, if σ ≠ 1 ∧ σ ∈ F.group n then 1 else 0) =
          (Finset.univ.filter p).card := by
            change (∑ σ : G, if p σ then 1 else 0) =
              (Finset.univ.filter p).card
            exact Finset.sum_boole (R := ℕ) p (Finset.univ : Finset G)
      _ = Fintype.card {σ : G // p σ} := by
        symm
        simpa using Fintype.card_subtype p
      _ = Fintype.card {x : H // x ≠ 1} := Fintype.card_congr e
      _ = Nat.card H - 1 := hcard_nonidentity
      _ = Nat.card (F.group n) - 1 := by rfl
  calc
    Finset.sum (Finset.range N) (fun n => Nat.card (F.group n) - 1) =
        ∑ n ∈ Finset.range N,
          ∑ σ : G, if σ ≠ 1 ∧ σ ∈ F.group n then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hinner n).symm
    _ = ∑ σ : G, ∑ n ∈ Finset.range N,
          if σ ≠ 1 ∧ σ ∈ F.group n then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ σ : G, (chapter02VisibleLowerLevels F N σ).card := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact (hvisible σ).symm

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
