import LastLib.Book03RamificationTheory.Chapter04.Section04HerbrandFunction

namespace LastLib.Book03RamificationTheory.Chapter04

noncomputable section

open scoped BigOperators Pointwise

/-! ## 4.5. Upper reindexing for a subgroup -/

/-- Upper ramification groups obtained by reindexing the lower filtration with
the inverse Herbrand function. -/
def chapter04UpperGroup
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (v : ℝ) : Subgroup G :=
  chapter04RealLowerGroup F (chapter04HerbrandInverse F v)

/-- The upper filtration of the extension represented by a subgroup
filtration. -/
def chapter04SubgroupUpperGroup
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (v : ℝ) : Subgroup H :=
  chapter04RealLowerGroup (chapter04SubgroupLowerFiltration F H)
    (chapter04HerbrandInverse (chapter04SubgroupLowerFiltration F H) v)

/-- The change of upper scale appearing when an upper subgroup filtration is
viewed inside the ambient filtration. -/
def chapter04UpperReindexing
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (v : ℝ) : ℝ :=
  chapter04HerbrandFunction F
    (chapter04HerbrandInverse (chapter04SubgroupLowerFiltration F H) v)

private theorem chapter04_real_lower_group_map_eq_inf
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) (t : ℝ) :
    (chapter04RealLowerGroup (chapter04SubgroupLowerFiltration F H) t).map H.subtype =
      H ⊓ chapter04RealLowerGroup F t := by
  by_cases htneg : t < 0
  · have hsub_top :
        chapter04RealLowerGroup (chapter04SubgroupLowerFiltration F H) t = ⊤ := by
      simp [chapter04RealLowerGroup, htneg]
    have hamb_top : chapter04RealLowerGroup F t = ⊤ := by
      simp [chapter04RealLowerGroup, htneg]
    rw [hsub_top, hamb_top]
    rw [inf_top_eq]
    ext g
    constructor
    · rintro ⟨x, -, rfl⟩
      exact x.property
    · intro hg
      exact ⟨⟨g, hg⟩, by simp, rfl⟩
  · have ht0 : 0 ≤ t := le_of_not_gt htneg
    have hceil : 0 ≤ Int.ceil t := Int.ceil_nonneg ht0
    have hsub :
        chapter04RealLowerGroup (chapter04SubgroupLowerFiltration F H) t =
          chapter04LowerGroup (chapter04SubgroupLowerFiltration F H) (Int.ceil t) := by
      simp [chapter04RealLowerGroup, htneg,
        chapter04LowerGroup_of_nonnegative
          (chapter04SubgroupLowerFiltration F H) hceil]
    have hamb :
        chapter04RealLowerGroup F t = chapter04LowerGroup F (Int.ceil t) := by
      simp [chapter04RealLowerGroup, htneg,
        chapter04LowerGroup_of_nonnegative F hceil]
    rw [hsub, hamb]
    exact chapter04SubgroupLowerGroup_map_eq_inf F H (Int.ceil t)

private theorem chapter04_herbrand_inverse_ge_neg_one
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {v : ℝ} (hv : -1 ≤ v) :
    -1 ≤ chapter04HerbrandInverse F v := by
  by_contra hdom
  have hinv_neg : chapter04HerbrandInverse F v < -1 := lt_of_not_ge hdom
  have hinv_nonpos : chapter04HerbrandInverse F v ≤ 0 :=
    le_trans hinv_neg.le (by norm_num)
  have hright := chapter04_herbrand_inverse_right_inverse F hv
  rw [chapter04HerbrandFunction_of_nonpositive F hinv_nonpos] at hright
  linarith

/-- Upper numbering for a subgroup, with the necessary Herbrand change of
scale.  This is the formal version of (4.1). -/
theorem chapter04_upper_reindexing_subgroup
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) {v : ℝ}
    (hv : 0 ≤ v) :
    (chapter04SubgroupUpperGroup F H v).map H.subtype =
      H ⊓ chapter04UpperGroup F (chapter04UpperReindexing F H v) := by
  let Fsub := chapter04SubgroupLowerFiltration F H
  have hdom : -1 ≤ chapter04HerbrandInverse Fsub v :=
    chapter04_herbrand_inverse_ge_neg_one Fsub (le_trans (by norm_num) hv)
  change (chapter04RealLowerGroup Fsub
      (chapter04HerbrandInverse Fsub v)).map H.subtype =
    H ⊓ chapter04RealLowerGroup F
      (chapter04HerbrandInverse F
        (chapter04HerbrandFunction F (chapter04HerbrandInverse Fsub v)))
  rw [chapter04_herbrand_inverse_left_inverse F hdom]
  exact chapter04_real_lower_group_map_eq_inf F H _

/-- Membership form of the subgroup upper-numbering formula. -/
theorem chapter04_upper_reindexing_subgroup_mem_iff
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) {v : ℝ}
    (hv : 0 ≤ v) (σ : H) :
    σ ∈ chapter04SubgroupUpperGroup F H v ↔
      (σ : G) ∈ chapter04UpperGroup F (chapter04UpperReindexing F H v) := by
  have hmap := chapter04_upper_reindexing_subgroup F H hv
  rw [← Subgroup.mem_map_iff_mem H.subtype_injective, hmap]
  exact and_iff_right σ.property

/-- Abstract tower transitivity for Herbrand functions.  In a normal field
tower this is the identity `φ_(L/K) = φ_(M/K) ∘ φ_(L/M)`. -/
def chapter04HerbrandTowerIdentity
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) [H.Normal]
    (Q : Chapter04LowerFiltration (G ⧸ H)) : Prop :=
  ∀ {t : ℝ}, -1 ≤ t →
    chapter04HerbrandFunction F t =
      chapter04HerbrandFunction Q
        (chapter04HerbrandFunction (chapter04SubgroupLowerFiltration F H) t)

/-- Under tower transitivity, the subgroup reindexing is exactly the quotient
Herbrand coordinate. -/
theorem chapter04_upper_reindexing_eq_quotient_herbrand
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) [H.Normal]
    (Q : Chapter04LowerFiltration (G ⧸ H))
    (htower : chapter04HerbrandTowerIdentity F H Q) {v : ℝ}
    (hv : -1 ≤ v) :
    chapter04UpperReindexing F H v = chapter04HerbrandFunction Q v := by
  let Fsub := chapter04SubgroupLowerFiltration F H
  have hinv_dom : -1 ≤ chapter04HerbrandInverse Fsub v :=
    chapter04_herbrand_inverse_ge_neg_one Fsub hv
  change chapter04HerbrandFunction F
      (chapter04HerbrandInverse Fsub v) = chapter04HerbrandFunction Q v
  calc
    chapter04HerbrandFunction F (chapter04HerbrandInverse Fsub v) =
        chapter04HerbrandFunction Q
          (chapter04HerbrandFunction Fsub
            (chapter04HerbrandInverse Fsub v)) := htower hinv_dom
    _ = chapter04HerbrandFunction Q v := by
      rw [chapter04_herbrand_inverse_right_inverse Fsub hv]

end
end LastLib.Book03RamificationTheory.Chapter04
