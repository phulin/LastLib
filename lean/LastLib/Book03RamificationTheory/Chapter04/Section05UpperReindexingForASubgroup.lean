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

/-- Upper numbering for a subgroup, with the necessary Herbrand change of
scale.  This is the formal version of (4.1). -/
theorem chapter04_upper_reindexing_subgroup
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) {v : ℝ}
    (hv : 0 ≤ v) :
    (chapter04SubgroupUpperGroup F H v).map H.subtype =
      H ⊓ chapter04UpperGroup F (chapter04UpperReindexing F H v) := by
  sorry

/-- Membership form of the subgroup upper-numbering formula. -/
theorem chapter04_upper_reindexing_subgroup_mem_iff
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (H : Subgroup G) {v : ℝ}
    (hv : 0 ≤ v) (σ : H) :
    σ ∈ chapter04SubgroupUpperGroup F H v ↔
      (σ : G) ∈ chapter04UpperGroup F (chapter04UpperReindexing F H v) := by
  sorry

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
  sorry

end
end LastLib.Book03RamificationTheory.Chapter04
