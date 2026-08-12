import LastLib.Book03RamificationTheory.Chapter05.Section03TowerTransitivity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

/-! ## 5.4. Break conversion in examples -/

/-- The piecewise Herbrand function for one cyclic wild layer. -/
def chapter05SingleBreakHerbrand (p m : ℕ) (u : ℝ) : ℝ :=
  if u ≤ 0 then u else if u ≤ (m : ℝ) then u else
    (m : ℝ) + (u - m) / (p : ℝ)

/-- The piecewise Herbrand function for a tame totally ramified layer. -/
def chapter05TameHerbrand (e : ℕ) (u : ℝ) : ℝ :=
  if u ≤ 0 then u else u / (e : ℝ)

/-- The lower-filtration hypotheses for a single positive break. -/
structure Chapter05SingleWildBreakData
    (G : Type*) [Group G] [Fintype G] where
  profile : Chapter05RamificationFiltration G
  p : ℕ
  m : ℕ
  p_prime : Nat.Prime p
  m_pos : 0 < m
  cyclic : IsCyclic G
  zeroth_card : Nat.card (profile.lowerGroup 0) = p
  lower_through_break :
    ∀ u : ℝ, 0 ≤ u → u ≤ (m : ℝ) →
      profile.lowerGroup u = profile.lowerGroup 0
  lower_after_break :
    ∀ u : ℝ, (m : ℝ) < u → profile.lowerGroup u = ⊥

/-- The single-break formula from the source, including the negative extension. -/
theorem chapter05_single_wild_break_herbrand_formula
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05SingleWildBreakData G)
    (hintegrable : ∀ a b : ℝ,
      IntervalIntegrable (chapter05HerbrandSlope D.profile) volume a b)
    (u : ℝ) :
    chapter05HerbrandFunction D.profile u =
      chapter05SingleBreakHerbrand D.p D.m u := by
  sorry

theorem chapter05_single_wild_break_upper_label_is_the_same
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05SingleWildBreakData G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D.profile))
    (hintegrable : ∀ a b : ℝ,
      IntervalIntegrable (chapter05HerbrandSlope D.profile) volume a b) :
    chapter05UpperBreak D.profile (D.m : ℝ) ∧
      chapter05HerbrandFunction D.profile (D.m : ℝ) = (D.m : ℝ) ∧
      ∀ v : ℝ, chapter05UpperBreak D.profile v → v = (D.m : ℝ) := by
  sorry

/-- A tame layer has constant positive slope `1/e`. -/
theorem chapter05_tame_herbrand_slope
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) (he : 0 < e)
    (hcard : Nat.card (D.lowerGroup 0) = e)
    (htrivial : ∀ u : ℝ, 0 < u → D.lowerGroup u = ⊥) :
    ∀ u : ℝ, 0 < u → chapter05HerbrandSlope D u = (e : ℝ)⁻¹ := by
  sorry

/-- The Herbrand function for a tame totally ramified group of order `e`. -/
theorem chapter05_tame_herbrand_formula
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) (he : 0 < e)
    (hcard : Nat.card (D.lowerGroup 0) = e)
    (htotal : Nat.card G = e)
    (htrivial : ∀ u : ℝ, 0 < u → D.lowerGroup u = ⊥)
    (hintegrable : ∀ a b : ℝ,
      IntervalIntegrable (chapter05HerbrandSlope D) volume a b)
    (u : ℝ) :
    chapter05HerbrandFunction D u = chapter05TameHerbrand e u := by
  sorry

/-- Positive upper groups vanish immediately after zero in the tame case. -/
theorem chapter05_tame_upper_groups_drop_after_zero
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) (he : 0 < e)
    (hcard : Nat.card (D.lowerGroup 0) = e)
    (htotal : Nat.card G = e)
    (htrivial : ∀ u : ℝ, 0 < u → D.lowerGroup u = ⊥)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    ∀ v : ℝ, 0 < v → chapter05UpperRamificationGroup D v = ⊥ := by
  sorry

theorem chapter05_tame_has_only_zero_break
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) (he : 1 < e)
    (hcard : Nat.card (D.lowerGroup 0) = e)
    (htotal : Nat.card G = e)
    (htrivial : ∀ u : ℝ, 0 < u → D.lowerGroup u = ⊥)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (hzero : D.lowerGroup 0 ≠ ⊥) :
    chapter05UpperBreak D 0 ∧
      ∀ v : ℝ, 0 < v → ¬chapter05UpperBreak D v := by
  sorry

/-- The tame slope is the scale change that becomes visible in a composite tower. -/
theorem chapter05_tame_scale_change_is_one_division_by_e
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) (he : 0 < e)
    (hcard : Nat.card (D.lowerGroup 0) = e)
    (htrivial : ∀ u : ℝ, 0 < u → D.lowerGroup u = ⊥) :
    ∀ u : ℝ, 0 < u →
      chapter05HerbrandSlope D u = (1 : ℝ) / (e : ℝ) := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter05
