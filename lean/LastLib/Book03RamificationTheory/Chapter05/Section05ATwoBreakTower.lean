import LastLib.Book03RamificationTheory.Chapter05.Section04BreakConversionInExamples

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

open scoped BigOperators

/-! ## 5.5. A two-break tower -/

/-- The piecewise Herbrand function for the two wild layers in the source. -/
def chapter05TwoBreakHerbrand (p a b : ℕ) (u : ℝ) : ℝ :=
  if u ≤ 0 then u else if u ≤ (a : ℝ) then u else
    if u ≤ (b : ℝ) then
      (a : ℝ) + (u - a) / (p : ℝ)
    else
      (a : ℝ) + ((b - a : ℕ) : ℝ) / (p : ℝ) +
        (u - b) / (p : ℝ) ^ 2

/-- The second upper label in the two-break profile. -/
def chapter05TwoBreakSecondUpper (p a b : ℕ) : ℝ :=
  (a : ℝ) + ((b - a : ℕ) : ℝ) / (p : ℝ)

/-- A lower filtration with the two layers `G` and `H` displayed in the source. -/
structure Chapter05TwoBreakData
    (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] where
  profile : Chapter05RamificationFiltration G
  p a b : ℕ
  p_prime : Nat.Prime p
  a_pos : 0 < a
  a_lt_b : a < b
  group_card : Nat.card G = p ^ 2
  subgroup_card : Nat.card H = p
  lower_first_layer :
    ∀ u : ℝ, 0 ≤ u → u ≤ (a : ℝ) → profile.lowerGroup u = ⊤
  lower_second_layer :
    ∀ u : ℝ, (a : ℝ) < u → u ≤ (b : ℝ) → profile.lowerGroup u = H
  lower_after_second_layer :
    ∀ u : ℝ, (b : ℝ) < u → profile.lowerGroup u = ⊥

/-- The complete tower package needed to identify the subgroup and quotient stages. -/
structure Chapter05TwoBreakTowerData
    (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] where
  twoBreak : Chapter05TwoBreakData G H
  tower : Chapter05HerbrandTowerSetup G H
  top_profile_eq : tower.quotientSetup.upstairs = twoBreak.profile
  quotient_first_layer :
    ∀ u : ℝ, 0 ≤ u → u ≤ (twoBreak.a : ℝ) →
      tower.quotientSetup.downstairs.lowerGroup u =
        tower.quotientSetup.downstairs.lowerGroup 0
  quotient_after_first_layer :
    ∀ u : ℝ, (twoBreak.a : ℝ) < u →
      tower.quotientSetup.downstairs.lowerGroup u = ⊥

theorem chapter05_two_break_herbrand_formula
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (D : Chapter05TwoBreakData G H)
    (hintegrable : ∀ a' b' : ℝ,
      IntervalIntegrable (chapter05HerbrandSlope D.profile) volume a' b')
    (u : ℝ) :
    chapter05HerbrandFunction D.profile u =
      chapter05TwoBreakHerbrand D.p D.a D.b u := by
  sorry

theorem chapter05_two_break_upper_breaks
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (D : Chapter05TwoBreakData G H)
    (hbij : Function.Bijective (chapter05HerbrandFunction D.profile)) :
    chapter05UpperBreak D.profile D.a ∧
      chapter05UpperBreak D.profile
        (chapter05TwoBreakSecondUpper D.p D.a D.b) ∧
      ∀ v : ℝ, chapter05UpperBreak D.profile v →
        v = (D.a : ℝ) ∨
          v = chapter05TwoBreakSecondUpper D.p D.a D.b := by
  sorry

/- SOURCE_ISSUE: The source says that the second label may be fractional for
   an arbitrary nonabelian filtration immediately after assuming `|G|=p^2`.
   Every group of order `p^2` is abelian, so that wording cannot describe an
   actual group in this displayed example.  The declarations below separate
   the arithmetic nonintegrality possibility from the abelian local case. -/
theorem chapter05_two_break_second_label_nonintegral_of_not_dvd
    (p a b : ℕ) (hp : 0 < p) (hab : a < b)
    (hndvd : ¬p ∣ b - a) :
    ¬chapter05UpperBreakIsInteger (chapter05TwoBreakSecondUpper p a b) := by
  sorry

theorem chapter05_two_break_second_label_integral_iff_dvd
    (p a b : ℕ) (hp : 0 < p) (hab : a < b) :
    chapter05UpperBreakIsInteger (chapter05TwoBreakSecondUpper p a b) ↔
      p ∣ b - a := by
  sorry

theorem chapter05_two_break_upper_label_is_strictly_compressed
    (p a b : ℕ) (hp : Nat.Prime p) (hab : a < b) :
    (a : ℝ) < chapter05TwoBreakSecondUpper p a b ∧
      chapter05TwoBreakSecondUpper p a b < (b : ℝ) := by
  sorry

theorem chapter05_two_break_subextension_has_lower_break_b
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05TwoBreakTowerData G H) :
    chapter05LowerBreak T.tower.subextension T.twoBreak.b := by
  sorry

theorem chapter05_two_break_quotient_has_lower_break_a
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05TwoBreakTowerData G H) :
    chapter05LowerBreak T.tower.quotientSetup.downstairs T.twoBreak.a := by
  sorry

theorem chapter05_two_break_quotient_upper_groups
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05TwoBreakTowerData G H)
    (hbij : Function.Bijective
      (chapter05HerbrandFunction T.tower.quotientSetup.downstairs)) :
    (∀ v : ℝ, 0 ≤ v → v ≤ (T.twoBreak.a : ℝ) →
      chapter05UpperRamificationGroup T.tower.quotientSetup.downstairs v = ⊤) ∧
    (∀ v : ℝ, (T.twoBreak.a : ℝ) < v →
      chapter05UpperRamificationGroup T.tower.quotientSetup.downstairs v = ⊥) := by
  sorry

theorem chapter05_two_break_raw_stage_labels
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05TwoBreakTowerData G H) :
    chapter05LowerBreak T.tower.subextension T.twoBreak.b ∧
      chapter05LowerBreak T.tower.quotientSetup.downstairs T.twoBreak.a := by
  exact ⟨chapter05_two_break_subextension_has_lower_break_b H T,
    chapter05_two_break_quotient_has_lower_break_a H T⟩

theorem chapter05_two_break_tower_function_composition
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05TwoBreakTowerData G H)
    (hLK : Function.Bijective
      (chapter05HerbrandFunction T.tower.quotientSetup.upstairs))
    (hLM : Function.Bijective
      (chapter05HerbrandFunction T.tower.subextension))
    (hMK : Function.Bijective
      (chapter05HerbrandFunction T.tower.quotientSetup.downstairs))
    {u : ℝ} (hu : (-1 : ℝ) ≤ u) :
    chapter05HerbrandFunction T.tower.quotientSetup.upstairs u =
      chapter05HerbrandFunction T.tower.quotientSetup.downstairs
        (chapter05HerbrandFunction T.tower.subextension u) := by
  exact chapter05_herbrand_tower_transitivity H T.tower hLK hLM hMK hu

theorem chapter05_two_break_hasse_arf_congruence
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05TwoBreakTowerData G H)
    (hsecond : chapter05UpperBreakIsInteger
      (chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b)) :
    T.twoBreak.p ∣ T.twoBreak.b - T.twoBreak.a := by
  exact (chapter05_two_break_second_label_integral_iff_dvd
    T.twoBreak.p T.twoBreak.a T.twoBreak.b T.twoBreak.p_pos.pos T.twoBreak.a_lt_b).mp
      hsecond

end
end LastLib.Book03RamificationTheory.Chapter05
