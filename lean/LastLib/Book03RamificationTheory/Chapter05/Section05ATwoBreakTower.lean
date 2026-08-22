import LastLib.Book03RamificationTheory.Chapter05.Section04BreakConversionInExamples
import Mathlib.GroupTheory.PGroup

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
  p : ℕ
  a : ℕ
  b : ℕ
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

/- A genuine group of order p² is abelian.  The two-break profile above is
   intentionally more abstract, so this bridge is stated separately for the
   actual group-theoretic hypothesis used by the Hasse--Arf discussion. -/
theorem chapter05_two_break_group_is_commutative
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (D : Chapter05TwoBreakData G H) :
    IsMulCommutative G := by
  let _hprime : Fact (Nat.Prime D.p) := ⟨D.p_prime⟩
  exact IsPGroup.isMulCommutative_of_card_eq_prime_sq D.group_card

/-- The complete tower package needed to identify the subgroup and quotient stages. -/
structure Chapter05TwoBreakTowerData
    (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] where
  twoBreak : Chapter05TwoBreakData G H
  tower : Chapter05HerbrandTowerSetup G H
  top_profile_eq : tower.quotientSetup.upstairs = twoBreak.profile
  /- The quotient stage is itself totally ramified at depth zero.  Without
     this field, `quotient_first_layer` and `quotient_after_first_layer` also
     allow the downstairs profile to be trivial everywhere, so the claimed
     quotient break at `a` (and the asserted top/bottom upper groups) need not
     hold. -/
  quotient_zeroth_group_top :
    tower.quotientSetup.downstairs.lowerGroup 0 = ⊤
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
    (u : ℝ) :
    chapter05HerbrandFunction D.profile u =
      chapter05TwoBreakHerbrand D.p D.a D.b u := by
  have htop0 : D.profile.lowerGroup 0 = (⊤ : Subgroup G) := by
    exact D.lower_first_layer 0 (by norm_num) (by norm_num)
  have hp0 : (D.p : ℝ) ≠ 0 := by
    exact_mod_cast D.p_prime.ne_zero
  have hgroup_card : Fintype.card G = D.p ^ 2 := by
    simpa [Nat.card_eq_fintype_card] using D.group_card
  have hcast : ((D.b - D.a : ℕ) : ℝ) =
      (D.b : ℝ) - (D.a : ℝ) := by
    exact_mod_cast Nat.cast_sub D.a_lt_b.le
  have ha0 : (0 : ℝ) ≤ (D.a : ℝ) := by
    exact_mod_cast D.a_pos.le
  have hab : (D.a : ℝ) ≤ (D.b : ℝ) := by
    exact_mod_cast D.a_lt_b.le
  by_cases hu0 : u ≤ 0
  · simp [chapter05HerbrandFunction, chapter05TwoBreakHerbrand, hu0]
  · by_cases hua : u ≤ (D.a : ℝ)
    · rw [chapter05HerbrandFunction, if_neg hu0,
        chapter05TwoBreakHerbrand, if_neg hu0, if_pos hua]
      have hconst : Set.EqOn (chapter05HerbrandSlope D.profile)
          (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 u) := by
        intro t ht
        simp [chapter05HerbrandSlope,
          D.lower_first_layer t (le_of_lt ht.1)
            (le_of_lt (lt_of_lt_of_le ht.2 hua)),
          htop0, hgroup_card, hp0]
      rw [intervalIntegral.integral_congr_Ioo_of_le (le_of_not_ge hu0) hconst,
        intervalIntegral.integral_const]
      simp [smul_eq_mul]
    · by_cases hub : u ≤ (D.b : ℝ)
      · have hconst1 : Set.EqOn (chapter05HerbrandSlope D.profile)
            (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 (D.a : ℝ)) := by
          intro t ht
          simp [chapter05HerbrandSlope,
            D.lower_first_layer t (le_of_lt ht.1) (le_of_lt ht.2),
            htop0, hgroup_card, hp0]
        have hconst2 : Set.EqOn (chapter05HerbrandSlope D.profile)
            (fun _ : ℝ => (D.p : ℝ)⁻¹)
            (Set.Ioo (D.a : ℝ) u) := by
          intro t ht
          have ht0 : ¬t ≤ 0 := by
            have ha_pos : (0 : ℝ) < (D.a : ℝ) := by exact_mod_cast D.a_pos
            linarith [ht.1]
          simp [chapter05HerbrandSlope, ht0,
            D.lower_second_layer t ht.1
              (le_of_lt (lt_of_lt_of_le ht.2 hub)),
            htop0, hgroup_card, D.subgroup_card, div_eq_mul_inv];
            field_simp [hp0]
        have hconst1' : Set.EqOn (chapter05HerbrandSlope D.profile)
            (fun _ : ℝ => (1 : ℝ)) (Set.uIoo 0 (D.a : ℝ)) := by
          intro t ht
          apply hconst1
          simpa [Set.uIoo_of_le ha0] using ht
        have hconst2' : Set.EqOn (chapter05HerbrandSlope D.profile)
            (fun _ : ℝ => (D.p : ℝ)⁻¹) (Set.uIoo (D.a : ℝ) u) := by
          intro t ht
          apply hconst2
          simpa [Set.uIoo_of_le (le_of_not_ge hua)] using ht
        have hI1 :
            IntervalIntegrable (chapter05HerbrandSlope D.profile)
              MeasureTheory.volume 0 (D.a : ℝ) := by
          apply (intervalIntegrable_congr_uIoo hconst1').mpr
          exact intervalIntegrable_const
        have hI2 :
            IntervalIntegrable (chapter05HerbrandSlope D.profile)
              MeasureTheory.volume (D.a : ℝ) u := by
          apply (intervalIntegrable_congr_uIoo hconst2').mpr
          exact intervalIntegrable_const
        rw [chapter05HerbrandFunction, if_neg hu0,
          chapter05TwoBreakHerbrand, if_neg hu0, if_neg hua, if_pos hub]
        rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
        rw [intervalIntegral.integral_congr_Ioo_of_le ha0 hconst1,
          intervalIntegral.integral_congr_Ioo_of_le (le_of_not_ge hua) hconst2,
          intervalIntegral.integral_const, intervalIntegral.integral_const]
        simp [smul_eq_mul, div_eq_mul_inv]
      · have hbu : (D.b : ℝ) ≤ u := le_of_not_ge hub
        have hconst1 : Set.EqOn (chapter05HerbrandSlope D.profile)
            (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 (D.a : ℝ)) := by
          intro t ht
          simp [chapter05HerbrandSlope,
            D.lower_first_layer t (le_of_lt ht.1) (le_of_lt ht.2),
            htop0, hgroup_card, hp0]
        have hconst2 : Set.EqOn (chapter05HerbrandSlope D.profile)
            (fun _ : ℝ => (D.p : ℝ)⁻¹)
            (Set.Ioo (D.a : ℝ) (D.b : ℝ)) := by
          intro t ht
          have ht0 : ¬t ≤ 0 := by
            have ha_pos : (0 : ℝ) < (D.a : ℝ) := by exact_mod_cast D.a_pos
            linarith [ht.1]
          simp [chapter05HerbrandSlope, ht0,
            D.lower_second_layer t ht.1 (le_of_lt ht.2),
            htop0, hgroup_card, D.subgroup_card, div_eq_mul_inv];
            field_simp [hp0]
        have hconst3 : Set.EqOn (chapter05HerbrandSlope D.profile)
            (fun _ : ℝ => (D.p : ℝ)⁻¹ ^ 2)
            (Set.Ioo (D.b : ℝ) u) := by
          intro t ht
          have ht0 : ¬t ≤ 0 := by
            have hb_pos : (0 : ℝ) < (D.b : ℝ) := by
              exact lt_of_lt_of_le (by exact_mod_cast D.a_pos) hab
            linarith [ht.1]
          simp [chapter05HerbrandSlope, ht0,
            D.lower_after_second_layer t ht.1,
            htop0, hgroup_card, div_eq_mul_inv]
        have hconst1' : Set.EqOn (chapter05HerbrandSlope D.profile)
            (fun _ : ℝ => (1 : ℝ)) (Set.uIoo 0 (D.a : ℝ)) := by
          intro t ht
          apply hconst1
          simpa [Set.uIoo_of_le ha0] using ht
        have hconst2' : Set.EqOn (chapter05HerbrandSlope D.profile)
            (fun _ : ℝ => (D.p : ℝ)⁻¹)
            (Set.uIoo (D.a : ℝ) (D.b : ℝ)) := by
          intro t ht
          apply hconst2
          simpa [Set.uIoo_of_le hab] using ht
        have hconst3' : Set.EqOn (chapter05HerbrandSlope D.profile)
            (fun _ : ℝ => (D.p : ℝ)⁻¹ ^ 2)
            (Set.uIoo (D.b : ℝ) u) := by
          intro t ht
          apply hconst3
          simpa [Set.uIoo_of_le hbu] using ht
        have hI1 :
            IntervalIntegrable (chapter05HerbrandSlope D.profile)
              MeasureTheory.volume 0 (D.a : ℝ) := by
          apply (intervalIntegrable_congr_uIoo hconst1').mpr
          exact intervalIntegrable_const
        have hI2 :
            IntervalIntegrable (chapter05HerbrandSlope D.profile)
              MeasureTheory.volume (D.a : ℝ) (D.b : ℝ) := by
          apply (intervalIntegrable_congr_uIoo hconst2').mpr
          exact intervalIntegrable_const
        have hI3 :
            IntervalIntegrable (chapter05HerbrandSlope D.profile)
              MeasureTheory.volume (D.b : ℝ) u := by
          apply (intervalIntegrable_congr_uIoo hconst3').mpr
          exact intervalIntegrable_const
        rw [chapter05HerbrandFunction, if_neg hu0,
          chapter05TwoBreakHerbrand, if_neg hu0, if_neg hua, if_neg hub]
        rw [← intervalIntegral.integral_add_adjacent_intervals
              (hI1.trans hI2) hI3,
          ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
        rw [intervalIntegral.integral_congr_Ioo_of_le ha0 hconst1,
          intervalIntegral.integral_congr_Ioo_of_le hab hconst2,
          intervalIntegral.integral_congr_Ioo_of_le hbu hconst3,
          intervalIntegral.integral_const, intervalIntegral.integral_const,
          intervalIntegral.integral_const]
        simp [smul_eq_mul, div_eq_mul_inv, hcast]

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
  have ha0 : (0 : ℝ) ≤ (D.a : ℝ) := by
    exact_mod_cast D.a_pos.le
  have hab : (D.a : ℝ) ≤ (D.b : ℝ) := by
    exact_mod_cast D.a_lt_b.le
  have hcast : ((D.b - D.a : ℕ) : ℝ) =
      (D.b : ℝ) - (D.a : ℝ) := by
    exact_mod_cast Nat.cast_sub D.a_lt_b.le
  have hp0 : (0 : ℝ) < (D.p : ℝ) := by
    exact_mod_cast D.p_prime.pos
  have hcomp : (D.a : ℝ) <
        chapter05TwoBreakSecondUpper D.p D.a D.b ∧
      chapter05TwoBreakSecondUpper D.p D.a D.b < (D.b : ℝ) := by
    rw [chapter05TwoBreakSecondUpper]
    have hd : 0 < ((D.b - D.a : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt D.a_lt_b
    have hp1 : (1 : ℝ) < (D.p : ℝ) := by
      exact_mod_cast D.p_prime.one_lt
    constructor
    · exact lt_add_of_pos_right _ (div_pos hd hp0)
    · have hdiv : ((D.b - D.a : ℕ) : ℝ) / (D.p : ℝ) <
          ((D.b - D.a : ℕ) : ℝ) := by
        apply (div_lt_iff₀ hp0).2
        nlinarith
      have hcast' : (D.a : ℝ) + ((D.b - D.a : ℕ) : ℝ) = (D.b : ℝ) := by
        rw [Nat.cast_sub D.a_lt_b.le]
        ring
      rw [← hcast']
      simpa [add_comm] using add_lt_add_right hdiv (D.a : ℝ)
  have hformula : ∀ x : ℝ,
      chapter05HerbrandFunction D.profile x =
        chapter05TwoBreakHerbrand D.p D.a D.b x := by
    intro x
    exact chapter05_two_break_herbrand_formula H D x
  have hF_le : ∀ {x : ℝ}, x ≤ (D.a : ℝ) →
      chapter05HerbrandFunction D.profile x = x := by
    intro x hx
    rw [hformula x]
    by_cases hx0 : x ≤ 0
    · simp [chapter05TwoBreakHerbrand, hx0]
    · simp [chapter05TwoBreakHerbrand, hx0, hx]
  have hF_mid : ∀ {x : ℝ}, (D.a : ℝ) < x → x ≤ (D.b : ℝ) →
      chapter05HerbrandFunction D.profile x =
        (D.a : ℝ) + (x - (D.a : ℝ)) / (D.p : ℝ) := by
    intro x hxa hxb
    rw [hformula x]
    have hx0 : ¬x ≤ 0 := by
      have ha_pos : (0 : ℝ) < (D.a : ℝ) := by exact_mod_cast D.a_pos
      linarith
    simp [chapter05TwoBreakHerbrand, hx0, not_le.mpr hxa, hxb]
  have hF_gt : ∀ {x : ℝ}, (D.b : ℝ) < x →
      chapter05HerbrandFunction D.profile x =
        (D.a : ℝ) + ((D.b - D.a : ℕ) : ℝ) / (D.p : ℝ) +
          (x - (D.b : ℝ)) / (D.p : ℝ) ^ 2 := by
    intro x hxb
    rw [hformula x]
    have hxa : ¬x ≤ (D.a : ℝ) := by linarith [hab, hxb]
    have hb_pos : (0 : ℝ) < (D.b : ℝ) := by
      exact lt_of_lt_of_le (by exact_mod_cast D.a_pos) hab
    have hx0 : ¬x ≤ 0 := by linarith
    simp [chapter05TwoBreakHerbrand, hx0, hxa, hxb]
  have hFa : chapter05HerbrandFunction D.profile (D.a : ℝ) =
      (D.a : ℝ) := hF_le le_rfl
  have hFb : chapter05HerbrandFunction D.profile (D.b : ℝ) =
      chapter05TwoBreakSecondUpper D.p D.a D.b := by
    have h := hF_mid (x := (D.b : ℝ))
      (by exact_mod_cast D.a_lt_b) le_rfl
    simpa [chapter05TwoBreakSecondUpper, hcast] using h
  have hF_gt_a : ∀ {x : ℝ}, (D.a : ℝ) < x →
      (D.a : ℝ) < chapter05HerbrandFunction D.profile x := by
    intro x hxa
    by_cases hxb : x ≤ (D.b : ℝ)
    · rw [hF_mid hxa hxb]
      exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr hxa) hp0)
    · have hxb' : (D.b : ℝ) < x := lt_of_not_ge hxb
      rw [hF_gt hxb']
      have hpos : 0 < (x - (D.b : ℝ)) / (D.p : ℝ) ^ 2 := by
        exact div_pos (sub_pos.mpr hxb') (sq_pos_of_pos hp0)
      have hcpos : (D.a : ℝ) <
          (D.a : ℝ) + ((D.b - D.a : ℕ) : ℝ) / (D.p : ℝ) :=
        hcomp.1
      linarith
  have hF_gt_c : ∀ {x : ℝ}, (D.b : ℝ) < x →
      chapter05TwoBreakSecondUpper D.p D.a D.b <
        chapter05HerbrandFunction D.profile x := by
    intro x hxb
    rw [hF_gt hxb, chapter05TwoBreakSecondUpper]
    have hpos : 0 < (x - (D.b : ℝ)) / (D.p : ℝ) ^ 2 := by
      exact div_pos (sub_pos.mpr hxb) (sq_pos_of_pos hp0)
    linarith
  have hupper_top : ∀ {v : ℝ}, (-1 : ℝ) ≤ v → v ≤ (D.a : ℝ) →
      chapter05UpperRamificationGroup D.profile v = ⊤ := by
    intro v hv hvA
    have hvinv := chapter05_herbrand_inverse_spec D.profile hbij v
    have hinv_le : chapter05HerbrandInverse D.profile v ≤ (D.a : ℝ) := by
      by_contra hnot
      have hgt : (D.a : ℝ) < chapter05HerbrandInverse D.profile v :=
        lt_of_not_ge hnot
      have hgt' := hF_gt_a hgt
      linarith
    rw [chapter05UpperRamificationGroup, if_pos hv]
    by_cases hinv_neg : chapter05HerbrandInverse D.profile v < 0
    · have hinv_eq : chapter05HerbrandInverse D.profile v = v := by
        have hfx := hF_le hinv_le
        calc
          chapter05HerbrandInverse D.profile v =
              chapter05HerbrandFunction D.profile
                (chapter05HerbrandInverse D.profile v) := hfx.symm
          _ = v := hvinv
      rw [D.profile.lower_neg _ (by linarith) hinv_neg]
    · have hinv_nonneg : (0 : ℝ) ≤ chapter05HerbrandInverse D.profile v :=
        le_of_not_gt hinv_neg
      rw [D.lower_first_layer _ hinv_nonneg hinv_le]
  have hupper_mid : ∀ {v : ℝ}, (D.a : ℝ) < v →
      v ≤ chapter05TwoBreakSecondUpper D.p D.a D.b →
      chapter05UpperRamificationGroup D.profile v = H := by
    intro v hva hvc
    have hvinv := chapter05_herbrand_inverse_spec D.profile hbij v
    have hinv_gt : (D.a : ℝ) < chapter05HerbrandInverse D.profile v := by
      by_contra hnot
      have hinv_le := le_of_not_gt hnot
      have hfx := hF_le hinv_le
      linarith
    have hinv_le_b : chapter05HerbrandInverse D.profile v ≤ (D.b : ℝ) := by
      by_contra hnot
      have hinv_gt_b : (D.b : ℝ) < chapter05HerbrandInverse D.profile v :=
        lt_of_not_ge hnot
      have hgtc := hF_gt_c hinv_gt_b
      linarith
    have hvneg : (-1 : ℝ) ≤ v := by
      have ha0' : (0 : ℝ) ≤ (D.a : ℝ) := ha0
      linarith
    rw [chapter05UpperRamificationGroup, if_pos hvneg,
      D.lower_second_layer _ hinv_gt hinv_le_b]
  have hupper_bot : ∀ {v : ℝ},
      chapter05TwoBreakSecondUpper D.p D.a D.b < v →
      chapter05UpperRamificationGroup D.profile v = ⊥ := by
    intro v hvc
    have hvinv := chapter05_herbrand_inverse_spec D.profile hbij v
    have hinv_gt_b : (D.b : ℝ) < chapter05HerbrandInverse D.profile v := by
      by_contra hnot
      have hinv_le_b := le_of_not_gt hnot
      have hFle : chapter05HerbrandFunction D.profile
          (chapter05HerbrandInverse D.profile v) ≤
            chapter05TwoBreakSecondUpper D.p D.a D.b := by
        by_cases hinv_le_a :
            chapter05HerbrandInverse D.profile v ≤ (D.a : ℝ)
        · rw [hF_le hinv_le_a]
          linarith [hcomp.1]
        · have hinv_gt_a : (D.a : ℝ) <
              chapter05HerbrandInverse D.profile v := lt_of_not_ge hinv_le_a
          by_cases hinv_le_b' :
              chapter05HerbrandInverse D.profile v ≤ (D.b : ℝ)
          · rw [hF_mid hinv_gt_a hinv_le_b']
            have hdiv :
                (chapter05HerbrandInverse D.profile v - (D.a : ℝ)) / (D.p : ℝ) ≤
                  ((D.b - D.a : ℕ) : ℝ) / (D.p : ℝ) := by
              apply (div_le_div_iff_of_pos_right hp0).2
              rw [hcast]
              linarith
            rw [chapter05TwoBreakSecondUpper]
            linarith
          · exact False.elim (hnot (lt_of_not_ge hinv_le_b'))
      linarith
    have hvneg : (-1 : ℝ) ≤ v := by
      linarith [hcomp.1]
    rw [chapter05UpperRamificationGroup, if_pos hvneg,
      D.lower_after_second_layer _ hinv_gt_b]
  have hRight_top : ∀ {v : ℝ}, (-1 : ℝ) ≤ v → v < (D.a : ℝ) →
      chapter05UpperRightLimit D.profile v = ⊤ := by
    intro v hv hva
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      exact le_top
    · have hw : v < (v + (D.a : ℝ)) / 2 := by linarith
      have hwA : (v + (D.a : ℝ)) / 2 ≤ (D.a : ℝ) := by linarith
      have hmem : (⊤ : Subgroup G) ∈
          chapter05UpperRamificationGroup D.profile '' Set.Ioi v := by
        refine ⟨(v + (D.a : ℝ)) / 2, hw, ?_⟩
        exact hupper_top (by linarith) hwA
      exact le_sSup hmem
  have hRight_a :
      chapter05UpperRightLimit D.profile (D.a : ℝ) = H := by
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      rcases hK with ⟨w, hw, rfl⟩
      by_cases hwc : w ≤ chapter05TwoBreakSecondUpper D.p D.a D.b
      · rw [hupper_mid hw hwc]
      · rw [hupper_bot (lt_of_not_ge hwc)]
        exact bot_le
    · have hw : (D.a : ℝ) <
          ((D.a : ℝ) + chapter05TwoBreakSecondUpper D.p D.a D.b) / 2 := by
        linarith [hcomp.1]
      have hwc : ((D.a : ℝ) +
          chapter05TwoBreakSecondUpper D.p D.a D.b) / 2 ≤
            chapter05TwoBreakSecondUpper D.p D.a D.b := by
        linarith [hcomp.1]
      have hmem : H ∈
          chapter05UpperRamificationGroup D.profile ''
            Set.Ioi (D.a : ℝ) := by
        refine ⟨((D.a : ℝ) +
          chapter05TwoBreakSecondUpper D.p D.a D.b) / 2, hw, ?_⟩
        exact hupper_mid hw hwc
      exact le_sSup hmem
  have hRight_mid : ∀ {v : ℝ}, (D.a : ℝ) < v →
      v < chapter05TwoBreakSecondUpper D.p D.a D.b →
      chapter05UpperRightLimit D.profile v = H := by
    intro v hva hvc
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      rcases hK with ⟨w, hw, rfl⟩
      by_cases hwc : w ≤ chapter05TwoBreakSecondUpper D.p D.a D.b
      · rw [hupper_mid (lt_trans hva hw) hwc]
      · rw [hupper_bot (lt_of_not_ge hwc)]
        exact bot_le
    · have hw : v <
          (v + chapter05TwoBreakSecondUpper D.p D.a D.b) / 2 := by
        linarith
      have hwc : (v + chapter05TwoBreakSecondUpper D.p D.a D.b) / 2 ≤
          chapter05TwoBreakSecondUpper D.p D.a D.b := by
        linarith
      have hmem : H ∈
          chapter05UpperRamificationGroup D.profile '' Set.Ioi v := by
        refine ⟨(v + chapter05TwoBreakSecondUpper D.p D.a D.b) / 2, hw, ?_⟩
        exact hupper_mid (lt_trans hva hw) hwc
      exact le_sSup hmem
  have hRight_bot : ∀ {v : ℝ},
      chapter05TwoBreakSecondUpper D.p D.a D.b ≤ v →
      chapter05UpperRightLimit D.profile v = ⊥ := by
    intro v hvc
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      rcases hK with ⟨w, hw, rfl⟩
      rw [hupper_bot (lt_of_le_of_lt hvc hw)]
    · exact bot_le
  have hHtop : H ≠ (⊤ : Subgroup G) := by
    intro htop
    have hcard : D.p = D.p ^ 2 := by
      calc
        D.p = Nat.card H := D.subgroup_card.symm
        _ = Nat.card (⊤ : Subgroup G) :=
          congrArg (fun K : Subgroup G => Nat.card K) htop
        _ = Nat.card G := by simp
        _ = D.p ^ 2 := D.group_card
    nlinarith [D.p_prime.one_lt]
  have hHbot : H ≠ (⊥ : Subgroup G) := by
    intro hbot
    have hcard : 1 < Nat.card H := by
      rw [D.subgroup_card]
      exact D.p_prime.one_lt
    have hnontrivial : Nontrivial H :=
      (Finite.one_lt_card_iff_nontrivial).mp hcard
    obtain ⟨x, y, hxy⟩ := hnontrivial.exists_pair_ne
    have hxH : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact x.property
    have hyH : (y : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact y.property
    have hx1 : x = 1 := by
      apply Subtype.ext
      simpa using hxH
    have hy1 : y = 1 := by
      apply Subtype.ext
      simpa using hyH
    exact hxy (hx1.trans hy1.symm)
  have hbreak_a : chapter05UpperBreak D.profile (D.a : ℝ) := by
    rw [chapter05UpperBreak]
    refine ⟨by linarith, ?_⟩
    have ha_ne : (D.a : ℝ) ≠ (-1 : ℝ) := by
      have ha_pos : (0 : ℝ) < (D.a : ℝ) := by exact_mod_cast D.a_pos
      linarith
    rw [if_neg ha_ne, hupper_top (by linarith) le_rfl, hRight_a]
    exact Ne.symm hHtop
  have hbreak_c : chapter05UpperBreak D.profile
      (chapter05TwoBreakSecondUpper D.p D.a D.b) := by
    rw [chapter05UpperBreak]
    refine ⟨by linarith [hcomp.1], ?_⟩
    have hc_ne : chapter05TwoBreakSecondUpper D.p D.a D.b ≠
        (-1 : ℝ) := by
      have hc_pos : (0 : ℝ) <
          chapter05TwoBreakSecondUpper D.p D.a D.b :=
        lt_of_le_of_lt ha0 hcomp.1
      linarith
    rw [if_neg hc_ne, hupper_mid hcomp.1 le_rfl,
      hRight_bot le_rfl]
    exact hHbot
  refine ⟨hbreak_a, hbreak_c, ?_⟩
  intro v hv
  rw [chapter05UpperBreak] at hv
  rcases hv with ⟨hvneg, hvcond⟩
  by_cases hvminus : v = (-1 : ℝ)
  · exfalso
    have hzero : D.profile.lowerGroup 0 = (⊤ : Subgroup G) := by
      exact D.lower_first_layer 0 (by norm_num) (by norm_num)
    simp [hvminus, hzero] at hvcond
  have hvcond' : chapter05UpperRamificationGroup D.profile v ≠
      chapter05UpperRightLimit D.profile v := by
    simpa [hvminus] using hvcond
  by_cases hva : v < (D.a : ℝ)
  · exfalso
    apply hvcond'
    rw [hupper_top hvneg (le_of_lt hva), hRight_top hvneg hva]
  by_cases hva_eq : v = (D.a : ℝ)
  · exact Or.inl hva_eq
  have hva' : (D.a : ℝ) < v := lt_of_le_of_ne
    (le_of_not_gt hva) (Ne.symm hva_eq)
  by_cases hvc : v < chapter05TwoBreakSecondUpper D.p D.a D.b
  · exfalso
    apply hvcond'
    rw [hupper_mid hva' (le_of_lt hvc), hRight_mid hva' hvc]
  by_cases hvc_eq : v = chapter05TwoBreakSecondUpper D.p D.a D.b
  · exact Or.inr hvc_eq
  have hvc' : chapter05TwoBreakSecondUpper D.p D.a D.b < v :=
    lt_of_le_of_ne (le_of_not_gt hvc) (Ne.symm hvc_eq)
  exfalso
  apply hvcond'
  rw [hupper_bot hvc', hRight_bot hvc'.le]

/- The displayed arithmetic expression can be fractional for an abstract
   piecewise profile.  In an actual Galois extension with `|G| = p^2`, the
   group is abelian and, with perfect residue field, Hasse--Arf forces the
   second upper label to be integral.  The declarations below keep those two
   assertions separate. -/
theorem chapter05_two_break_second_label_nonintegral_of_not_dvd
    (p a b : ℕ) (hp : 0 < p) (hab : a < b)
    (hndvd : ¬p ∣ b - a) :
    ¬chapter05UpperBreakIsInteger (chapter05TwoBreakSecondUpper p a b) := by
  intro h
  rcases h with ⟨z, hz⟩
  rw [chapter05TwoBreakSecondUpper] at hz
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp)
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := by
    exact_mod_cast Nat.cast_sub hab.le
  have hz' : (z : ℝ) * (p : ℝ) =
      (a : ℝ) * (p : ℝ) + (b - a : ℕ) := by
    field_simp [hp0] at hz
    nlinarith [hz, hcast]
  have hz_int : z * (p : ℤ) =
      (a : ℤ) * (p : ℤ) + (b - a : ℕ) := by
    exact_mod_cast hz'
  have hd_int : (b - a : ℕ) = (z - (a : ℤ)) * (p : ℤ) := by
    nlinarith [hz_int]
  apply hndvd
  refine Int.natCast_dvd_natCast.mp ?_
  refine ⟨z - (a : ℤ), ?_⟩
  rw [hd_int]
  ring

theorem chapter05_two_break_second_label_integral_iff_dvd
    (p a b : ℕ) (hp : 0 < p) (hab : a < b) :
    chapter05UpperBreakIsInteger (chapter05TwoBreakSecondUpper p a b) ↔
      p ∣ b - a := by
  constructor
  · rintro ⟨z, hz⟩
    rw [chapter05TwoBreakSecondUpper] at hz
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hp)
    have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := by
      exact_mod_cast Nat.cast_sub hab.le
    have hz' : (z : ℝ) * (p : ℝ) =
        (a : ℝ) * (p : ℝ) + (b - a : ℕ) := by
      field_simp [hp0] at hz
      nlinarith [hz, hcast]
    have hz_int : z * (p : ℤ) =
        (a : ℤ) * (p : ℤ) + (b - a : ℕ) := by
      exact_mod_cast hz'
    have hd_int : (b - a : ℕ) = (z - (a : ℤ)) * (p : ℤ) := by
      nlinarith [hz_int]
    refine Int.natCast_dvd_natCast.mp ?_
    refine ⟨z - (a : ℤ), ?_⟩
    rw [hd_int]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨(a + k : ℕ), ?_⟩
    rw [chapter05TwoBreakSecondUpper]
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hp)
    have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := by
      exact_mod_cast Nat.cast_sub hab.le
    have hreal : (b : ℝ) - (a : ℝ) = (p : ℝ) * (k : ℝ) := by
      rw [← hcast]
      exact_mod_cast hk
    rw [hcast, hreal]
    field_simp [hp0]
    norm_num

theorem chapter05_two_break_upper_label_is_strictly_compressed
    (p a b : ℕ) (hp : Nat.Prime p) (hab : a < b) :
    (a : ℝ) < chapter05TwoBreakSecondUpper p a b ∧
      chapter05TwoBreakSecondUpper p a b < (b : ℝ) := by
  rw [chapter05TwoBreakSecondUpper]
  have hd : 0 < ((b - a : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hab
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  constructor
  · exact lt_add_of_pos_right _ (div_pos hd hp0)
  · have hdiv : ((b - a : ℕ) : ℝ) / (p : ℝ) < ((b - a : ℕ) : ℝ) := by
      apply (div_lt_iff₀ hp0).2
      nlinarith
    have hcast : (a : ℝ) + ((b - a : ℕ) : ℝ) = (b : ℝ) := by
      rw [Nat.cast_sub hab.le]
      ring
    rw [← hcast]
    simpa [add_comm] using add_lt_add_right hdiv (a : ℝ)

theorem chapter05_two_break_subextension_has_lower_break_b
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05TwoBreakTowerData G H) :
    chapter05LowerBreak T.tower.subextension T.twoBreak.b := by
  rw [chapter05LowerBreak]
  have hb : (-1 : ℝ) ≤ (T.twoBreak.b : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ (T.twoBreak.b : ℝ) := by positivity
    linarith
  have hb1 : (-1 : ℝ) ≤ ((T.twoBreak.b + 1 : ℕ) : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ ((T.twoBreak.b + 1 : ℕ) : ℝ) := by positivity
    linarith
  rw [T.tower.subgroup_lower_formula (T.twoBreak.b : ℝ) hb,
    T.tower.subgroup_lower_formula ((T.twoBreak.b + 1 : ℕ) : ℝ) hb1]
  rw [T.top_profile_eq]
  rw [T.twoBreak.lower_second_layer (T.twoBreak.b : ℝ)
    (by exact_mod_cast T.twoBreak.a_lt_b) (by norm_num)]
  rw [T.twoBreak.lower_after_second_layer ((T.twoBreak.b + 1 : ℕ) : ℝ)
    (by norm_num)]
  have hcard : 1 < Nat.card H := by
    rw [T.twoBreak.subgroup_card]
    exact T.twoBreak.p_prime.one_lt
  have hnontrivial : Nontrivial H :=
    (Finite.one_lt_card_iff_nontrivial).mp hcard
  have htop : (⊤ : Subgroup H) ≠ ⊥ := by
    intro htop
    obtain ⟨x, y, hxy⟩ := hnontrivial.exists_pair_ne
    have hx : x ∈ (⊥ : Subgroup H) := by
      rw [← htop]
      trivial
    have hy : y ∈ (⊥ : Subgroup H) := by
      rw [← htop]
      trivial
    have hx1 : x = 1 := by simpa using hx
    have hy1 : y = 1 := by simpa using hy
    exact hxy (hx1.trans hy1.symm)
  rw [Subgroup.comap_subtype, Subgroup.subgroupOf_self,
    MonoidHom.comap_bot, Subgroup.ker_subtype]
  exact htop

theorem chapter05_two_break_quotient_has_lower_break_a
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal]
    (T : Chapter05TwoBreakTowerData G H) :
    chapter05LowerBreak T.tower.quotientSetup.downstairs T.twoBreak.a := by
  rw [chapter05LowerBreak]
  have ha_nonneg : (0 : ℝ) ≤ (T.twoBreak.a : ℝ) := by positivity
  rw [T.quotient_first_layer (T.twoBreak.a : ℝ) ha_nonneg le_rfl,
    T.quotient_zeroth_group_top,
    T.quotient_after_first_layer ((T.twoBreak.a + 1 : ℕ) : ℝ) (by norm_num)]
  have hidx : H.index = T.twoBreak.p := by
    have hmul := H.index_mul_card
    rw [T.twoBreak.group_card, T.twoBreak.subgroup_card] at hmul
    nlinarith [T.twoBreak.p_prime.pos]
  have hqcard : 1 < Nat.card (G ⧸ H) := by
    rw [← H.index_eq_card, hidx]
    exact T.twoBreak.p_prime.one_lt
  have hnontrivial : Nontrivial (G ⧸ H) :=
    (Finite.one_lt_card_iff_nontrivial).mp hqcard
  have htop : (⊤ : Subgroup (G ⧸ H)) ≠ ⊥ := by
    intro htop
    obtain ⟨x, y, hxy⟩ := hnontrivial.exists_pair_ne
    have hx : x ∈ (⊥ : Subgroup (G ⧸ H)) := by
      rw [← htop]
      trivial
    have hy : y ∈ (⊥ : Subgroup (G ⧸ H)) := by
      rw [← htop]
      trivial
    have hx1 : x = 1 := by simpa using hx
    have hy1 : y = 1 := by simpa using hy
    exact hxy (hx1.trans hy1.symm)
  exact htop

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
  classical
  let D := T.tower.quotientSetup.downstairs
  have ha0 : (0 : ℝ) ≤ (T.twoBreak.a : ℝ) := by positivity
  have htop0 : D.lowerGroup 0 = (⊤ : Subgroup (G ⧸ H)) := by
    simpa [D] using T.quotient_zeroth_group_top
  have hF_le : ∀ {x : ℝ}, x ≤ (T.twoBreak.a : ℝ) →
      chapter05HerbrandFunction D x = x := by
    intro x hx
    by_cases hx0 : x ≤ 0
    · simp [chapter05HerbrandFunction, hx0]
    · rw [chapter05HerbrandFunction, if_neg hx0]
      have hconst : Set.EqOn (chapter05HerbrandSlope D)
          (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 x) := by
        intro t ht
        have ht0 : ¬t ≤ 0 := not_le.mpr ht.1
        have hgroup : D.lowerGroup t = D.lowerGroup 0 := by
          simpa [D] using T.quotient_first_layer t (le_of_lt ht.1)
            (le_trans ht.2.le hx)
        simp [chapter05HerbrandSlope, ht0, hgroup, htop0]
      rw [intervalIntegral.integral_congr_Ioo_of_le (le_of_not_ge hx0) hconst,
        intervalIntegral.integral_const]
      simp [smul_eq_mul]
  have hF_gt_a : ∀ {x : ℝ}, (T.twoBreak.a : ℝ) < x →
      (T.twoBreak.a : ℝ) < chapter05HerbrandFunction D x := by
    intro x hxa
    have hx0 : ¬x ≤ 0 := by linarith
    have hconst1 : Set.EqOn (chapter05HerbrandSlope D)
        (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 (T.twoBreak.a : ℝ)) := by
      intro t ht
      have ht0 : ¬t ≤ 0 := not_le.mpr ht.1
      have hgroup : D.lowerGroup t = D.lowerGroup 0 := by
        simpa [D] using T.quotient_first_layer t (le_of_lt ht.1) ht.2.le
      simp [chapter05HerbrandSlope, ht0, hgroup, htop0]
    have hconst2 : Set.EqOn (chapter05HerbrandSlope D)
        (fun _ : ℝ => (1 : ℝ) /
          (Nat.card (D.lowerGroup 0) : ℝ))
        (Set.Ioo (T.twoBreak.a : ℝ) x) := by
      intro t ht
      have ht0 : ¬t ≤ 0 := by linarith [ha0, ht.1]
      have hgroup : D.lowerGroup t = (⊥ : Subgroup (G ⧸ H)) := by
        simpa [D] using T.quotient_after_first_layer t ht.1
      simp [chapter05HerbrandSlope, ht0, hgroup, htop0]
    have hconst1' : Set.EqOn (chapter05HerbrandSlope D)
        (fun _ : ℝ => (1 : ℝ))
        (Set.uIoo 0 (T.twoBreak.a : ℝ)) := by
      intro t ht
      apply hconst1
      simpa [Set.uIoo_of_le ha0] using ht
    have hconst2' : Set.EqOn (chapter05HerbrandSlope D)
        (fun _ : ℝ => (1 : ℝ) /
          (Nat.card (D.lowerGroup 0) : ℝ))
        (Set.uIoo (T.twoBreak.a : ℝ) x) := by
      intro t ht
      apply hconst2
      simpa [Set.uIoo_of_le (le_of_lt hxa)] using ht
    have hI1 : IntervalIntegrable (chapter05HerbrandSlope D)
        MeasureTheory.volume 0 (T.twoBreak.a : ℝ) := by
      apply (intervalIntegrable_congr_uIoo hconst1').mpr
      exact intervalIntegrable_const
    have hI2 : IntervalIntegrable (chapter05HerbrandSlope D)
        MeasureTheory.volume (T.twoBreak.a : ℝ) x := by
      apply (intervalIntegrable_congr_uIoo hconst2').mpr
      exact intervalIntegrable_const
    rw [chapter05HerbrandFunction, if_neg hx0]
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2,
      intervalIntegral.integral_congr_Ioo_of_le ha0 hconst1,
      intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hxa) hconst2,
      intervalIntegral.integral_const, intervalIntegral.integral_const]
    have hden : 0 < (Nat.card (D.lowerGroup 0) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hpos : 0 < (x - (T.twoBreak.a : ℝ)) /
        (Nat.card (D.lowerGroup 0) : ℝ) :=
      div_pos (sub_pos.mpr hxa) hden
    have hpos' : 0 < (x - (T.twoBreak.a : ℝ)) *
        (Nat.card (D.lowerGroup 0) : ℝ)⁻¹ := by
      simpa [div_eq_mul_inv] using hpos
    simpa [smul_eq_mul, div_eq_mul_inv, Nat.card_eq_fintype_card] using
      (lt_add_of_pos_right (T.twoBreak.a : ℝ) hpos')
  have hupper_top : ∀ {v : ℝ}, (-1 : ℝ) ≤ v →
      v ≤ (T.twoBreak.a : ℝ) →
      chapter05UpperRamificationGroup D v = ⊤ := by
    intro v hv hvA
    have hvinv := chapter05_herbrand_inverse_spec D hbij v
    have hinv_le : chapter05HerbrandInverse D v ≤ (T.twoBreak.a : ℝ) := by
      by_contra hnot
      have hgt : (T.twoBreak.a : ℝ) < chapter05HerbrandInverse D v :=
        lt_of_not_ge hnot
      linarith [hF_gt_a hgt]
    rw [chapter05UpperRamificationGroup, if_pos hv]
    by_cases hinv_neg : chapter05HerbrandInverse D v < 0
    · have hinv_eq : chapter05HerbrandInverse D v = v := by
        calc
          chapter05HerbrandInverse D v =
              chapter05HerbrandFunction D (chapter05HerbrandInverse D v) :=
            (hF_le hinv_le).symm
          _ = v := hvinv
      rw [D.lower_neg _ (by linarith) hinv_neg]
    · have hinv_nonneg : (0 : ℝ) ≤ chapter05HerbrandInverse D v :=
        le_of_not_gt hinv_neg
      rw [show D.lowerGroup (chapter05HerbrandInverse D v) =
          D.lowerGroup 0 by
            simpa [D] using T.quotient_first_layer _ hinv_nonneg hinv_le]
      exact htop0
  have hupper_bot : ∀ {v : ℝ}, (T.twoBreak.a : ℝ) < v →
      chapter05UpperRamificationGroup D v = ⊥ := by
    intro v hva
    have hvinv := chapter05_herbrand_inverse_spec D hbij v
    have hinv_gt : (T.twoBreak.a : ℝ) < chapter05HerbrandInverse D v := by
      by_contra hnot
      have hinv_le := le_of_not_gt hnot
      linarith [hF_le hinv_le]
    have hvneg : (-1 : ℝ) ≤ v := by linarith [ha0, hva]
    rw [chapter05UpperRamificationGroup, if_pos hvneg]
    simpa [D] using T.quotient_after_first_layer
      (chapter05HerbrandInverse D v) hinv_gt
  constructor
  · intro v hv0 hvA
    simpa [D] using hupper_top (by linarith) hvA
  · intro v hvA
    simpa [D] using hupper_bot hvA

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
    {u : ℝ} :
    chapter05HerbrandFunction T.tower.quotientSetup.upstairs u =
      chapter05HerbrandFunction T.tower.quotientSetup.downstairs
        (chapter05HerbrandFunction T.tower.subextension u) := by
  exact chapter05_herbrand_tower_transitivity H T.tower

theorem chapter05_two_break_integral_second_label_implies_dvd
    (p a b : ℕ) (hp : 0 < p) (hab : a < b)
    (hsecond : chapter05UpperBreakIsInteger
      (chapter05TwoBreakSecondUpper p a b)) :
    p ∣ b - a := by
  exact (chapter05_two_break_second_label_integral_iff_dvd p a b hp hab).mp hsecond

end
end LastLib.Book03RamificationTheory.Chapter05
