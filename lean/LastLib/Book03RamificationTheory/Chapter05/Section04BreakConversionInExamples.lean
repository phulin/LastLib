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
  group_card : Nat.card G = p
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
    (_hintegrable : ∀ a b : ℝ,
      IntervalIntegrable (chapter05HerbrandSlope D.profile) volume a b)
    (u : ℝ) :
    chapter05HerbrandFunction D.profile u =
      chapter05SingleBreakHerbrand D.p D.m u := by
  by_cases hu0 : u ≤ 0
  · simp [chapter05HerbrandFunction, chapter05SingleBreakHerbrand, hu0]
  · by_cases hum : u ≤ (D.m : ℝ)
    · rw [chapter05HerbrandFunction, if_neg hu0,
        chapter05SingleBreakHerbrand, if_neg hu0, if_pos hum]
      have hconst : Set.EqOn (chapter05HerbrandSlope D.profile)
          (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 u) := by
        intro t ht
        simp [chapter05HerbrandSlope,
          D.lower_through_break t (le_of_lt ht.1)
            (le_of_lt (lt_of_lt_of_le ht.2 hum)), D.zeroth_card,
          D.p_prime.ne_zero]
      rw [intervalIntegral.integral_congr_Ioo_of_le (le_of_not_ge hu0) hconst,
        intervalIntegral.integral_const]
      simp [smul_eq_mul]
    · have hmu : (D.m : ℝ) ≤ u := le_of_not_ge hum
      rw [chapter05HerbrandFunction, if_neg hu0,
        chapter05SingleBreakHerbrand, if_neg hu0, if_neg hum]
      have hconst1 : Set.EqOn (chapter05HerbrandSlope D.profile)
          (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 (D.m : ℝ)) := by
        intro t ht
        simp [chapter05HerbrandSlope,
          D.lower_through_break t (le_of_lt ht.1) (le_of_lt ht.2),
          D.zeroth_card, D.p_prime.ne_zero]
      have hconst2 : Set.EqOn (chapter05HerbrandSlope D.profile)
          (fun _ : ℝ => (D.p : ℝ)⁻¹) (Set.Ioo (D.m : ℝ) u) := by
        intro t ht
        have ht0 : ¬t ≤ 0 := by
          have hm0 : (0 : ℝ) < (D.m : ℝ) := by exact_mod_cast D.m_pos
          linarith [ht.1]
        simp [chapter05HerbrandSlope,
          D.lower_after_break t ht.1, D.zeroth_card,
          div_eq_mul_inv, ht0]
      have hconst1' : Set.EqOn (chapter05HerbrandSlope D.profile)
          (fun _ : ℝ => (1 : ℝ)) (Set.uIoo 0 (D.m : ℝ)) := by
        intro t ht
        apply hconst1
        simpa [Set.uIoo_of_le (by exact_mod_cast D.m_pos.le)] using ht
      have hconst2' : Set.EqOn (chapter05HerbrandSlope D.profile)
          (fun _ : ℝ => (D.p : ℝ)⁻¹) (Set.uIoo (D.m : ℝ) u) := by
        intro t ht
        apply hconst2
        simpa [Set.uIoo_of_le hmu] using ht
      have hI1 :
          IntervalIntegrable (chapter05HerbrandSlope D.profile)
            MeasureTheory.volume 0 (D.m : ℝ) := by
        apply (intervalIntegrable_congr_uIoo hconst1').mpr
        exact intervalIntegrable_const
      have hI2 :
          IntervalIntegrable (chapter05HerbrandSlope D.profile)
            MeasureTheory.volume (D.m : ℝ) u := by
        apply (intervalIntegrable_congr_uIoo hconst2').mpr
        exact intervalIntegrable_const
      rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
      rw [intervalIntegral.integral_congr_Ioo_of_le
          (by exact_mod_cast D.m_pos.le) hconst1,
        intervalIntegral.integral_congr_Ioo_of_le hmu hconst2,
        intervalIntegral.integral_const, intervalIntegral.integral_const]
      simp [smul_eq_mul, div_eq_mul_inv]

theorem chapter05_single_wild_break_upper_label_is_the_same
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05SingleWildBreakData G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D.profile))
    (_hintegrable : ∀ a b : ℝ,
      IntervalIntegrable (chapter05HerbrandSlope D.profile) volume a b) :
    chapter05UpperBreak D.profile (D.m : ℝ) ∧
      chapter05HerbrandFunction D.profile (D.m : ℝ) = (D.m : ℝ) ∧
      ∀ v : ℝ, chapter05UpperBreak D.profile v → v = (D.m : ℝ) := by
  have htop0 : D.profile.lowerGroup 0 = (⊤ : Subgroup G) := by
    apply Subgroup.eq_top_of_card_eq
    rw [D.zeroth_card, D.group_card]
  have hformula : ∀ x : ℝ,
      chapter05HerbrandFunction D.profile x =
        chapter05SingleBreakHerbrand D.p D.m x := by
    intro x
    exact chapter05_single_wild_break_herbrand_formula D (volume := 0)
      (by
        intro a' b'
        exact (intervalIntegrable_iff).2
          (_root_.MeasureTheory.IntegrableOn.of_measure_zero (by simp))) x
  have hm0 : (0 : ℝ) ≤ (D.m : ℝ) := by
    exact_mod_cast D.m_pos.le
  have hF_le : ∀ {x : ℝ}, x ≤ (D.m : ℝ) →
      chapter05HerbrandFunction D.profile x = x := by
    intro x hx
    rw [hformula x]
    by_cases hx0 : x ≤ 0
    · simp [chapter05SingleBreakHerbrand, hx0]
    · simp [chapter05SingleBreakHerbrand, hx0, hx]
  have hF_gt : ∀ {x : ℝ}, (D.m : ℝ) < x →
      chapter05HerbrandFunction D.profile x =
        (D.m : ℝ) + (x - (D.m : ℝ)) / (D.p : ℝ) := by
    intro x hxm
    rw [hformula x]
    have hx0 : ¬x ≤ 0 := by
      have hmpos : (0 : ℝ) < (D.m : ℝ) := by exact_mod_cast D.m_pos
      linarith
    simp [chapter05SingleBreakHerbrand, hx0, not_le.mpr hxm]
  have hp0 : (0 : ℝ) < (D.p : ℝ) := by
    exact_mod_cast D.p_prime.pos
  have htopbot : (⊤ : Subgroup G) ≠ ⊥ := by
    have hcard : 1 < Nat.card G := by
      rw [D.group_card]
      exact D.p_prime.one_lt
    have hnontrivial : Nontrivial G :=
      (Finite.one_lt_card_iff_nontrivial).mp hcard
    intro h
    obtain ⟨x, y, hxy⟩ := hnontrivial.exists_pair_ne
    have hx : x ∈ (⊥ : Subgroup G) := by
      rw [← h]
      trivial
    have hy : y ∈ (⊥ : Subgroup G) := by
      rw [← h]
      trivial
    have hx1 : x = 1 := by simpa using hx
    have hy1 : y = 1 := by simpa using hy
    exact hxy (hx1.trans hy1.symm)
  have hupper_top : ∀ {v : ℝ}, (-1 : ℝ) ≤ v → v ≤ (D.m : ℝ) →
      chapter05UpperRamificationGroup D.profile v = ⊤ := by
    intro v hv hvm
    have hvinv := chapter05_herbrand_inverse_spec D.profile hbij v
    have hinv_le : chapter05HerbrandInverse D.profile v ≤ (D.m : ℝ) := by
      by_contra hnot
      have hgt : (D.m : ℝ) < chapter05HerbrandInverse D.profile v :=
        lt_of_not_ge hnot
      have hfx := hF_gt hgt
      have hpos : 0 <
          (chapter05HerbrandInverse D.profile v - (D.m : ℝ)) /
            (D.p : ℝ) := div_pos (sub_pos.mpr hgt) hp0
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
      rw [D.lower_through_break _ hinv_nonneg hinv_le, htop0]
  have hupper_bot : ∀ {v : ℝ}, (D.m : ℝ) < v →
      chapter05UpperRamificationGroup D.profile v = ⊥ := by
    intro v hvm
    have hvinv := chapter05_herbrand_inverse_spec D.profile hbij v
    have hinv_gt : (D.m : ℝ) < chapter05HerbrandInverse D.profile v := by
      by_contra hnot
      have hinv_le := le_of_not_gt hnot
      have hfx := hF_le hinv_le
      linarith
    rw [chapter05UpperRamificationGroup, if_pos (by linarith),
      D.lower_after_break _ hinv_gt]
  have hRight_top : ∀ {v : ℝ}, (-1 : ℝ) ≤ v → v < (D.m : ℝ) →
      chapter05UpperRightLimit D.profile v = ⊤ := by
    intro v hv hvm
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      exact le_top
    · have hw : v < (v + (D.m : ℝ)) / 2 := by linarith
      have hwM : (v + (D.m : ℝ)) / 2 ≤ (D.m : ℝ) := by linarith
      have hmem : (⊤ : Subgroup G) ∈
          chapter05UpperRamificationGroup D.profile '' Set.Ioi v := by
        refine ⟨(v + (D.m : ℝ)) / 2, hw, hupper_top (by linarith) hwM⟩
      exact le_sSup hmem
  have hRight_bot : ∀ {v : ℝ}, (D.m : ℝ) ≤ v →
      chapter05UpperRightLimit D.profile v = ⊥ := by
    intro v hvm
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      rcases hK with ⟨w, hw, rfl⟩
      rw [hupper_bot (lt_of_le_of_lt hvm hw)]
    · exact bot_le
  have hbreak_m : chapter05UpperBreak D.profile (D.m : ℝ) := by
    rw [chapter05UpperBreak]
    refine ⟨by linarith, ?_⟩
    have hm_ne : (D.m : ℝ) ≠ (-1 : ℝ) := by
      have hmpos : (0 : ℝ) < (D.m : ℝ) := by exact_mod_cast D.m_pos
      linarith
    rw [if_neg hm_ne, hupper_top (by linarith) le_rfl,
      hRight_bot le_rfl]
    exact htopbot
  refine ⟨hbreak_m, hF_le le_rfl, ?_⟩
  intro v hv
  rw [chapter05UpperBreak] at hv
  rcases hv with ⟨hvneg, hvcond⟩
  by_cases hvminus : v = (-1 : ℝ)
  · exfalso
    simp [hvminus, htop0] at hvcond
  have hvcond' : chapter05UpperRamificationGroup D.profile v ≠
      chapter05UpperRightLimit D.profile v := by
    simpa [hvminus] using hvcond
  by_cases hvm : v < (D.m : ℝ)
  · exfalso
    apply hvcond'
    rw [hupper_top hvneg (le_of_lt hvm), hRight_top hvneg hvm]
  by_cases hvm_eq : v = (D.m : ℝ)
  · exact hvm_eq
  have hvm' : (D.m : ℝ) < v :=
    lt_of_le_of_ne (le_of_not_gt hvm) (Ne.symm hvm_eq)
  exfalso
  apply hvcond'
  rw [hupper_bot hvm', hRight_bot hvm'.le]

/-- A tame layer has constant positive slope `1/e`. -/
theorem chapter05_tame_herbrand_slope
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) (he : 0 < e)
    (hcard : Nat.card (D.lowerGroup 0) = e)
    (htrivial : ∀ u : ℝ, 0 < u → D.lowerGroup u = ⊥) :
    ∀ u : ℝ, 0 < u → chapter05HerbrandSlope D u = (e : ℝ)⁻¹ := by
  intro u hu
  have he0 : (e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt he)
  rw [chapter05HerbrandSlope, if_neg (not_le.mpr hu), htrivial u hu, hcard]
  field_simp [he0]
  simp

/-- The Herbrand function for a tame totally ramified group of order `e`. -/
theorem chapter05_tame_herbrand_formula
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) (he : 0 < e)
    (hcard : Nat.card (D.lowerGroup 0) = e)
    (_htotal : Nat.card G = e)
    (htrivial : ∀ u : ℝ, 0 < u → D.lowerGroup u = ⊥)
    (_hintegrable : ∀ a b : ℝ,
      IntervalIntegrable (chapter05HerbrandSlope D) volume a b)
    (u : ℝ) :
    chapter05HerbrandFunction D u = chapter05TameHerbrand e u := by
  by_cases hu : u ≤ 0
  · simp [chapter05HerbrandFunction, chapter05TameHerbrand, hu]
  · have hu' : 0 < u := lt_of_not_ge hu
    rw [chapter05HerbrandFunction, if_neg hu, chapter05TameHerbrand, if_neg hu]
    have hconst : Set.EqOn (chapter05HerbrandSlope D)
        (fun _ : ℝ => (e : ℝ)⁻¹) (Set.Ioo 0 u) := by
      intro t ht
      exact chapter05_tame_herbrand_slope D e he hcard htrivial t ht.1
    rw [intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hu') hconst]
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul, div_eq_mul_inv]

/-- Positive upper groups vanish immediately after zero in the tame case. -/
theorem chapter05_tame_upper_groups_drop_after_zero
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) (_he : 0 < e)
    (_hcard : Nat.card (D.lowerGroup 0) = e)
    (_htotal : Nat.card G = e)
    (htrivial : ∀ u : ℝ, 0 < u → D.lowerGroup u = ⊥)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    ∀ v : ℝ, 0 < v → chapter05UpperRamificationGroup D v = ⊥ := by
  intro v hv
  have hvinv := chapter05_herbrand_inverse_spec D hbij v
  have hinv_pos : 0 < chapter05HerbrandInverse D v := by
    by_contra hnot
    have hinv_le : chapter05HerbrandInverse D v ≤ 0 := le_of_not_gt hnot
    have hfx := chapter05_herbrand_function_of_nonpositive D hinv_le
    rw [hfx] at hvinv
    linarith
  rw [chapter05UpperRamificationGroup, if_pos (by linarith),
    htrivial _ hinv_pos]

theorem chapter05_tame_has_only_zero_break
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) (he : 1 < e)
    (hcard : Nat.card (D.lowerGroup 0) = e)
    (htotal : Nat.card G = e)
    (htrivial : ∀ u : ℝ, 0 < u → D.lowerGroup u = ⊥)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (hzero : D.lowerGroup 0 ≠ ⊥) :
    chapter05UpperBreak D 0 ∧
      ∀ v : ℝ, v ≠ 0 → ¬chapter05UpperBreak D v := by
  have htop0 : D.lowerGroup 0 = (⊤ : Subgroup G) := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, htotal]
  have htame : ∀ x : ℝ,
      chapter05HerbrandFunction D x = chapter05TameHerbrand e x := by
    intro x
    exact chapter05_tame_herbrand_formula D e (by omega) hcard htotal
      htrivial (volume := 0)
      (by
        intro a' b'
        exact (intervalIntegrable_iff).2
          (_root_.MeasureTheory.IntegrableOn.of_measure_zero (by simp))) x
  have hupper_neg : ∀ {v : ℝ}, (-1 : ℝ) ≤ v → v < 0 →
      chapter05UpperRamificationGroup D v = ⊤ := by
    intro v hv hv0
    have hvinv := chapter05_herbrand_inverse_spec D hbij v
    have hinv_eq : chapter05HerbrandInverse D v = v := by
      by_cases hinv0 : chapter05HerbrandInverse D v ≤ 0
      · have hform := htame (chapter05HerbrandInverse D v)
        rw [hform, chapter05TameHerbrand, if_pos hinv0] at hvinv
        exact hvinv
      · have hinv_pos : 0 < chapter05HerbrandInverse D v :=
          lt_of_not_ge hinv0
        have hform := htame (chapter05HerbrandInverse D v)
        rw [hform, chapter05TameHerbrand, if_neg hinv0] at hvinv
        have he0 : 0 < e := by omega
        have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he0
        have hpos : 0 <
            chapter05HerbrandInverse D v / (e : ℝ) :=
          div_pos hinv_pos hepos
        linarith
    rw [chapter05UpperRamificationGroup, if_pos hv, hinv_eq,
      D.lower_neg v hv hv0]
  have hRight_zero : chapter05UpperRightLimit D 0 = (⊥ : Subgroup G) := by
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      rcases hK with ⟨w, hw, rfl⟩
      rw [chapter05_tame_upper_groups_drop_after_zero D e (by omega)
        hcard htotal htrivial hbij w hw]
    · exact bot_le
  have hRight_pos : ∀ {v : ℝ}, 0 < v →
      chapter05UpperRightLimit D v = (⊥ : Subgroup G) := by
    intro v hv
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      rcases hK with ⟨w, hw, rfl⟩
      rw [chapter05_tame_upper_groups_drop_after_zero D e (by omega)
        hcard htotal htrivial hbij w (lt_trans hv hw)]
    · exact bot_le
  have hRight_neg : ∀ {v : ℝ}, (-1 : ℝ) ≤ v → v < 0 →
      chapter05UpperRightLimit D v = (⊤ : Subgroup G) := by
    intro v hv hv0
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      exact le_top
    · have hw : v < v / 2 := by linarith
      have hw0 : v / 2 < 0 := by linarith
      have hmem : (⊤ : Subgroup G) ∈
          chapter05UpperRamificationGroup D '' Set.Ioi v := by
        refine ⟨v / 2, hw, hupper_neg (by linarith) hw0⟩
      exact le_sSup hmem
  have hbreak_zero : chapter05UpperBreak D 0 := by
    rw [chapter05UpperBreak]
    refine ⟨by norm_num, ?_⟩
    have hne : (0 : ℝ) ≠ (-1 : ℝ) := by norm_num
    rw [if_neg hne, chapter05_upper_group_zero_eq_lower_zero D hbij,
      hRight_zero]
    exact hzero
  refine ⟨hbreak_zero, ?_⟩
  intro v hvne hvbreak
  rw [chapter05UpperBreak] at hvbreak
  rcases hvbreak with ⟨hvneg, hvcond⟩
  by_cases hvminus : v = (-1 : ℝ)
  · exfalso
    simp [hvminus, htop0] at hvcond
  have hvcond' : chapter05UpperRamificationGroup D v ≠
      chapter05UpperRightLimit D v := by
    simpa [hvminus] using hvcond
  by_cases hvpos : 0 < v
  · exfalso
    apply hvcond'
    rw [chapter05_tame_upper_groups_drop_after_zero D e (by omega)
      hcard htotal htrivial hbij v hvpos, hRight_pos hvpos]
  · have hvneg' : v < 0 := by
      have hvle : v ≤ 0 := le_of_not_gt hvpos
      exact lt_of_le_of_ne hvle hvne
    exfalso
    apply hvcond'
    rw [hupper_neg hvneg hvneg', hRight_neg hvneg hvneg']

/-- The tame slope is the scale change that becomes visible in a composite tower. -/
theorem chapter05_tame_scale_change_is_one_division_by_e
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter05RamificationFiltration G) (e : ℕ) (he : 0 < e)
    (hcard : Nat.card (D.lowerGroup 0) = e)
    (htrivial : ∀ u : ℝ, 0 < u → D.lowerGroup u = ⊥) :
    ∀ u : ℝ, 0 < u →
      chapter05HerbrandSlope D u = (1 : ℝ) / (e : ℝ) := by
  intro u hu
  simpa [one_div] using
    chapter05_tame_herbrand_slope D e he hcard htrivial u hu

end
end LastLib.Book03RamificationTheory.Chapter05
