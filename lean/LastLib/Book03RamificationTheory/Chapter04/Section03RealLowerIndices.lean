import LastLib.Book03RamificationTheory.Chapter04.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter04

noncomputable section

open scoped BigOperators Pointwise

/-! ## 4.3. Real lower indices and continuity convention -/

/-- The ceiling convention is constant on each interval `m < u ≤ m + 1`,
which is the source-facing form of left continuity at positive integers. -/
theorem chapter04_real_lower_group_left_continuous_convention
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) (m : ℕ) {u : ℝ}
    (hm : (m : ℝ) < u) (hm' : u ≤ (m + 1 : ℕ)) :
    chapter04RealLowerGroup F u = F.lower (m + 1) := by
  exact chapter04RealLowerGroup_on_right_closed_unit_interval F m hm hm'

/-- The negative interval retains the `-1` group, which is the whole ambient
group in the normalized Galois situation. -/
theorem chapter04_real_lower_group_negative_interval
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) {u : ℝ}
    (hu : (-1 : ℝ) ≤ u) (hu' : u < 0) :
    chapter04RealLowerGroup F u = ⊤ := by
  exact chapter04RealLowerGroup_neg F hu hu'

/-- All integral lower groups are unchanged by the real extension. -/
theorem chapter04_real_lower_group_at_integral_index
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) {i : ℤ} (hi : -1 ≤ i) :
    chapter04RealLowerGroup F (i : ℝ) = chapter04LowerGroup F i := by
  by_cases hneg : (i : ℝ) < 0
  · have hneg' : i < 0 := by exact_mod_cast hneg
    have hi' : (-1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    rw [chapter04RealLowerGroup_neg F hi' hneg]
    simp [chapter04LowerGroup, hneg']
  · have hi0 : 0 ≤ i := by exact_mod_cast (le_of_not_gt hneg)
    rw [chapter04LowerGroup_of_nonnegative F hi0]
    simp [chapter04RealLowerGroup, hneg]

/-- The floor convention has the same integral groups but uses the opposite
endpoint convention: it is constant on `m ≤ u < m + 1`. -/
theorem chapter04_floor_convention_has_same_integral_groups
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) {i : ℤ} (hi : -1 ≤ i) :
    chapter04FloorRealLowerGroup F (i : ℝ) = chapter04LowerGroup F i := by
  by_cases hneg : (i : ℝ) < 0
  · have hneg' : i < 0 := by exact_mod_cast hneg
    have hi' : (-1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    simp [chapter04FloorRealLowerGroup, hneg, chapter04LowerGroup, hneg']
  · have hi0 : 0 ≤ i := by exact_mod_cast (le_of_not_gt hneg)
    rw [chapter04LowerGroup_of_nonnegative F hi0]
    simp [chapter04FloorRealLowerGroup, hneg]

/-- On positive intervals the floor and ceiling conventions differ only by the
endpoint at which the next integer group is entered. -/
theorem chapter04_floor_ceiling_endpoint_shift
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) (m : ℕ) {u : ℝ}
    (hm : (m : ℝ) < u) (hm' : u < (m + 1 : ℕ)) :
    chapter04RealLowerGroup F u = F.lower (m + 1) ∧
      chapter04FloorRealLowerGroup F u = F.lower m := by
  exact ⟨
    chapter04RealLowerGroup_on_right_closed_unit_interval F m hm hm'.le,
    chapter04FloorRealLowerGroup_on_left_closed_unit_interval F m hm.le hm'⟩

/-- The first positive interval has the standard slope normalization. -/
theorem chapter04_herbrand_first_slope
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    chapter04HerbrandFunction F 1 = chapter04HerbrandSlope F 0 := by
  have hrel := Subgroup.relIndex_mul_index (F.descending 0)
  have hA := Subgroup.index_mul_card (F.lower 1)
  have hB := Subgroup.index_mul_card (F.lower 0)
  have hidxpos : 0 < (F.lower 0).index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := F.lower 0))
  have hcard : (F.lower 1).relIndex (F.lower 0) * Nat.card (F.lower 1) =
      Nat.card (F.lower 0) := by
    apply Nat.eq_of_mul_eq_mul_left hidxpos
    calc
      (F.lower 0).index *
          ((F.lower 1).relIndex (F.lower 0) * Nat.card (F.lower 1)) =
          ((F.lower 1).relIndex (F.lower 0) * (F.lower 0).index) *
            Nat.card (F.lower 1) := by ring
      _ = (F.lower 1).index * Nat.card (F.lower 1) := by rw [hrel]
      _ = Nat.card G := hA
      _ = (F.lower 0).index * Nat.card (F.lower 0) := hB.symm
  have hrelpos : 0 < (F.lower 1).relIndex (F.lower 0) := by
    have hcard0pos : 0 < Nat.card (F.lower 0) := Nat.card_pos
    apply Nat.pos_of_ne_zero
    intro hzero
    have : Nat.card (F.lower 0) = 0 := by simpa [hzero] using hcard.symm
    exact (Nat.ne_of_gt hcard0pos) this
  have hcard_real :
      ((F.lower 1).relIndex (F.lower 0) : ℝ) * Nat.card (F.lower 1) =
        Nat.card (F.lower 0) := by
    exact_mod_cast hcard
  unfold chapter04HerbrandFunction
  rw [if_pos (by exact zero_le_one)]
  calc
    (∫ t in (0 : ℝ)..1, chapter04HerbrandIntegrand F t) =
        ∫ t in (0 : ℝ)..1, (fun _ => chapter04HerbrandSlope F 0) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with t ht
      have ht' : ((0 : ℕ) : ℝ) < t := by simpa using ht.1
      have ht'' : t ≤ (0 + 1 : ℕ) := by simpa using ht.2
      rw [chapter04HerbrandIntegrand,
        chapter04RealLowerGroup_on_right_closed_unit_interval F 0 ht' ht'']
      simp only [Nat.zero_add]
      unfold chapter04HerbrandSlope
      have hcard0ne : (Nat.card (F.lower 0) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (show 0 < Nat.card (F.lower 0) from Nat.card_pos))
      apply (eq_div_iff hcard0ne).2
      rw [← hcard_real]
      field_simp [ne_of_gt hrelpos]
    _ = chapter04HerbrandSlope F 0 := by simp

end
end LastLib.Book03RamificationTheory.Chapter04
