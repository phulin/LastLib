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
  sorry

/-- The floor convention has the same integral groups but uses the opposite
endpoint convention: it is constant on `m ≤ u < m + 1`. -/
theorem chapter04_floor_convention_has_same_integral_groups
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) {i : ℤ} (hi : -1 ≤ i) :
    chapter04FloorRealLowerGroup F (i : ℝ) = chapter04LowerGroup F i := by
  sorry

/-- On positive intervals the floor and ceiling conventions differ only by the
endpoint at which the next integer group is entered. -/
theorem chapter04_floor_ceiling_endpoint_shift
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) (m : ℕ) {u : ℝ}
    (hm : (m : ℝ) < u) (hm' : u < (m + 1 : ℕ)) :
    chapter04RealLowerGroup F u = F.lower (m + 1) ∧
      chapter04FloorRealLowerGroup F u = F.lower m := by
  sorry

/-- The first positive interval has the standard slope normalization. -/
theorem chapter04_herbrand_first_slope
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    chapter04HerbrandFunction F 1 = chapter04HerbrandSlope F 0 := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter04
