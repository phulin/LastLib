import LastLib.Book03RamificationTheory.Chapter04.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter04

noncomputable section

open scoped BigOperators Pointwise

/-! ## 4.4. The Herbrand function -/

/-- The integral form of the Herbrand function on the nonnegative half-line. -/
theorem chapter04_herbrand_function_integral_formula
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {u : ℝ} (hu : 0 ≤ u) :
    chapter04HerbrandFunction F u =
      ∫ t in (0 : ℝ)..u, chapter04HerbrandIntegrand F t := by
  sorry

/-- The closed piecewise-linear formula on the interval `[m,m+1]`. -/
theorem chapter04_herbrand_function_piecewise_formula
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (m : ℕ) {u : ℝ}
    (hm : (m : ℝ) ≤ u) (hm' : u ≤ (m + 1 : ℕ)) :
    chapter04HerbrandFunction F u =
      chapter04HerbrandPiecewiseValue F m u := by
  sorry

/-- The slope on `(m,m+1)` is the ratio `|G_(m+1)| / |G₀|`. -/
theorem chapter04_herbrand_slope_on_interval
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (m : ℕ) {u v : ℝ}
    (hu : (m : ℝ) ≤ u) (hu' : u ≤ (m + 1 : ℕ))
    (hv : (m : ℝ) ≤ v) (hv' : v ≤ (m + 1 : ℕ)) :
    chapter04HerbrandFunction F u - chapter04HerbrandFunction F v =
      (u - v) * chapter04HerbrandSlope F m := by
  sorry

theorem chapter04_herbrand_slope_eq_first_ratio
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    chapter04HerbrandFunction F 1 =
      (Nat.card (F.lower 1) : ℝ) / Nat.card (F.lower 0) := by
  sorry

/-- Herbrand slopes decrease when the lower groups shrink. -/
theorem chapter04_herbrand_slope_antitone
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {m n : ℕ} (hmn : m ≤ n) :
    chapter04HerbrandSlope F n ≤ chapter04HerbrandSlope F m := by
  sorry

/-- The clock never runs faster than the lower clock: every positive slope is
at most one. -/
theorem chapter04_herbrand_slope_le_one
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (m : ℕ) :
    chapter04HerbrandSlope F m ≤ 1 := by
  sorry

/-- Positivity of the reciprocal index is the monotonicity input for the
Herbrand map. -/
theorem chapter04_herbrand_integrand_pos
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (u : ℝ) :
    0 < chapter04HerbrandIntegrand F u := by
  sorry

/-- The integral map is continuous and strictly increasing on the full
ramification domain, and its range is the same half-line. -/
theorem chapter04_herbrand_is_homeomorphism_on_domain
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    ContinuousOn (chapter04HerbrandFunction F) (Set.Ici (-1 : ℝ)) ∧
      StrictMonoOn (chapter04HerbrandFunction F) (Set.Ici (-1 : ℝ)) ∧
      Set.range (fun u : Set.Ici (-1 : ℝ) => chapter04HerbrandFunction F u) =
        Set.Ici (-1 : ℝ) := by
  sorry

/-- The inverse notation is a genuine two-sided inverse on the book's domain. -/
theorem chapter04_herbrand_inverse_left_inverse
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {u : ℝ} (hu : -1 ≤ u) :
    chapter04HerbrandInverse F (chapter04HerbrandFunction F u) = u := by
  sorry

theorem chapter04_herbrand_inverse_right_inverse
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {u : ℝ} (hu : -1 ≤ u) :
    chapter04HerbrandFunction F (chapter04HerbrandInverse F u) = u := by
  sorry

/-- The Herbrand function only sees the inertia group and the positive lower
filtration.  Changes in the unramified quotient leave it unchanged. -/
theorem chapter04_herbrand_depends_only_on_inertia_and_positive_filtration
    {G : Type*} [Group G] [Finite G]
    (F F' : Chapter04LowerFiltration G)
    (hzero : F.lower 0 = F'.lower 0)
    (hpositive : ∀ n : ℕ, 1 ≤ n → F.lower n = F'.lower n) :
    ∀ u : ℝ, chapter04HerbrandFunction F u = chapter04HerbrandFunction F' u := by
  sorry

/-- In the tame totally ramified case, the positive filtration is trivial and
the Herbrand clock has constant slope `1 / |G₀|`. -/
theorem chapter04_tame_totally_ramified_herbrand_formula
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G)
    (hzero : F.lower 0 = ⊤) (hone : F.lower 1 = ⊥)
    {u : ℝ} (hu : 0 < u) :
    chapter04HerbrandFunction F u =
      u / Nat.card (F.lower 0) := by
  sorry

/-- A one-break profile packages the Artin--Schreier example used in the
preceding chapter: the group is full through `m` and trivial afterwards. -/
structure Chapter04OneBreakProfile
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (p m : ℕ) : Prop where
  card_zero : Nat.card (F.lower 0) = p
  full_through_break : ∀ n : ℕ, n ≤ m → F.lower n = ⊤
  trivial_after_break : ∀ n : ℕ, m + 1 ≤ n → F.lower n = ⊥

/-- The Herbrand function for a single wild break is the identity through the
break and has slope `1/p` afterwards. -/
theorem chapter04_artin_schreier_one_break_herbrand_formula
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (p m : ℕ)
    (hprofile : Chapter04OneBreakProfile F p m) (hp : 0 < p) {u : ℝ}
    (hu : 0 ≤ u) :
    (u ≤ m → chapter04HerbrandFunction F u = u) ∧
      (m ≤ u →
        chapter04HerbrandFunction F u =
          m + (u - m) / p) := by
  sorry

end
end LastLib.Book03RamificationTheory.Chapter04
