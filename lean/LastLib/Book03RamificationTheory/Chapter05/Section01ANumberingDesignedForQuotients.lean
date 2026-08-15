import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section05HigherRamificationBoundary
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

open scoped BigOperators
open Filter
open MeasureTheory

/-! ## 5.1. A numbering designed for quotients -/

/--
 A finite lower ramification filtration in the real-index convention used in
 Book 3.  The `lowerGroup` field is the real extension of the integer lower
 groups from Chapter 4.  In particular, on `(m,m+1]` it has the value of the
 `(m+1)`st integer group; this is the convention for which the Herbrand slope
 on that interval is `|G_(m+1)| / |G_0|`.

 The displacement field deliberately uses the Chapter 4 normalization
 `G_m = {σ | i_G(σ) ≥ m+1}`.  It is only constrained away from the identity,
 whose displacement is recorded separately as zero because the finite value
 `i_G(1)=+∞` is not needed by any quotient identity.
-/
structure Chapter05RamificationFiltration
    (G : Type*) [Group G] [Finite G] where
  lowerGroup : ℝ → Subgroup G
  lower_antitone : Antitone lowerGroup
  lower_normal : ∀ u : ℝ, (lowerGroup u).Normal
  lower_neg : ∀ u : ℝ, (-1 : ℝ) ≤ u → u < 0 → lowerGroup u = ⊤
  lower_real_convention :
    ∀ (m : ℕ) (u : ℝ), (m : ℝ) < u → u ≤ (m + 1 : ℕ) →
      lowerGroup u = lowerGroup (m + 1 : ℕ)
  lower_eventually_trivial : ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
    lowerGroup (m : ℝ) = ⊥
  displacement : G → ℕ
  displacement_one : displacement 1 = 0
  lower_nat_mem_iff :
    ∀ {σ : G}, σ ≠ 1 → ∀ n : ℕ,
      σ ∈ lowerGroup (n : ℝ) ↔ n + 1 ≤ displacement σ

namespace Chapter05RamificationFiltration

variable {G : Type*} [Group G] [Finite G]

instance lowerGroup_normal
    (D : Chapter05RamificationFiltration G) (u : ℝ) :
    (D.lowerGroup u).Normal := D.lower_normal u

instance :
    CoeFun (Chapter05RamificationFiltration G) (fun _ => ℝ → Subgroup G) :=
  ⟨Chapter05RamificationFiltration.lowerGroup⟩

@[simp] theorem lowerGroup_apply (D : Chapter05RamificationFiltration G)
    (u : ℝ) : D u = D.lowerGroup u := rfl

@[ext] theorem ext
    {D D' : Chapter05RamificationFiltration G}
    (hlower : D.lowerGroup = D'.lowerGroup)
    (hdisplacement : D.displacement = D'.displacement) :
    D = D' := by
  cases D
  cases D'
  cases hlower
  cases hdisplacement
  rfl

end Chapter05RamificationFiltration

/-- The right-hand limit of a decreasing subgroup-valued filtration. -/
noncomputable def chapter05RightLimit
    {G : Type*} [Group G] [Finite G]
    (F : ℝ → Subgroup G) (u : ℝ) : Subgroup G :=
  sSup (F '' Set.Ioi u)

/-- Left continuity away from the deliberately separated jump at zero. -/
def chapter05LeftContinuousOnPositive
    {G : Type*} [Group G] [Finite G]
    (F : ℝ → Subgroup G) : Prop :=
  ∀ u : ℝ, 0 < u → F u = sInf (F '' Set.Ioo (-1 : ℝ) u)

/-- The integer lower breaks, with the Chapter 4 shift by one. -/
def chapter05LowerBreak
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (m : ℕ) : Prop :=
  D.lowerGroup (m : ℝ) ≠ D.lowerGroup (m + 1 : ℕ)

/-- The slope of the Herbrand clock at a positive lower depth. -/
noncomputable def chapter05HerbrandSlope
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (u : ℝ) : ℝ :=
  if u ≤ 0 then 1 else
    (Nat.card (D.lowerGroup u) : ℝ) /
      (Nat.card (D.lowerGroup 0) : ℝ)

/--
 The Herbrand function, extended by the identity on the negative interval.
 The interval integral is the canonical construction; the filtration fields
 ensure that its integrand is the required positive piecewise-constant slope.
-/
noncomputable def chapter05HerbrandFunction
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (u : ℝ) : ℝ :=
  if u ≤ 0 then u else
    ∫ t in (0 : ℝ)..u, chapter05HerbrandSlope D t

theorem chapter05_herbrand_function_neg_one
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    chapter05HerbrandFunction D (-1 : ℝ) = -1 := by
  simp [chapter05HerbrandFunction]

theorem chapter05_herbrand_function_zero
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    chapter05HerbrandFunction D 0 = 0 := by
  simp [chapter05HerbrandFunction]

theorem chapter05_herbrand_function_of_nonpositive
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) {u : ℝ} (hu : u ≤ 0) :
    chapter05HerbrandFunction D u = u := by
  simp [chapter05HerbrandFunction, hu]

/-! The explicit interval formula from the source is kept alongside the
    integral definition.  It is the form used in break calculations and
    makes the finite-sum normalization available to later sections. -/
theorem chapter05_herbrand_function_interval_formula
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (m : ℕ) {u : ℝ}
    (hu_lower : (m : ℝ) ≤ u)
    (hu_upper : u ≤ (m + 1 : ℕ)) :
    chapter05HerbrandFunction D u =
    ((Finset.sum (Finset.Icc 1 m)
          (fun j => (Nat.card (D.lowerGroup (j : ℝ)) : ℝ))) +
        (u - (m : ℝ)) *
          (Nat.card (D.lowerGroup (m + 1 : ℕ)) : ℝ)) /
        (Nat.card (D.lowerGroup 0) : ℝ) := by
  have hpiece : ∀ j : ℕ,
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume
        (j : ℝ) ((j + 1 : ℕ) : ℝ) := by
    intro j
    have hconst : Set.EqOn (chapter05HerbrandSlope D)
        (fun _ : ℝ =>
          (Nat.card (D.lowerGroup (j + 1 : ℕ)) : ℝ) /
            Nat.card (D.lowerGroup 0))
        (Set.uIoo (j : ℝ) ((j + 1 : ℕ) : ℝ)) := by
      intro t ht
      have ht'' : (j : ℝ) < t ∧ t < ((j + 1 : ℕ) : ℝ) := by
        simpa [Set.uIoo_of_le (by norm_num : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ))]
          using ht
      have ht' : (j : ℝ) < t ∧ t ≤ ((j + 1 : ℕ) : ℝ) :=
        ⟨ht''.1, ht''.2.le⟩
      have ht0 : ¬t ≤ 0 := by
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith
      rw [chapter05HerbrandSlope, if_neg ht0]
      rw [D.lower_real_convention j t ht'.1 ht'.2]
    exact (intervalIntegrable_congr_uIoo hconst).mpr intervalIntegrable_const
  have hinterval : ∀ j : ℕ,
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume 0 (j : ℝ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have htrans := ih.trans (hpiece j)
        simpa [Nat.cast_add, Nat.cast_one] using htrans
  have hformula : ∀ (j : ℕ) {x : ℝ},
      (j : ℝ) ≤ x → x ≤ ((j + 1 : ℕ) : ℝ) →
        chapter05HerbrandFunction D x =
          ((Finset.sum (Finset.Icc 1 j)
              (fun k => (Nat.card (D.lowerGroup (k : ℝ)) : ℝ))) +
            (x - (j : ℝ)) *
              (Nat.card (D.lowerGroup (j + 1 : ℕ)) : ℝ)) /
            (Nat.card (D.lowerGroup 0) : ℝ) := by
    intro j
    induction j with
    | zero =>
        intro x hx_lower hx_upper
        by_cases hx0 : x ≤ 0
        · have hx_eq : x = 0 := le_antisymm hx0 (by simpa using hx_lower)
          subst x
          simp [chapter05HerbrandFunction]
        · rw [chapter05HerbrandFunction, if_neg hx0]
          have hconst : Set.EqOn (chapter05HerbrandSlope D)
              (fun _ : ℝ =>
                (Nat.card (D.lowerGroup 1) : ℝ) /
                  Nat.card (D.lowerGroup 0)) (Set.Ioo 0 x) := by
            intro t ht
            have ht0 : ¬t ≤ 0 := not_le.mpr ht.1
            have hgroup : D.lowerGroup t = D.lowerGroup 1 :=
              by
                simpa using
                  (D.lower_real_convention 0 t (by simpa using ht.1)
                    (le_trans ht.2.le hx_upper))
            simp [chapter05HerbrandSlope, ht0, hgroup]
          rw [intervalIntegral.integral_congr_Ioo_of_le (le_of_not_ge hx0)
              hconst, intervalIntegral.integral_const]
          simp [smul_eq_mul]
          ring
    | succ j ih =>
        intro x hx_lower hx_upper
        have hx_pos : 0 < x := by
          have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
          exact lt_of_lt_of_le hpos hx_lower
        rw [chapter05HerbrandFunction, if_neg (not_le.mpr hx_pos)]
        have hbase := ih (x := ((j + 1 : ℕ) : ℝ))
          (by norm_num) (by norm_num)
        have hjpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.zero_lt_succ j
        rw [chapter05HerbrandFunction, if_neg (not_le.mpr hjpos)] at hbase
        have hconst : Set.EqOn (chapter05HerbrandSlope D)
            (fun _ : ℝ =>
              (Nat.card (D.lowerGroup (j + 2 : ℕ)) : ℝ) /
                Nat.card (D.lowerGroup 0))
            (Set.Ioo ((j + 1 : ℕ) : ℝ) x) := by
          intro t ht
          have ht0 : ¬t ≤ 0 := by
            have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.zero_lt_succ j
            exact not_le_of_gt (hpos.trans ht.1)
          have hgroup : D.lowerGroup t = D.lowerGroup (j + 2 : ℕ) :=
            by
              simpa [Nat.add_assoc] using
                D.lower_real_convention (j + 1) t ht.1
                  (ht.2.le.trans hx_upper)
          rw [chapter05HerbrandSlope, if_neg ht0, hgroup]
        have htail : IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume
            ((j + 1 : ℕ) : ℝ) x := by
          have hconst' : Set.EqOn (chapter05HerbrandSlope D)
              (fun _ : ℝ =>
                (Nat.card (D.lowerGroup (j + 2 : ℕ)) : ℝ) /
                  Nat.card (D.lowerGroup 0))
              (Set.uIoo ((j + 1 : ℕ) : ℝ) x) := by
            have hx_lower' : (j : ℝ) + 1 ≤ x := by
              simpa [Nat.cast_add, Nat.cast_one] using hx_lower
            intro t ht
            have ht'' : ((j + 1 : ℕ) : ℝ) < t ∧ t < x := by
              simpa [Set.uIoo_of_le hx_lower'] using ht
            exact hconst ⟨ht''.1, ht''.2⟩
          exact (intervalIntegrable_congr_uIoo hconst').mpr intervalIntegrable_const
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hinterval (j + 1)) htail]
        rw [hbase, intervalIntegral.integral_congr_Ioo_of_le hx_lower hconst,
          intervalIntegral.integral_const]
        have hsum : Finset.Icc 1 (j + 1) =
            insert (j + 1) (Finset.Icc 1 j) := by
          rw [show j + 1 = Nat.succ j by omega]
          exact (Finset.insert_Icc_right_eq_Icc_succ
            (Nat.succ_le_succ (Nat.zero_le j))).symm
        rw [hsum]
        rw [Finset.sum_insert]
        · simp [smul_eq_mul, Nat.add_comm, Nat.add_left_comm]
          ring
        · simp
  exact hformula m hu_lower hu_upper

/-!
  The source's ``homeomorphism'' assertion is recorded in two useful forms:
  the interval-wise slope formula and the resulting domain statement.  The
  latter is stated on `[-1, ∞)` because that is the ramification domain; the
  global inverse used below is an `invFun` only for API convenience.
-/
theorem chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    ContinuousOn (chapter05HerbrandFunction D) (Set.Ici (-1 : ℝ)) ∧
      StrictMonoOn (chapter05HerbrandFunction D) (Set.Ici (-1 : ℝ)) ∧
      (∀ m : ℕ, ∀ {u v : ℝ},
        (m : ℝ) ≤ u → u ≤ (m + 1 : ℕ) →
        (m : ℝ) ≤ v → v ≤ (m + 1 : ℕ) →
        chapter05HerbrandFunction D u - chapter05HerbrandFunction D v =
          (u - v) *
            ((Nat.card (D.lowerGroup (m + 1 : ℕ)) : ℝ) /
              Nat.card (D.lowerGroup 0))) := by
  have hpiece : ∀ j : ℕ,
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume
        (j : ℝ) ((j + 1 : ℕ) : ℝ) := by
    intro j
    have hconst : Set.EqOn (chapter05HerbrandSlope D)
        (fun _ : ℝ =>
          (Nat.card (D.lowerGroup (j + 1 : ℕ)) : ℝ) /
            Nat.card (D.lowerGroup 0))
        (Set.uIoo (j : ℝ) ((j + 1 : ℕ) : ℝ)) := by
      intro t ht
      have ht' : (j : ℝ) < t ∧ t < ((j + 1 : ℕ) : ℝ) := by
        simpa [Set.uIoo_of_le (by norm_num :
          (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ))] using ht
      have ht0 : ¬t ≤ 0 := by
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith
      rw [chapter05HerbrandSlope, if_neg ht0]
      rw [D.lower_real_convention j t ht'.1 ht'.2.le]
    exact (intervalIntegrable_congr_uIoo hconst).mpr intervalIntegrable_const
  have hnat : ∀ j : ℕ,
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume
        0 (j : ℝ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have htrans := ih.trans (hpiece j)
        simpa [Nat.cast_add, Nat.cast_one] using htrans
  have hneg : ∀ a b : ℝ, a ≤ 0 → b ≤ 0 →
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume a b := by
    intro a b ha hb
    rcases le_total a b with hab | hba
    · have hconst : Set.EqOn (chapter05HerbrandSlope D)
          (fun _ : ℝ => (1 : ℝ)) (Set.uIoo a b) := by
        intro t ht
        have ht' : a < t ∧ t < b := by
          simpa [Set.uIoo_of_le hab] using ht
        rw [chapter05HerbrandSlope, if_pos (le_trans ht'.2.le hb)]
      exact (intervalIntegrable_congr_uIoo hconst).mpr intervalIntegrable_const
    · have hconst : Set.EqOn (chapter05HerbrandSlope D)
          (fun _ : ℝ => (1 : ℝ)) (Set.uIoo a b) := by
        intro t ht
        have ht' : b < t ∧ t < a := by
          simpa [Set.uIoo_of_ge hba] using ht
        rw [chapter05HerbrandSlope, if_pos (le_trans ht'.2.le ha)]
      exact (intervalIntegrable_congr_uIoo hconst).mpr intervalIntegrable_const
  have hpos : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume a b := by
    intro a b ha hab
    obtain ⟨N, hN⟩ := exists_nat_ge b
    have h0N : (0 : ℝ) ≤ (N : ℝ) := le_trans ha (hab.trans hN)
    apply (hnat N).mono_set
    intro t ht
    have htab : t ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using ht
    have ht0N : t ∈ Set.Icc (0 : ℝ) (N : ℝ) := by
      exact ⟨le_trans ha htab.1, le_trans htab.2 hN⟩
    simpa [Set.uIcc_of_le h0N] using ht0N
  have hint : ∀ a b : ℝ,
      IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume a b := by
    have hint_le : ∀ {a b : ℝ}, a ≤ b →
        IntervalIntegrable (chapter05HerbrandSlope D) MeasureTheory.volume a b := by
      intro a b hab
      by_cases hb0 : b ≤ 0
      · exact hneg a b (hab.trans hb0) hb0
      · have hbpos : 0 ≤ b := le_of_not_ge hb0
        by_cases ha0 : a ≤ 0
        · exact (hneg a 0 ha0 le_rfl).trans
            (hpos (a := 0) (b := b) le_rfl hbpos)
        · exact hpos (le_of_not_ge ha0) hab
    intro a b
    rcases le_total a b with hab | hba
    · exact hint_le hab
    · exact (hint_le hba).symm
  have hslope_pos : ∀ t : ℝ, 0 < chapter05HerbrandSlope D t := by
    intro t
    by_cases ht : t ≤ 0
    · simp [chapter05HerbrandSlope, ht]
    · rw [chapter05HerbrandSlope, if_neg ht]
      have hnum : 0 < (Nat.card (D.lowerGroup t) : ℝ) := by
        exact_mod_cast Nat.card_pos
      have hden : 0 < (Nat.card (D.lowerGroup 0) : ℝ) := by
        exact_mod_cast Nat.card_pos
      positivity
  have hF_eq_integral : ∀ u : ℝ,
      chapter05HerbrandFunction D u =
        ∫ t in (0 : ℝ)..u, chapter05HerbrandSlope D t := by
    intro u
    by_cases hu : u ≤ 0
    · rw [chapter05_herbrand_function_of_nonpositive D hu]
      have hconst : Set.EqOn (chapter05HerbrandSlope D)
          (fun _ : ℝ => (1 : ℝ)) (Set.uIoo (0 : ℝ) u) := by
        intro t ht
        have ht' : u < t ∧ t < 0 := by
          simpa [Set.uIoo_of_ge hu] using ht
        rw [chapter05HerbrandSlope, if_pos ht'.2.le]
      calc
        u = ∫ _ in (0 : ℝ)..u, (1 : ℝ) := by simp
        _ = ∫ t in (0 : ℝ)..u, chapter05HerbrandSlope D t := by
          symm
          exact intervalIntegral.integral_congr_uIoo hconst
    · simp [chapter05HerbrandFunction, hu]
  have hcontinuous : ContinuousOn (chapter05HerbrandFunction D)
      (Set.Ici (-1 : ℝ)) := by
    rw [show chapter05HerbrandFunction D =
        (fun u : ℝ => ∫ t in (0 : ℝ)..u, chapter05HerbrandSlope D t) by
      funext u; exact hF_eq_integral u]
    exact (intervalIntegral.continuous_primitive hint 0).continuousOn
  have hstrict : StrictMonoOn (chapter05HerbrandFunction D)
      (Set.Ici (-1 : ℝ)) := by
    intro x hx y hy hxy
    have hdiff :
        (∫ t in (0 : ℝ)..y, chapter05HerbrandSlope D t) -
            ∫ t in (0 : ℝ)..x, chapter05HerbrandSlope D t =
          ∫ t in x..y, chapter05HerbrandSlope D t := by
      exact intervalIntegral.integral_interval_sub_left (hint 0 y) (hint 0 x)
    have hposint := intervalIntegral.intervalIntegral_pos_of_pos
      (hint x y) hslope_pos hxy
    rw [hF_eq_integral x, hF_eq_integral y]
    linarith
  refine ⟨hcontinuous, hstrict, ?_⟩
  intro m u v hu_lower hu_upper hv_lower hv_upper
  rw [chapter05_herbrand_function_interval_formula D m hu_lower hu_upper,
    chapter05_herbrand_function_interval_formula D m hv_lower hv_upper]
  ring

theorem chapter05_herbrand_is_homeomorphism_on_domain
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    ContinuousOn (chapter05HerbrandFunction D) (Set.Ici (-1 : ℝ)) ∧
      StrictMonoOn (chapter05HerbrandFunction D) (Set.Ici (-1 : ℝ)) ∧
      Set.range (fun u : Set.Ici (-1 : ℝ) => chapter05HerbrandFunction D u) =
        Set.Ici (-1 : ℝ) := by
  have hbase := chapter05_herbrand_function_is_continuous_increasing_piecewise_linear D
  have hcontinuous := hbase.1
  have hstrict := hbase.2.1
  obtain ⟨B, hB⟩ := D.lower_eventually_trivial
  let c : ℝ := 1 / (Nat.card (D.lowerGroup 0) : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    have hden : 0 < (Nat.card (D.lowerGroup 0) : ℝ) := by
      exact_mod_cast Nat.card_pos
    exact one_div_pos.mpr hden
  have htail_step : ∀ m : ℕ, B ≤ m →
      chapter05HerbrandFunction D ((m + 1 : ℕ) : ℝ) =
        chapter05HerbrandFunction D (m : ℝ) + c := by
    intro m hm
    have hFm := chapter05_herbrand_function_interval_formula D m
      (by norm_num : (m : ℝ) ≤ (m : ℝ)) (by norm_num :
        (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ))
    have hFnext := chapter05_herbrand_function_interval_formula D m
      (u := ((m + 1 : ℕ) : ℝ)) (by norm_num) (by norm_num)
    have hgroup : D.lowerGroup ((m + 1 : ℕ) : ℝ) = ⊥ :=
      hB (m + 1) (by omega)
    rw [hgroup] at hFnext
    dsimp [c]
    rw [hFm, hFnext]
    rw [Subgroup.card_eq_one.mpr rfl]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have htail : ∀ k : ℕ,
      chapter05HerbrandFunction D ((B + k : ℕ) : ℝ) =
        chapter05HerbrandFunction D (B : ℝ) + (k : ℝ) * c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep := htail_step (B + k) (by omega)
        rw [show B + (k + 1) = B + k + 1 by omega]
        rw [hstep, ih]
        push_cast
        ring
  have htop : Tendsto (chapter05HerbrandFunction D) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro z
    obtain ⟨k, hk⟩ := exists_nat_ge
      ((z - chapter05HerbrandFunction D (B : ℝ)) / c)
    filter_upwards [eventually_ge_atTop ((B + k : ℕ) : ℝ)] with x hx
    have hx_dom : x ∈ Set.Ici (-1 : ℝ) := by
      have hBk : (0 : ℝ) ≤ ((B + k : ℕ) : ℝ) := by positivity
      change (-1 : ℝ) ≤ x
      exact le_trans (by norm_num) (hBk.trans hx)
    have hBk_dom : ((B + k : ℕ) : ℝ) ∈ Set.Ici (-1 : ℝ) := by
      have hBk : (0 : ℝ) ≤ ((B + k : ℕ) : ℝ) := by positivity
      exact le_trans (by norm_num) hBk
    have hmono := hstrict.monotoneOn hBk_dom hx_dom hx
    have hz_le : z ≤ chapter05HerbrandFunction D (B : ℝ) +
        (k : ℝ) * c := by
      have hk' : (z - chapter05HerbrandFunction D (B : ℝ)) / c ≤ (k : ℝ) := by
        exact_mod_cast hk
      have hmul : z - chapter05HerbrandFunction D (B : ℝ) ≤
          (k : ℝ) * c := (div_le_iff₀ hc).mp hk'
      linarith
    have hz_le' : z ≤ chapter05HerbrandFunction D ((B + k : ℕ) : ℝ) := by
      calc
        z ≤ chapter05HerbrandFunction D (B : ℝ) + (k : ℝ) * c := hz_le
        _ = chapter05HerbrandFunction D ((B + k : ℕ) : ℝ) := (htail k).symm
    exact hz_le'.trans hmono
  have himage : chapter05HerbrandFunction D '' Set.Ici (-1 : ℝ) =
      Set.Ici (-1 : ℝ) := by
    have hmono : MonotoneOn (chapter05HerbrandFunction D)
        (Set.Ici (-1 : ℝ)) := hstrict.monotoneOn
    simpa [chapter05_herbrand_function_neg_one D] using
      hcontinuous.image_Ici_of_monotoneOn hmono htop
  refine ⟨hcontinuous, hstrict, ?_⟩
  rw [show Set.range (fun u : Set.Ici (-1 : ℝ) =>
      chapter05HerbrandFunction D u) =
        chapter05HerbrandFunction D '' Set.Ici (-1 : ℝ) by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩]
  exact himage

theorem chapter05_herbrand_bijective_of_filtration
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    Function.Bijective (chapter05HerbrandFunction D) := by
  have hhome := chapter05_herbrand_is_homeomorphism_on_domain D
  have hcontinuous := hhome.1
  have hstrict := hhome.2.1
  have hF_domain : ∀ {y : ℝ}, (-1 : ℝ) ≤ y →
      (-1 : ℝ) ≤ chapter05HerbrandFunction D y := by
    intro y hy
    by_cases hy0 : y ≤ 0
    · rw [chapter05_herbrand_function_of_nonpositive D hy0]
      exact hy
    · have hypos : 0 < y := lt_of_not_ge hy0
      have hzero_dom : (0 : ℝ) ∈ Set.Ici (-1 : ℝ) := by norm_num
      have hy_dom : y ∈ Set.Ici (-1 : ℝ) := by exact hy
      have hlt := hstrict hzero_dom hy_dom hypos
      rw [chapter05_herbrand_function_zero D] at hlt
      linarith
  have hglobal : StrictMono (chapter05HerbrandFunction D) := by
    intro x y hxy
    by_cases hx : x < (-1 : ℝ)
    · by_cases hy : y < (-1 : ℝ)
      · rw [chapter05_herbrand_function_of_nonpositive D (by linarith),
          chapter05_herbrand_function_of_nonpositive D (by linarith)]
        exact hxy
      · have hy_dom : (-1 : ℝ) ≤ y := le_of_not_gt hy
        have hFy := hF_domain hy_dom
        rw [chapter05_herbrand_function_of_nonpositive D (by linarith)]
        linarith
    · have hx_dom : (-1 : ℝ) ≤ x := le_of_not_gt hx
      have hy_dom : (-1 : ℝ) ≤ y := hx_dom.trans hxy.le
      exact hstrict hx_dom hy_dom hxy
  constructor
  · exact hglobal.injective
  · intro y
    by_cases hy : (-1 : ℝ) ≤ y
    · have hy_range : y ∈ Set.range
          (fun u : Set.Ici (-1 : ℝ) => chapter05HerbrandFunction D u) := by
        rw [hhome.2.2]
        exact hy
      rcases hy_range with ⟨u, hu⟩
      exact ⟨u, hu⟩
    · refine ⟨y, ?_⟩
      exact chapter05_herbrand_function_of_nonpositive D (by
        have hy' : y < (-1 : ℝ) := lt_of_not_ge hy
        linarith)

/-- The inverse of the Herbrand function, using `invFun` before bijectivity is proved. -/
noncomputable def chapter05HerbrandInverse
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (v : ℝ) : ℝ :=
  Function.invFun (chapter05HerbrandFunction D) v

/-- The upper-numbered group `G^v = G_{ψ(v)}` on `[-1, ∞)`, extended by `⊤`
outside the ramification domain so the filtration is globally antitone. -/
def chapter05UpperRamificationGroup
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (v : ℝ) : Subgroup G :=
  if (-1 : ℝ) ≤ v then D.lowerGroup (chapter05HerbrandInverse D v) else ⊤

/-- The upper filtration immediately to the right of an index. -/
noncomputable def chapter05UpperRightLimit
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (v : ℝ) : Subgroup G :=
  chapter05RightLimit (chapter05UpperRamificationGroup D) v

/-- The stable group immediately to the right of zero. -/
noncomputable def chapter05UpperZeroPlus
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Subgroup G :=
  chapter05UpperRightLimit D 0

/-- An upper ramification break is a strict drop at the chosen upper index.

  The endpoint `-1` is handled separately: the real lower convention is
  constant on `(-1, 0)`, so its ordinary right limit would miss the initial
  drop from the full decomposition group to inertia. -/
def chapter05UpperBreak
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (v : ℝ) : Prop :=
  (-1 : ℝ) ≤ v ∧
    if v = (-1 : ℝ) then
      D.lowerGroup 0 ≠ ⊤
    else
      chapter05UpperRamificationGroup D v ≠ chapter05UpperRightLimit D v

/-- The set of all upper breaks of a filtration. -/
def chapter05UpperBreakSet
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Set ℝ :=
  {v | chapter05UpperBreak D v}

/-- The book's rationality predicate for an upper break. -/
def chapter05UpperBreakIsRational (v : ℝ) : Prop :=
  ∃ q : ℚ, (q : ℝ) = v

/-- The book's integrality predicate for an upper break. -/
def chapter05UpperBreakIsInteger (v : ℝ) : Prop :=
  ∃ z : ℤ, (z : ℝ) = v

/--
 The canonical integer congruence groups from Book 2, embedded in the ambient
 Galois group.  This is the bridge used when a Chapter 4 profile is realized
 by a chosen valuation branch.
-/
def chapter05RamificationGroupInG
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (n : ℕ) : Subgroup (Gal(E / F)) :=
  (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
    F A n).map (Subgroup.subtype _)

/- SOURCE_ISSUE: With the convention `G_u = G_(ceil u)` for `u > 0` and
   `G_i = {σ | i_G(σ) ≥ i+1}`, the indicator of membership in `G_t` has
   integral `i_G(γ)-1` for an inertial nonidentity element, not `i_G(γ)`.
   The corrected bridge below uses the shifted quantity explicitly. -/
noncomputable def chapter05DisplacementIndicatorIntegral
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (σ : G) : ℝ :=
  by
    classical
    exact if σ = 1 then 0 else
      ∫ t in Set.Ioi (0 : ℝ), (if σ ∈ D.lowerGroup t then (1 : ℝ) else 0)

theorem chapter05_displacement_integral_identity
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (σ : G) (hσ : σ ≠ 1)
    (hinertial : 1 ≤ D.displacement σ) :
    ((D.displacement σ - 1 : ℕ) : ℝ) =
      chapter05DisplacementIndicatorIntegral D σ := by
  classical
  let d : ℕ := D.displacement σ
  have hd : 1 ≤ d := hinertial
  have hmem_iff : ∀ {t : ℝ}, 0 < t →
      (σ ∈ D.lowerGroup t ↔ t ≤ (d : ℝ) - 1) := by
    intro t ht
    by_cases hnat : ∃ n : ℕ, t = (n : ℝ)
    · rcases hnat with ⟨n, rfl⟩
      have hnpos : 0 < n := by
        exact_mod_cast ht
      have hconv : D.lowerGroup (n : ℝ) = D.lowerGroup (n : ℝ) := by
        rfl
      rw [hconv, D.lower_nat_mem_iff (σ := σ) hσ n]
      constructor
      · intro h
        have h' : (n + 1 : ℕ) ≤ d := by simpa [d] using h
        have h'' : ((n + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast h'
        norm_num at h'' ⊢
        linarith
      · intro h
        have h' : (n : ℝ) + 1 ≤ (d : ℝ) := by linarith
        have h'' : ((n + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by
          simpa [Nat.cast_add, Nat.cast_one] using h'
        exact_mod_cast h''
    · let n : ℕ := ⌊t⌋₊
      have ht_nonneg : 0 ≤ t := le_of_lt ht
      have hn_le : (n : ℝ) ≤ t := by
        exact Nat.floor_le ht_nonneg
      have hn_lt : (n : ℝ) < t := by
        exact lt_of_le_of_ne hn_le (Ne.symm (by
          intro h
          apply hnat
          exact ⟨n, h⟩))
      have ht_upper : t ≤ ((n + 1 : ℕ) : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_one, n] using
          (Nat.lt_floor_add_one t).le
      have hconv : D.lowerGroup t =
          D.lowerGroup ((n + 1 : ℕ) : ℝ) :=
        D.lower_real_convention n t hn_lt ht_upper
      rw [hconv, D.lower_nat_mem_iff (σ := σ) hσ (n + 1)]
      constructor
      · intro h
        have h' : (n + 2 : ℕ) ≤ d := by simpa [Nat.add_assoc, d] using h
        have h'' : ((n + 2 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast h'
        have h'' : (n : ℝ) + 2 ≤ (d : ℝ) := by
          simpa [Nat.cast_add, Nat.cast_one] using h''
        have ht_upper' : t ≤ (n : ℝ) + 1 := by
          simpa [Nat.cast_add, Nat.cast_one] using ht_upper
        linarith
      · intro h
        by_contra hnot
        have h' : d ≤ n + 1 := by omega
        have h'' : (d : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h'
        have h'' : (d : ℝ) ≤ (n : ℝ) + 1 := by
          simpa [Nat.cast_add, Nat.cast_one] using h''
        linarith
  have hae : (fun t : ℝ => if σ ∈ D.lowerGroup t then (1 : ℝ) else 0) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t : ℝ => if t ∈ Set.Ioc (0 : ℝ) ((d : ℝ) - 1) then (1 : ℝ) else 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    by_cases hmem : σ ∈ D.lowerGroup t
    · have htd := (hmem_iff ht).mp hmem
      rw [if_pos hmem, if_pos ⟨ht, htd⟩]
    · have htd : ¬t ≤ (d : ℝ) - 1 := fun h => hmem ((hmem_iff ht).mpr h)
      rw [if_neg hmem, if_neg (by intro h; exact htd h.2)]
  rw [chapter05DisplacementIndicatorIntegral, if_neg hσ]
  rw [integral_congr_ae hae]
  have hmeas : MeasurableSet (Set.Ioc (0 : ℝ) ((d : ℝ) - 1)) := measurableSet_Ioc
  rw [show (fun t : ℝ => if t ∈ Set.Ioc (0 : ℝ) ((d : ℝ) - 1) then (1 : ℝ) else 0) =
      Set.indicator (Set.Ioc (0 : ℝ) ((d : ℝ) - 1)) (fun _ => (1 : ℝ)) by
    funext t
    simp [Set.indicator]]
  rw [integral_indicator_const (1 : ℝ) hmeas, measureReal_restrict_apply hmeas]
  simp [d, hd, Nat.cast_sub hd]

theorem chapter05_displacement_integral_identity_noninertial
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (σ : G) (hσ : σ ≠ 1)
    (hnoninertial : ¬1 ≤ D.displacement σ) :
    (0 : ℝ) = chapter05DisplacementIndicatorIntegral D σ := by
  classical
  have hσ0 : σ ∉ D.lowerGroup 0 := by
    intro hmem
    exact hnoninertial ((D.lower_nat_mem_iff hσ 0).mp (by simpa using hmem))
  rw [chapter05DisplacementIndicatorIntegral, if_neg hσ]
  have hae : (fun t : ℝ => if σ ∈ D.lowerGroup t then (1 : ℝ) else 0) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] (fun _ => 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hnot : σ ∉ D.lowerGroup t := by
      intro hmem
      have hle : D.lowerGroup t ≤ D.lowerGroup 0 :=
        D.lower_antitone ht.le
      exact hσ0 (hle hmem)
    simp [hnot]
  rw [integral_congr_ae hae]
  simp

/- The real convention has a separate, prescribed jump at zero: the negative
   interval is the full group while the value at zero is inertia. -/
theorem chapter05_lower_group_neg_one_eq_top
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    D.lowerGroup (-1 : ℝ) = ⊤ := by
  exact D.lower_neg (-1) (by norm_num) (by norm_num)

theorem chapter05_lower_filtration_left_continuous_on_positive
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) :
    chapter05LeftContinuousOnPositive D.lowerGroup := by
  rw [chapter05LeftContinuousOnPositive]
  intro u hu
  apply le_antisymm
  · apply le_sInf
    rintro K ⟨t, ht, rfl⟩
    exact D.lower_antitone ht.2.le
  · have hu_nonneg : (0 : ℝ) ≤ u := hu.le
    let n : ℕ := ⌊u⌋₊
    by_cases hinteger : u = (n : ℝ)
    · have hn_pos : 0 < n := by
        exact_mod_cast (by simpa [hinteger] using hu)
      let t : ℝ := u - (1 / 2 : ℝ)
      have hnt : ((n - 1 : ℕ) : ℝ) < t := by
        have hncast : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        dsimp [t]
        rw [hinteger, ← hncast]
        linarith
      have htu : t < u := by
        dsimp [t]
        linarith
      have htu_lower : (-1 : ℝ) < t := by
        dsimp [t]
        linarith
      have htu_upper : t ≤ (n : ℝ) := by
        dsimp [t]
        linarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num]
      have hu_lower : ((n - 1 : ℕ) : ℝ) < u := by
        rw [hinteger]
        have hncast : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        rw [← hncast]
        linarith
      have hu_upper : u ≤ (n : ℝ) := by simp [hinteger]
      have hn_succ : n - 1 + 1 = n := by omega
      have ht_group : D.lowerGroup t = D.lowerGroup (n : ℝ) := by
        simpa [hn_succ] using
          D.lower_real_convention (n - 1) t hnt
            (by simpa [hn_succ] using htu_upper)
      have hu_group : D.lowerGroup u = D.lowerGroup (n : ℝ) := by
        simpa [hn_succ] using
          D.lower_real_convention (n - 1) u hu_lower
            (by simpa [hn_succ] using hu_upper)
      apply sInf_le
      exact ⟨t, ⟨htu_lower, htu⟩, ht_group.trans hu_group.symm⟩
    · have hn_le : (n : ℝ) ≤ u := by
        exact Nat.floor_le hu_nonneg
      have hn_lt : (n : ℝ) < u := lt_of_le_of_ne hn_le (Ne.symm hinteger)
      have hu_lt : u < (n : ℝ) + 1 := by
        simpa [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one u
      let t : ℝ := ((n : ℝ) + u) / 2
      have hnt : (n : ℝ) < t := by
        dsimp [t]
        linarith
      have htu : t < u := by
        dsimp [t]
        linarith
      have htu_lower : (-1 : ℝ) < t := by
        have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
        dsimp [t]
        linarith
      have htu_upper : t ≤ (n : ℝ) + 1 := by
        dsimp [t]
        linarith
      have ht_group : D.lowerGroup t = D.lowerGroup ((n + 1 : ℕ) : ℝ) := by
        exact D.lower_real_convention n t hnt
          (by simpa [Nat.cast_add, Nat.cast_one] using htu_upper)
      have hu_group : D.lowerGroup u = D.lowerGroup ((n + 1 : ℕ) : ℝ) := by
        exact D.lower_real_convention n u hn_lt
          (by simpa [Nat.cast_add, Nat.cast_one] using hu_lt.le)
      apply sInf_le
      exact ⟨t, ⟨htu_lower, htu⟩, ht_group.trans hu_group.symm⟩

/-- The Herbrand integrand is the reciprocal of the corresponding subgroup index. -/
theorem chapter05_herbrand_slope_eq_reciprocal_index
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (u : ℝ) (hu : 0 < u)
    (n : ℕ)
    (hindex : Nat.card (D.lowerGroup 0) =
      n * Nat.card (D.lowerGroup u)) :
    chapter05HerbrandSlope D u = (n : ℝ)⁻¹ := by
  rw [chapter05HerbrandSlope, if_neg (not_le.mpr hu)]
  have h0 : 0 < Nat.card (D.lowerGroup 0) := Nat.card_pos
  have hu' : 0 < Nat.card (D.lowerGroup u) := Nat.card_pos
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at hindex
    omega
  have hindex' : (Nat.card (D.lowerGroup 0) : ℝ) =
      (n : ℝ) * (Nat.card (D.lowerGroup u) : ℝ) := by
    exact_mod_cast hindex
  rw [hindex']
  have huc : (Nat.card (D.lowerGroup u) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hu')
  simp [div_eq_mul_inv, mul_inv_rev, huc]

/-- Bijectivity of the Herbrand function under an explicit integrability input. -/
theorem chapter05_herbrand_bijective
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (_hintegrable : ∀ a b : ℝ,
      IntervalIntegrable (chapter05HerbrandSlope D) volume a b) :
    Function.Bijective (chapter05HerbrandFunction D) := by
  exact chapter05_herbrand_bijective_of_filtration D

/-- Under bijectivity, the inverse really is a two-sided inverse. -/
theorem chapter05_herbrand_inverse_spec
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) (v : ℝ) :
    chapter05HerbrandFunction D (chapter05HerbrandInverse D v) = v := by
  simpa [chapter05HerbrandInverse] using
    Function.rightInverse_invFun hbij.surjective v

theorem chapter05_herbrand_inverse_left_inverse
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) (u : ℝ) :
    chapter05HerbrandInverse D (chapter05HerbrandFunction D u) = u := by
  simpa [chapter05HerbrandInverse] using
    Function.leftInverse_invFun hbij.injective u

/-!
 The defining upper-numbering identities.  The `hbij` argument is kept
 explicit because `chapter05HerbrandInverse` is defined with `Function.invFun`
 so that statements can be drafted before the analytic bijectivity proof.
-/
theorem chapter05_upper_group_eq_lower_at_inverse
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (_hbij : Function.Bijective (chapter05HerbrandFunction D))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter05UpperRamificationGroup D v =
      D.lowerGroup (chapter05HerbrandInverse D v) := by
  clear _hbij
  simp [chapter05UpperRamificationGroup, hv]

theorem chapter05_upper_group_neg_one_eq_top
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter05UpperRamificationGroup D (-1 : ℝ) = ⊤ := by
  have hinv : chapter05HerbrandInverse D (-1) = (-1 : ℝ) := by
    calc
      chapter05HerbrandInverse D (-1) =
          chapter05HerbrandInverse D (chapter05HerbrandFunction D (-1)) := by
        rw [chapter05_herbrand_function_neg_one D]
      _ = -1 := chapter05_herbrand_inverse_left_inverse D hbij (-1)
  rw [chapter05UpperRamificationGroup, hinv]
  simp [chapter05_lower_group_neg_one_eq_top D]

theorem chapter05_upper_group_zero_eq_lower_zero
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter05UpperRamificationGroup D 0 = D.lowerGroup 0 := by
  have hinv : chapter05HerbrandInverse D 0 = (0 : ℝ) := by
    calc
      chapter05HerbrandInverse D 0 =
          chapter05HerbrandInverse D (chapter05HerbrandFunction D 0) := by
        rw [chapter05_herbrand_function_zero D]
      _ = 0 := chapter05_herbrand_inverse_left_inverse D hbij 0
  rw [chapter05UpperRamificationGroup, hinv]
  simp

theorem chapter05_upper_zero_plus_eq_lower_one
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter05UpperZeroPlus D = D.lowerGroup 1 := by
  have hF1_formula : chapter05HerbrandFunction D (1 : ℝ) =
      (Nat.card (D.lowerGroup 1) : ℝ) /
        (Nat.card (D.lowerGroup 0) : ℝ) := by
    simpa using (chapter05_herbrand_function_interval_formula D 1 le_rfl
      (by norm_num))
  have hF1_pos : 0 < chapter05HerbrandFunction D (1 : ℝ) := by
    rw [hF1_formula]
    exact div_pos (by exact_mod_cast Nat.card_pos) (by exact_mod_cast Nat.card_pos)
  rw [chapter05UpperZeroPlus, chapter05UpperRightLimit, chapter05RightLimit]
  apply le_antisymm
  · apply sSup_le
    intro K hK
    rcases hK with ⟨v, hv, rfl⟩
    have hvinv := chapter05_herbrand_inverse_spec D hbij v
    have hinv_pos : 0 < chapter05HerbrandInverse D v := by
      by_contra hinv_not
      have hinv_nonpos : chapter05HerbrandInverse D v ≤ 0 := le_of_not_gt hinv_not
      have hidentity := chapter05_herbrand_function_of_nonpositive D hinv_nonpos
      have hinv_eq : chapter05HerbrandInverse D v = v :=
        hidentity.symm.trans hvinv
      apply hinv_not
      rw [hinv_eq]
      exact hv
    have hvpos : 0 < v := hv
    rw [chapter05UpperRamificationGroup, if_pos (by linarith : (-1 : ℝ) ≤ v)]
    by_cases hinv_le : chapter05HerbrandInverse D v ≤ 1
    · have hgroup : D.lowerGroup (chapter05HerbrandInverse D v) =
      D.lowerGroup 1 := by
        simpa using D.lower_real_convention 0 _ (by simpa using hinv_pos)
          (by simpa using hinv_le)
      rw [hgroup]
    · exact D.lower_antitone (le_of_not_ge hinv_le)
  · have hmem : D.lowerGroup 1 ∈
        chapter05UpperRamificationGroup D '' Set.Ioi (0 : ℝ) := by
      refine ⟨chapter05HerbrandFunction D (1 : ℝ), hF1_pos, ?_⟩
      rw [chapter05UpperRamificationGroup, if_pos (by linarith)]
      rw [chapter05_herbrand_inverse_left_inverse D hbij]
    exact le_sSup hmem

theorem chapter05_upper_filtration_left_continuous_on_positive
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    chapter05LeftContinuousOnPositive (chapter05UpperRamificationGroup D) := by
  have hmono : StrictMonoOn (chapter05HerbrandFunction D) (Set.Ici (-1 : ℝ)) :=
    (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear D).2.1
  have hinv_domain : ∀ {v : ℝ}, (-1 : ℝ) ≤ v →
      (-1 : ℝ) ≤ chapter05HerbrandInverse D v := by
    intro v hv
    by_contra hnot
    have hlt : chapter05HerbrandInverse D v < (-1 : ℝ) := lt_of_not_ge hnot
    have hidentity := chapter05_herbrand_function_of_nonpositive D (by linarith)
    have hspec := chapter05_herbrand_inverse_spec D hbij v
    have hinv_eq : chapter05HerbrandInverse D v = v := hidentity.symm.trans hspec
    linarith
  have hinv_mono : ∀ {v w : ℝ}, (-1 : ℝ) ≤ v → (-1 : ℝ) ≤ w →
      v ≤ w → chapter05HerbrandInverse D v ≤ chapter05HerbrandInverse D w := by
    intro v w hv hw hvw
    by_contra hnot
    have hlt : chapter05HerbrandInverse D w <
        chapter05HerbrandInverse D v := lt_of_not_ge hnot
    have hstrict := hmono (hinv_domain hw) (hinv_domain hv) hlt
    have hspec_v := chapter05_herbrand_inverse_spec D hbij v
    have hspec_w := chapter05_herbrand_inverse_spec D hbij w
    linarith
  have hsame : ∀ {x : ℝ}, 0 < x → ∃ y : ℝ, 0 < y ∧ y < x ∧
      D.lowerGroup y = D.lowerGroup x := by
    intro x hx
    let n : ℕ := ⌊x⌋₊
    by_cases hinteger : x = (n : ℝ)
    · have hn_pos : 0 < n := by
        exact_mod_cast (by simpa [hinteger] using hx)
      let y : ℝ := x - (1 / 2 : ℝ)
      have hncast : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hyn : ((n - 1 : ℕ) : ℝ) < y := by
        dsimp [y]
        rw [hinteger, ← hncast]
        linarith
      have hyx : y < x := by
        dsimp [y]
        linarith
      have hy_pos : 0 < y := by
        dsimp [y]
        rw [hinteger]
        linarith
      have hsucc : n - 1 + 1 = n := by omega
      have hy_group : D.lowerGroup y = D.lowerGroup (n : ℝ) := by
        simpa [hsucc] using D.lower_real_convention (n - 1) y hyn
          (by simpa [hsucc] using (show y ≤ (n : ℝ) by
            dsimp [y]
            linarith))
      have hx_group : D.lowerGroup x = D.lowerGroup (n : ℝ) := by
        simpa [hsucc] using D.lower_real_convention (n - 1) x
          (by rw [hinteger]; rw [← hncast]; linarith)
          (by simp [hsucc, hinteger])
      exact ⟨y, hy_pos, hyx, hy_group.trans hx_group.symm⟩
    · have hn_le : (n : ℝ) ≤ x := Nat.floor_le (le_of_lt hx)
      have hn_lt : (n : ℝ) < x := lt_of_le_of_ne hn_le (Ne.symm hinteger)
      have hx_lt : x < (n : ℝ) + 1 := by
        simpa [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
      let y : ℝ := ((n : ℝ) + x) / 2
      have hyn : (n : ℝ) < y := by
        dsimp [y]
        linarith
      have hyx : y < x := by
        dsimp [y]
        linarith
      have hy_pos : 0 < y := by
        have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
        dsimp [y]
        linarith
      have hy_group : D.lowerGroup y = D.lowerGroup ((n + 1 : ℕ) : ℝ) := by
        exact D.lower_real_convention n y hyn (by simpa [Nat.cast_add, Nat.cast_one] using
          (show y ≤ (n : ℝ) + 1 by dsimp [y]; linarith))
      have hx_group : D.lowerGroup x = D.lowerGroup ((n + 1 : ℕ) : ℝ) := by
        exact D.lower_real_convention n x hn_lt
          (by simpa [Nat.cast_add, Nat.cast_one] using hx_lt.le)
      exact ⟨y, hy_pos, hyx, hy_group.trans hx_group.symm⟩
  rw [chapter05LeftContinuousOnPositive]
  intro u hu
  have hψ_pos : 0 < chapter05HerbrandInverse D u := by
    by_contra hnot
    have hnonpos : chapter05HerbrandInverse D u ≤ 0 := le_of_not_gt hnot
    have hidentity := chapter05_herbrand_function_of_nonpositive D hnonpos
    have hspec := chapter05_herbrand_inverse_spec D hbij u
    have hψ_eq : chapter05HerbrandInverse D u = u := hidentity.symm.trans hspec
    apply hnot
    rw [hψ_eq]
    exact hu
  have hUu : chapter05UpperRamificationGroup D u =
      D.lowerGroup (chapter05HerbrandInverse D u) :=
    chapter05_upper_group_eq_lower_at_inverse D hbij (by linarith)
  apply le_antisymm
  · apply le_sInf
    rintro K ⟨v, hv, rfl⟩
    have hv_domain : (-1 : ℝ) ≤ v := le_of_lt hv.1
    have hψ := hinv_mono hv_domain (by linarith) hv.2.le
    have hUv : chapter05UpperRamificationGroup D v =
        D.lowerGroup (chapter05HerbrandInverse D v) :=
      chapter05_upper_group_eq_lower_at_inverse D hbij hv_domain
    rw [hUu, hUv]
    exact D.lower_antitone hψ
  · obtain ⟨x, hx_pos, hx_lt, hx_group⟩ := hsame hψ_pos
    have hx_mem : (x : ℝ) ∈ Set.Ici (-1 : ℝ) := by
      change (-1 : ℝ) ≤ x
      linarith
    have hu_mem : chapter05HerbrandInverse D u ∈ Set.Ici (-1 : ℝ) :=
      hinv_domain (by linarith)
    have hFx_pos : 0 < chapter05HerbrandFunction D x := by
      have hstrict := hmono (by norm_num) hx_mem hx_pos
      simpa [chapter05_herbrand_function_zero D] using hstrict
    have hFx_lt : chapter05HerbrandFunction D x < u := by
      have hstrict := hmono hx_mem hu_mem hx_lt
      have hspec := chapter05_herbrand_inverse_spec D hbij u
      simpa [hspec] using hstrict
    have hUx : chapter05UpperRamificationGroup D
        (chapter05HerbrandFunction D x) = D.lowerGroup x := by
      rw [chapter05UpperRamificationGroup, if_pos (by linarith)]
      rw [chapter05_herbrand_inverse_left_inverse D hbij]
    have hmem : chapter05UpperRamificationGroup D u ∈
        chapter05UpperRamificationGroup D '' Set.Ioo (-1 : ℝ) u := by
      refine ⟨chapter05HerbrandFunction D x, ⟨by linarith, hFx_lt⟩, ?_⟩
      exact hUx.trans (hx_group.trans hUu.symm)
    exact sInf_le hmem

theorem chapter05_upper_filtration_antitone
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    Antitone (chapter05UpperRamificationGroup D) := by
  have hmono : StrictMonoOn (chapter05HerbrandFunction D) (Set.Ici (-1 : ℝ)) :=
    (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear D).2.1
  have hinv_domain : ∀ {v : ℝ}, (-1 : ℝ) ≤ v →
      (-1 : ℝ) ≤ chapter05HerbrandInverse D v := by
    intro v hv
    by_contra hnot
    have hlt : chapter05HerbrandInverse D v < (-1 : ℝ) := lt_of_not_ge hnot
    have hidentity := chapter05_herbrand_function_of_nonpositive D (by linarith)
    have hspec := chapter05_herbrand_inverse_spec D hbij v
    linarith
  intro v₁ v₂ hv₁₂
  by_cases hv₁ : (-1 : ℝ) ≤ v₁
  · have hv₂ : (-1 : ℝ) ≤ v₂ := hv₁.trans hv₁₂
    have hψ : chapter05HerbrandInverse D v₁ ≤
        chapter05HerbrandInverse D v₂ := by
      by_contra hnot
      have hlt : chapter05HerbrandInverse D v₂ <
          chapter05HerbrandInverse D v₁ := lt_of_not_ge hnot
      have hstrict := hmono
        (hinv_domain hv₂) (hinv_domain hv₁) hlt
      have hspec₁ := chapter05_herbrand_inverse_spec D hbij v₁
      have hspec₂ := chapter05_herbrand_inverse_spec D hbij v₂
      linarith
    simp only [chapter05UpperRamificationGroup, hv₁, hv₂]
    exact D.lower_antitone hψ
  · simp [chapter05UpperRamificationGroup, hv₁]

theorem chapter05_upper_group_normal
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (_hbij : Function.Bijective (chapter05HerbrandFunction D)) (v : ℝ) :
    (chapter05UpperRamificationGroup D v).Normal := by
  clear _hbij
  by_cases hv : (-1 : ℝ) ≤ v <;>
    simp [chapter05UpperRamificationGroup, hv, D.lower_normal]

theorem chapter05_lower_break_maps_to_upper_break
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (m : ℕ) (hm : chapter05LowerBreak D m) :
    chapter05UpperBreak D (chapter05HerbrandFunction D (m : ℝ)) := by
  have hmono : StrictMonoOn (chapter05HerbrandFunction D) (Set.Ici (-1 : ℝ)) :=
    (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear D).2.1
  have hinv_domain : ∀ {v : ℝ}, (-1 : ℝ) ≤ v →
      (-1 : ℝ) ≤ chapter05HerbrandInverse D v := by
    intro v hv
    by_contra hnot
    have hlt : chapter05HerbrandInverse D v < (-1 : ℝ) := lt_of_not_ge hnot
    have hidentity := chapter05_herbrand_function_of_nonpositive D (by linarith)
    have hspec := chapter05_herbrand_inverse_spec D hbij v
    have hψ_eq : chapter05HerbrandInverse D v = v := hidentity.symm.trans hspec
    linarith
  have hF_nonneg : ∀ j : ℕ, 0 ≤
      chapter05HerbrandFunction D (j : ℝ) := by
    intro j
    have hj_mem : (j : ℝ) ∈ Set.Ici (-1 : ℝ) := by
      change (-1 : ℝ) ≤ (j : ℝ)
      have hj_nonneg : (0 : ℝ) ≤ (j : ℝ) := by positivity
      linarith
    have hzero_mem : (0 : ℝ) ∈ Set.Ici (-1 : ℝ) := by norm_num
    have hzero_le : (0 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast Nat.zero_le j
    have hmono' := hmono.monotoneOn hzero_mem hj_mem hzero_le
    simpa [chapter05_herbrand_function_zero D] using hmono'
  have hU_at : ∀ j : ℕ,
      chapter05UpperRamificationGroup D
          (chapter05HerbrandFunction D (j : ℝ)) = D.lowerGroup (j : ℝ) := by
    intro j
    rw [chapter05UpperRamificationGroup, if_pos (by linarith [hF_nonneg j])]
    rw [chapter05_herbrand_inverse_left_inverse D hbij]
  have hF_step : chapter05HerbrandFunction D (m : ℝ) <
      chapter05HerbrandFunction D ((m + 1 : ℕ) : ℝ) := by
    apply hmono
    · change (-1 : ℝ) ≤ (m : ℝ)
      have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    · change (-1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ)
      have hm1_nonneg : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
      linarith
    norm_num
  have hright : chapter05UpperRightLimit D
      (chapter05HerbrandFunction D (m : ℝ)) = D.lowerGroup ((m + 1 : ℕ) : ℝ) := by
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      rcases hK with ⟨w, hw, rfl⟩
      have hw_dom : (-1 : ℝ) ≤ w := by
        have hv_nonneg := hF_nonneg m
        have hw_gt : chapter05HerbrandFunction D (m : ℝ) < w := hw
        linarith
      have hψ_gt : (m : ℝ) < chapter05HerbrandInverse D w := by
        by_contra hnot
        have hψ_le : chapter05HerbrandInverse D w ≤ (m : ℝ) := le_of_not_gt hnot
        have hψ_dom := hinv_domain hw_dom
        have hm_mem : (m : ℝ) ∈ Set.Ici (-1 : ℝ) := by
          change (-1 : ℝ) ≤ (m : ℝ)
          have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
          linarith
        have hFm_le := hmono.monotoneOn hψ_dom hm_mem hψ_le
        have hspec_w := chapter05_herbrand_inverse_spec D hbij w
        have hw_gt : chapter05HerbrandFunction D (m : ℝ) < w := hw
        linarith
      rw [chapter05UpperRamificationGroup, if_pos hw_dom]
      by_cases hψ_le : chapter05HerbrandInverse D w ≤
          ((m + 1 : ℕ) : ℝ)
      · have hgroup : D.lowerGroup (chapter05HerbrandInverse D w) =
            D.lowerGroup ((m + 1 : ℕ) : ℝ) := by
          exact D.lower_real_convention m _ hψ_gt
            (by simpa using hψ_le)
        rw [hgroup]
      · exact D.lower_antitone (le_of_not_ge hψ_le)
    · have hmem : D.lowerGroup ((m + 1 : ℕ) : ℝ) ∈
          chapter05UpperRamificationGroup D ''
            Set.Ioi (chapter05HerbrandFunction D (m : ℝ)) := by
        refine ⟨chapter05HerbrandFunction D ((m + 1 : ℕ) : ℝ), hF_step, ?_⟩
        exact hU_at (m + 1)
      exact le_sSup hmem
  have hv_nonneg := hF_nonneg m
  have hv_ne : chapter05HerbrandFunction D (m : ℝ) ≠ (-1 : ℝ) := by
    intro hv
    linarith
  rw [chapter05UpperBreak]
  refine ⟨by linarith, ?_⟩
  rw [if_neg hv_ne, hU_at m, hright]
  exact hm

/-!
  The preceding implication is the forward half of the break correspondence.
  Apart from the separate endpoint at `-1`, the real lower profile is constant
  on each `(m,m+1]`, so an upper jump can occur only when the inverse Herbrand
  parameter is an integer.  This is the reusable converse needed when upper
  breaks are converted back to the rational lower-data calculation.
-/
theorem chapter05_upper_break_iff_herbrand_image_of_lower_break
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    {v : ℝ} :
    chapter05UpperBreak D v ↔
      (v = (-1 : ℝ) ∧ D.lowerGroup 0 ≠ ⊤) ∨
        ∃ m : ℕ, chapter05LowerBreak D m ∧
          chapter05HerbrandFunction D (m : ℝ) = v := by
  classical
  have hmono : StrictMonoOn (chapter05HerbrandFunction D) (Set.Ici (-1 : ℝ)) :=
    (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear D).2.1
  have hinv_domain : ∀ {x : ℝ}, (-1 : ℝ) ≤ x →
      (-1 : ℝ) ≤ chapter05HerbrandInverse D x := by
    intro x hx
    by_contra hnot
    have hlt : chapter05HerbrandInverse D x < (-1 : ℝ) := lt_of_not_ge hnot
    have hidentity := chapter05_herbrand_function_of_nonpositive D (by linarith)
    have hspec := chapter05_herbrand_inverse_spec D hbij x
    have hxeq : chapter05HerbrandInverse D x = x := hidentity.symm.trans hspec
    linarith
  have hF_nonneg : ∀ n : ℕ, 0 ≤ chapter05HerbrandFunction D (n : ℝ) := by
    intro n
    have hn_mem : (n : ℝ) ∈ Set.Ici (-1 : ℝ) := by
      change (-1 : ℝ) ≤ (n : ℝ)
      have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    have hzero_mem : (0 : ℝ) ∈ Set.Ici (-1 : ℝ) := by norm_num
    have hnmono := hmono.monotoneOn hzero_mem hn_mem
      (by exact_mod_cast Nat.zero_le n)
    simpa [chapter05_herbrand_function_zero D] using hnmono
  have hF_nonneg_real : ∀ {z : ℝ}, 0 ≤ z →
      0 ≤ chapter05HerbrandFunction D z := by
    intro z hz
    have hz_mem : z ∈ Set.Ici (-1 : ℝ) := by
      exact le_trans (by norm_num) hz
    have hzero_mem : (0 : ℝ) ∈ Set.Ici (-1 : ℝ) := by norm_num
    have hmono' := hmono.monotoneOn hzero_mem hz_mem hz
    rw [chapter05_herbrand_function_zero D] at hmono'
    exact hmono'
  have hU_at : ∀ n : ℕ,
      chapter05UpperRamificationGroup D
          (chapter05HerbrandFunction D (n : ℝ)) = D.lowerGroup (n : ℝ) := by
    intro n
    rw [chapter05UpperRamificationGroup, if_pos (by linarith [hF_nonneg n])]
    rw [chapter05_herbrand_inverse_left_inverse D hbij]
  have hF_step : ∀ n : ℕ,
      chapter05HerbrandFunction D (n : ℝ) <
        chapter05HerbrandFunction D ((n + 1 : ℕ) : ℝ) := by
    intro n
    apply hmono
    · change (-1 : ℝ) ≤ (n : ℝ)
      have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    · change (-1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
      have hn_nonneg : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      linarith
    norm_num
  have hright_integer : ∀ n : ℕ,
      chapter05UpperRightLimit D (chapter05HerbrandFunction D (n : ℝ)) =
        D.lowerGroup ((n + 1 : ℕ) : ℝ) := by
    intro n
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      rcases hK with ⟨w, hw, rfl⟩
      have hw_dom : (-1 : ℝ) ≤ w := by
        have hw_gt : chapter05HerbrandFunction D (n : ℝ) < w := hw
        linarith [hF_nonneg n]
      have hψ_gt : (n : ℝ) < chapter05HerbrandInverse D w := by
        by_contra hnot
        have hψ_le : chapter05HerbrandInverse D w ≤ (n : ℝ) := le_of_not_gt hnot
        have hn_mem : (n : ℝ) ∈ Set.Ici (-1 : ℝ) := by
          change (-1 : ℝ) ≤ (n : ℝ)
          have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
          linarith
        have hψ_le_F := hmono.monotoneOn (hinv_domain hw_dom) hn_mem hψ_le
        have hspec_w := chapter05_herbrand_inverse_spec D hbij w
        have hw_gt : chapter05HerbrandFunction D (n : ℝ) < w := hw
        linarith
      rw [chapter05UpperRamificationGroup, if_pos hw_dom]
      by_cases hψ_le : chapter05HerbrandInverse D w ≤
          ((n + 1 : ℕ) : ℝ)
      · have hgroup : D.lowerGroup (chapter05HerbrandInverse D w) =
            D.lowerGroup ((n + 1 : ℕ) : ℝ) := by
          exact D.lower_real_convention n _ hψ_gt
            (by simpa using hψ_le)
        rw [hgroup]
      · exact D.lower_antitone (le_of_not_ge hψ_le)
    · have hmem : D.lowerGroup ((n + 1 : ℕ) : ℝ) ∈
          chapter05UpperRamificationGroup D ''
            Set.Ioi (chapter05HerbrandFunction D (n : ℝ)) := by
        refine ⟨chapter05HerbrandFunction D ((n + 1 : ℕ) : ℝ), hF_step n,
          hU_at (n + 1)⟩
      exact le_sSup hmem
  have hright_noninteger : ∀ {x : ℝ}, 0 ≤ x →
      (∀ n : ℕ, x ≠ (n : ℝ)) →
      chapter05UpperRightLimit D (chapter05HerbrandFunction D x) =
        D.lowerGroup ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    intro x hx_nonneg hnot_nat
    let n : ℕ := ⌊x⌋₊
    have hn_le : (n : ℝ) ≤ x := by
      exact Nat.floor_le hx_nonneg
    have hn_lt : (n : ℝ) < x := by
      exact lt_of_le_of_ne hn_le (Ne.symm (hnot_nat n))
    have hx_lt : x < (n : ℝ) + 1 := by
      simpa [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
    have hU_x : chapter05UpperRamificationGroup D
        (chapter05HerbrandFunction D x) =
        D.lowerGroup ((n + 1 : ℕ) : ℝ) := by
      have hFx : 0 ≤ chapter05HerbrandFunction D x :=
        hF_nonneg_real hx_nonneg
      rw [chapter05UpperRamificationGroup, if_pos (by linarith)]
      rw [chapter05_herbrand_inverse_left_inverse D hbij]
      exact D.lower_real_convention n x hn_lt
        (by simpa [Nat.cast_add, Nat.cast_one] using hx_lt.le)
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      rcases hK with ⟨w, hw, rfl⟩
      have hw_dom : (-1 : ℝ) ≤ w := by
        have hw_gt : chapter05HerbrandFunction D x < w := hw
        have hFx : 0 ≤ chapter05HerbrandFunction D x :=
          hF_nonneg_real hx_nonneg
        linarith
      have hψ_gt : x < chapter05HerbrandInverse D w := by
        by_contra hnot
        have hψ_le : chapter05HerbrandInverse D w ≤ x := le_of_not_gt hnot
        have hx_mem : x ∈ Set.Ici (-1 : ℝ) := by
          exact le_trans (by norm_num) hx_nonneg
        have hψ_le_F := hmono.monotoneOn (hinv_domain hw_dom) hx_mem hψ_le
        have hspec_w := chapter05_herbrand_inverse_spec D hbij w
        have hw_gt : chapter05HerbrandFunction D x < w := hw
        linarith [hψ_le_F, hspec_w]
      have hnψ : (n : ℝ) < chapter05HerbrandInverse D w :=
        hn_lt.trans hψ_gt
      rw [chapter05UpperRamificationGroup, if_pos hw_dom]
      by_cases hψ_le : chapter05HerbrandInverse D w ≤
          ((n + 1 : ℕ) : ℝ)
      · have hgroup : D.lowerGroup (chapter05HerbrandInverse D w) =
            D.lowerGroup ((n + 1 : ℕ) : ℝ) := by
          exact D.lower_real_convention n _ hnψ
            (by simpa using hψ_le)
        rw [hgroup]
      · exact D.lower_antitone (le_of_not_ge hψ_le)
    · let y : ℝ := ((n : ℝ) + 1 + x) / 2
      have hxy : x < y := by
        dsimp [y]
        linarith
      have hy_lt : y < (n : ℝ) + 1 := by
        dsimp [y]
        linarith
      have hy_pos : 0 < y := by
        have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
        dsimp [y]
        linarith
      have hy_group : D.lowerGroup y = D.lowerGroup ((n + 1 : ℕ) : ℝ) := by
        exact D.lower_real_convention n y (by linarith) (by simpa [Nat.cast_add, Nat.cast_one] using hy_lt.le)
      have hFy : chapter05HerbrandFunction D x <
          chapter05HerbrandFunction D y := by
        apply hmono
        · have hx_mem : x ∈ Set.Ici (-1 : ℝ) := by
            exact le_trans (by norm_num) hx_nonneg
          exact hx_mem
        · have hy_mem : y ∈ Set.Ici (-1 : ℝ) := by
            exact le_trans (by norm_num) (le_of_lt hy_pos)
          exact hy_mem
        exact hxy
      have hmem : D.lowerGroup ((n + 1 : ℕ) : ℝ) ∈
          chapter05UpperRamificationGroup D ''
            Set.Ioi (chapter05HerbrandFunction D x) := by
        refine ⟨chapter05HerbrandFunction D y, hFy, ?_⟩
        have hFy_nonneg : 0 ≤ chapter05HerbrandFunction D y :=
          hF_nonneg_real (le_of_lt hy_pos)
        rw [chapter05UpperRamificationGroup, if_pos (by linarith)]
        rw [chapter05_herbrand_inverse_left_inverse D hbij]
        exact hy_group
      simpa [n] using le_sSup hmem
  constructor
  · intro hv
    have hv_dom := hv.1
    have hv_cond := hv.2
    by_cases hv_minus : v = (-1 : ℝ)
    · left
      exact ⟨hv_minus, by simpa [hv_minus] using hv_cond⟩
    · have hv_gt : (-1 : ℝ) < v := lt_of_le_of_ne hv_dom (Ne.symm hv_minus)
      have hv_cond' : chapter05UpperRamificationGroup D v ≠
          chapter05UpperRightLimit D v := by
        simpa [hv_minus] using hv_cond
      have hψ_dom := hinv_domain hv_dom
      have hspec := chapter05_herbrand_inverse_spec D hbij v
      have hψ_nonneg : 0 ≤ chapter05HerbrandInverse D v := by
        by_contra hnot
        have hψ_neg : chapter05HerbrandInverse D v < 0 := lt_of_not_ge hnot
        have hUtop : chapter05UpperRamificationGroup D v = ⊤ := by
          rw [chapter05UpperRamificationGroup, if_pos hv_dom]
          exact D.lower_neg _ hψ_dom hψ_neg
        have hright_top : chapter05UpperRightLimit D v = ⊤ := by
          rw [chapter05UpperRightLimit, chapter05RightLimit]
          apply le_antisymm
          · exact sSup_le (fun _ _ => le_top)
          · have hψ_eq : chapter05HerbrandFunction D
                (chapter05HerbrandInverse D v) =
                chapter05HerbrandInverse D v :=
              chapter05_herbrand_function_of_nonpositive D (le_of_lt hψ_neg)
            have hv_eq : v = chapter05HerbrandInverse D v :=
              hspec.symm.trans hψ_eq
            let y : ℝ := chapter05HerbrandInverse D v / 2
            have hyv : v < chapter05HerbrandFunction D y := by
              have hFy : chapter05HerbrandFunction D y = y := by
                exact chapter05_herbrand_function_of_nonpositive D (by
                  dsimp [y]
                  linarith)
              rw [hFy]
              dsimp [y]
              linarith
            have hy_dom : (-1 : ℝ) ≤ y := by
              dsimp [y]
              linarith
            have hy_neg : y < 0 := by
              dsimp [y]
              linarith
            have htop_mem : (⊤ : Subgroup G) ∈
                chapter05UpperRamificationGroup D '' Set.Ioi v := by
              refine ⟨chapter05HerbrandFunction D y, hyv, ?_⟩
              have hFy_dom : (-1 : ℝ) ≤ chapter05HerbrandFunction D y := by
                rw [chapter05_herbrand_function_of_nonpositive D (le_of_lt hy_neg)]
                exact hy_dom
              rw [chapter05UpperRamificationGroup, if_pos hFy_dom]
              rw [chapter05_herbrand_inverse_left_inverse D hbij]
              exact D.lower_neg y hy_dom hy_neg
            exact le_sSup htop_mem
        exact hv_cond' (hUtop.trans hright_top.symm)
      by_cases hnat : ∃ n : ℕ,
          chapter05HerbrandInverse D v = (n : ℝ)
      · rcases hnat with ⟨n, hn⟩
        have hv_repr : chapter05HerbrandFunction D (n : ℝ) = v := by
          simpa [hn] using hspec
        have hbreak_groups : chapter05LowerBreak D n := by
          rw [chapter05LowerBreak]
          intro heq
          apply hv_cond'
          rw [← hv_repr, hU_at n, hright_integer n, heq]
        exact Or.inr ⟨n, hbreak_groups, hv_repr⟩
      · have hright := hright_noninteger hψ_nonneg (by
          intro n hn
          exact hnat ⟨n, hn⟩)
        have hnot_nat' : ∀ n : ℕ,
            chapter05HerbrandInverse D v ≠ (n : ℝ) := by
          intro n hn
          exact hnat ⟨n, hn⟩
        have hU : chapter05UpperRamificationGroup D v =
            D.lowerGroup ((⌊chapter05HerbrandInverse D v⌋₊ + 1 : ℕ) : ℝ) := by
          calc
            chapter05UpperRamificationGroup D v =
                chapter05UpperRamificationGroup D
                  (chapter05HerbrandFunction D
                    (chapter05HerbrandInverse D v)) := by rw [hspec]
            _ = D.lowerGroup (chapter05HerbrandInverse D v) := by
              have hFψ_nonneg : 0 ≤ chapter05HerbrandFunction D
                  (chapter05HerbrandInverse D v) :=
                hF_nonneg_real hψ_nonneg
              rw [chapter05UpperRamificationGroup, if_pos (by linarith)]
              rw [chapter05_herbrand_inverse_left_inverse D hbij]
            _ = D.lowerGroup
                ((⌊chapter05HerbrandInverse D v⌋₊ + 1 : ℕ) : ℝ) := by
              exact D.lower_real_convention _ _
                (lt_of_le_of_ne (Nat.floor_le hψ_nonneg)
                  (Ne.symm (hnot_nat' _)))
                (by simpa [Nat.cast_add, Nat.cast_one] using
                  (Nat.lt_floor_add_one (chapter05HerbrandInverse D v)).le)
        have hright' : chapter05UpperRightLimit D v =
            D.lowerGroup ((⌊chapter05HerbrandInverse D v⌋₊ + 1 : ℕ) : ℝ) := by
          simpa only [hspec] using hright
        exact (hv_cond' (hU.trans hright'.symm)).elim
  · rintro (⟨hv, hnot⟩ | ⟨m, hm, rfl⟩)
    · rw [chapter05UpperBreak, hv]
      rw [if_pos rfl]
      exact ⟨by norm_num, hnot⟩
    · exact chapter05_lower_break_maps_to_upper_break D hbij m hm

theorem chapter05_upper_breaks_finite
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D)) :
    (chapter05UpperBreakSet D).Finite := by
  classical
  let B : Set ℕ := {m | chapter05LowerBreak D m}
  have hBfinite : B.Finite := by
    have hrange : (Set.range (fun σ : G => D.displacement σ - 1)).Finite :=
      Set.finite_range _
    apply hrange.subset
    intro m hm
    change chapter05LowerBreak D m at hm
    rw [chapter05LowerBreak] at hm
    have hle : D.lowerGroup ((m + 1 : ℕ) : ℝ) ≤
        D.lowerGroup (m : ℝ) := by
      apply D.lower_antitone
      norm_num
    have hnotle : ¬D.lowerGroup (m : ℝ) ≤
        D.lowerGroup ((m + 1 : ℕ) : ℝ) := by
      intro hle'
      exact hm (le_antisymm hle' hle)
    have hex : ∃ σ, σ ∈ D.lowerGroup (m : ℝ) ∧
        σ ∉ D.lowerGroup ((m + 1 : ℕ) : ℝ) := by
      by_contra h
      apply hnotle
      intro σ hσm
      by_contra hσnot
      exact h ⟨σ, hσm, hσnot⟩
    obtain ⟨σ, hσm, hσnot⟩ := hex
    have hσ : σ ≠ 1 := by
      intro hσone
      subst σ
      exact hσnot (D.lowerGroup ((m + 1 : ℕ) : ℝ)).one_mem
    have hdisp : m + 1 ≤ D.displacement σ :=
      (D.lower_nat_mem_iff hσ m).mp hσm
    have hdisp_next : ¬m + 1 + 1 ≤ D.displacement σ := by
      intro h
      apply hσnot
      exact (D.lower_nat_mem_iff hσ (m + 1)).mpr h
    have hdisp_eq : D.displacement σ = m + 1 := by
      omega
    refine ⟨σ, ?_⟩
    simp [hdisp_eq]
  have himage :
      (fun m : ℕ => chapter05HerbrandFunction D (m : ℝ)) '' B |>.Finite :=
    hBfinite.image _
  have hunion :
      (({(-1 : ℝ)} : Set ℝ) ∪
        (fun m : ℕ => chapter05HerbrandFunction D (m : ℝ)) '' B).Finite := by
    exact Set.toFinite {(-1 : ℝ)} |>.union himage
  apply hunion.subset
  intro v hv
  rcases (chapter05_upper_break_iff_herbrand_image_of_lower_break D hbij).mp hv with
    hneg | ⟨m, hm, hFm⟩
  · exact Or.inl (by simpa using hneg.1)
  · exact Or.inr ⟨m, hm, hFm⟩

theorem chapter05_upper_break_is_rational
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    {v : ℝ} (hv : chapter05UpperBreak D v) :
    chapter05UpperBreakIsRational v := by
  rcases (chapter05_upper_break_iff_herbrand_image_of_lower_break D hbij).mp hv with
    hneg | ⟨m, hm, hFm⟩
  · rcases hneg with ⟨hnegv, _⟩
    refine ⟨(-1 : ℚ), ?_⟩
    rw [hnegv]
    norm_num
  · let q : ℚ :=
      (Finset.sum (Finset.Icc 1 m)
          (fun j => (Nat.card (D.lowerGroup (j : ℝ)) : ℚ))) /
        (Nat.card (D.lowerGroup 0) : ℚ)
    refine ⟨q, ?_⟩
    rw [← hFm, chapter05_herbrand_function_interval_formula D m le_rfl
      (by norm_num)]
    simp [q]

theorem chapter05_first_positive_upper_break_exists
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hbij : Function.Bijective (chapter05HerbrandFunction D))
    (hwild : D.lowerGroup 1 ≠ ⊥) :
    ∃ r : ℝ, 0 < r ∧ chapter05UpperBreak D r ∧
      ∀ s : ℝ, 0 < s → chapter05UpperBreak D s → r ≤ s := by
  classical
  obtain ⟨b, hb⟩ := D.lower_eventually_trivial
  have hextriv : ∃ n : ℕ, D.lowerGroup (n : ℝ) = ⊥ := by
    refine ⟨b, ?_⟩
    exact hb b le_rfl
  let n : ℕ := Nat.find hextriv
  have hntriv : D.lowerGroup (n : ℝ) = ⊥ := by
    simpa [n] using Nat.find_spec hextriv
  have hnot_triv_before : ∀ k : ℕ, k < n →
      D.lowerGroup (k : ℝ) ≠ ⊥ := by
    intro k hk hktriv
    have hle : n ≤ k := by
      simpa [n] using Nat.find_min' hextriv hktriv
    omega
  have hnot_triv_zero : D.lowerGroup 0 ≠ ⊥ := by
    intro hzero
    apply hwild
    have hle : D.lowerGroup (1 : ℝ) ≤ D.lowerGroup 0 := by
      apply D.lower_antitone
      norm_num
    rw [hzero] at hle
    exact le_antisymm hle bot_le
  have hn_ne_zero : n ≠ 0 := by
    intro hn
    have hntriv0 : D.lowerGroup 0 = ⊥ := by
      simpa [hn] using hntriv
    exact hnot_triv_zero hntriv0
  have hn_ne_one : n ≠ 1 := by
    intro hn
    have hntriv1 : D.lowerGroup 1 = ⊥ := by
      simpa [hn] using hntriv
    exact hwild hntriv1
  have hn_gt_one : 1 < n := by omega
  let m : ℕ := n - 1
  have hm_pos : 0 < m := by
    dsimp [m]
    omega
  have hm_not_triv : D.lowerGroup (m : ℝ) ≠ ⊥ := by
    apply hnot_triv_before m
    dsimp [m]
    omega
  have hm_break : chapter05LowerBreak D m := by
    rw [chapter05LowerBreak]
    intro heq
    apply hm_not_triv
    rw [heq]
    have hmn : m + 1 = n := by
      dsimp [m]
      omega
    rw [hmn]
    exact hntriv
  have hexpos : ∃ k : ℕ, 0 < k ∧ chapter05LowerBreak D k :=
    ⟨m, hm_pos, hm_break⟩
  let k : ℕ := Nat.find hexpos
  have hk_spec : 0 < k ∧ chapter05LowerBreak D k := by
    simpa [k] using Nat.find_spec hexpos
  have hk_min : ∀ j : ℕ, 0 < j ∧ chapter05LowerBreak D j → k ≤ j := by
    intro j hj
    simpa [k] using Nat.find_min' hexpos hj
  have hsum_pos : 0 <
      Finset.sum (Finset.Icc 1 k)
        (fun j => (Nat.card (D.lowerGroup (j : ℝ)) : ℝ)) := by
    have hk_one : 1 ≤ k := by omega
    have hmem : 1 ∈ Finset.Icc 1 k := by
      exact Finset.mem_Icc.mpr ⟨le_rfl, hk_one⟩
    have hterm : 0 < (Nat.card (D.lowerGroup (1 : ℝ)) : ℝ) := by
      exact_mod_cast Nat.card_pos
    have hle : (Nat.card (D.lowerGroup (1 : ℝ)) : ℝ) ≤
        Finset.sum (Finset.Icc 1 k)
          (fun j => (Nat.card (D.lowerGroup (j : ℝ)) : ℝ)) := by
      simpa using (Finset.single_le_sum
        (s := Finset.Icc (1 : ℕ) k)
        (f := fun j : ℕ => (Nat.card (D.lowerGroup (j : ℝ)) : ℝ))
        (a := 1)
        (fun j _ => (Nat.cast_nonneg _ : (0 : ℝ) ≤
          (Nat.card (D.lowerGroup (j : ℝ)) : ℝ))) hmem)
    exact lt_of_lt_of_le hterm hle
  have hFk_formula : chapter05HerbrandFunction D (k : ℝ) =
      (Finset.sum (Finset.Icc 1 k)
        (fun j => (Nat.card (D.lowerGroup (j : ℝ)) : ℝ))) /
        (Nat.card (D.lowerGroup 0) : ℝ) := by
    simpa using (chapter05_herbrand_function_interval_formula D k le_rfl
      (by norm_num))
  have hden_pos : 0 < (Nat.card (D.lowerGroup 0) : ℝ) := by
    exact_mod_cast Nat.card_pos
  have hFk_pos : 0 < chapter05HerbrandFunction D (k : ℝ) := by
    rw [hFk_formula]
    exact div_pos hsum_pos hden_pos
  have hbreak_k : chapter05UpperBreak D
      (chapter05HerbrandFunction D (k : ℝ)) :=
    chapter05_lower_break_maps_to_upper_break D hbij k hk_spec.2
  refine ⟨chapter05HerbrandFunction D (k : ℝ), hFk_pos, hbreak_k, ?_⟩
  intro s hs_pos hs_break
  rcases (chapter05_upper_break_iff_herbrand_image_of_lower_break D hbij).mp
      hs_break with hneg | ⟨j, hj_break, hj_value⟩
  · linarith [hneg.1]
  · have hj_pos : 0 < j := by
      by_contra hj_not
      have hj_zero : j = 0 := Nat.eq_zero_of_not_pos hj_not
      subst j
      have hj_value' : chapter05HerbrandFunction D (0 : ℝ) = s := by
        simpa using hj_value
      rw [chapter05_herbrand_function_zero D] at hj_value'
      linarith
    have hkj : k ≤ j := hk_min j ⟨hj_pos, hj_break⟩
    have hmono :=
      (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear D).2.1
    have hk_mem : (k : ℝ) ∈ Set.Ici (-1 : ℝ) := by
      change (-1 : ℝ) ≤ (k : ℝ)
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      linarith
    have hj_mem : (j : ℝ) ∈ Set.Ici (-1 : ℝ) := by
      change (-1 : ℝ) ≤ (j : ℝ)
      have : (0 : ℝ) ≤ (j : ℝ) := by positivity
      linarith
    have hkj_real : (k : ℝ) ≤ (j : ℝ) := by exact_mod_cast hkj
    exact (hmono.monotoneOn hk_mem hj_mem hkj_real).trans_eq hj_value

/-- The first congruence group is inertia in the canonical Book 2 realization. -/
theorem chapter05_canonical_first_group_eq_inertia
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05RamificationGroupInG A 1 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG
        F A := by
  rw [chapter05RamificationGroupInG,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FirstRamificationGroup_eq_inertia
      (F := F) (E := E) A]

/-- The zeroth canonical group is the ambient decomposition group. -/
theorem chapter05_canonical_zero_group_eq_decomposition
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05RamificationGroupInG A 0 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        F A := by
  rw [chapter05RamificationGroupInG,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ZerothRamificationGroup_eq_top
      (F := F) (E := E) A]
  ext σ
  simp

end
end LastLib.Book03RamificationTheory.Chapter05
