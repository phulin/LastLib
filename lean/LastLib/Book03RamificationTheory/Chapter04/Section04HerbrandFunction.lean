import LastLib.Book03RamificationTheory.Chapter04.Dependencies
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Piecewise

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
  simp [chapter04HerbrandFunction, hu]

private theorem chapter04_real_lower_group_antitone
    {G : Type*} [Group G]
    (F : Chapter04LowerFiltration G) :
    Antitone (chapter04RealLowerGroup F) := by
  intro u v huv
  by_cases hvneg : v < 0
  · have huneg : u < 0 := lt_of_le_of_lt huv hvneg
    simp [chapter04RealLowerGroup, hvneg, huneg]
  · have hv0 : 0 ≤ v := le_of_not_gt hvneg
    by_cases huneg : u < 0
    · simp [chapter04RealLowerGroup, huneg]
    · have hu0 : 0 ≤ u := le_of_not_gt huneg
      have hcu : 0 ≤ Int.ceil u := Int.ceil_nonneg hu0
      have hcv : 0 ≤ Int.ceil v := Int.ceil_nonneg hv0
      have hcu' :
          chapter04RealLowerGroup F u = chapter04LowerGroup F (Int.ceil u) := by
        simp [chapter04RealLowerGroup, huneg,
          chapter04LowerGroup_of_nonnegative F hcu]
      have hcv' :
          chapter04RealLowerGroup F v = chapter04LowerGroup F (Int.ceil v) := by
        simp [chapter04RealLowerGroup, hvneg,
          chapter04LowerGroup_of_nonnegative F hcv]
      rw [hcu', hcv']
      exact chapter04LowerGroup_mono_anti F (by omega) (Int.ceil_mono huv)

private theorem chapter04_herbrand_integrand_antitone
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    Antitone (chapter04HerbrandIntegrand F) := by
  intro u v huv
  by_cases hvneg : v < 0
  · have huneg : u < 0 := lt_of_le_of_lt huv hvneg
    simp [chapter04HerbrandIntegrand, chapter04RealLowerGroup, hvneg, huneg]
  · have hv0 : 0 ≤ v := le_of_not_gt hvneg
    by_cases huneg : u < 0
    · have hcv : 0 ≤ Int.ceil v := Int.ceil_nonneg hv0
      have hvg :
          chapter04RealLowerGroup F v = chapter04LowerGroup F (Int.ceil v) := by
        simp [chapter04RealLowerGroup, hvneg,
          chapter04LowerGroup_of_nonnegative F hcv]
      have hzero :
          F.lower 0 = chapter04LowerGroup F 0 := by
        symm
        exact chapter04LowerGroup_of_nonnegative F le_rfl
      have hvg_le :
          chapter04RealLowerGroup F v ≤ F.lower 0 := by
        rw [hvg, hzero]
        exact chapter04LowerGroup_mono_anti F (by omega) (by omega)
      have hne :
          (chapter04RealLowerGroup F v).relIndex (F.lower 0) ≠ 0 := by
        have hfin :
            (chapter04RealLowerGroup F v).IsFiniteRelIndex (F.lower 0) :=
          Subgroup.isFiniteRelIndex_of_finiteIndex
        exact hfin.relIndex_ne_zero
      have hrel :
          (1 : ℝ) ≤
            ((chapter04RealLowerGroup F v).relIndex (F.lower 0) : ℝ) := by
        have hrel' :=
          Subgroup.relIndex_le_of_le_left hvg_le hne
        rw [Subgroup.relIndex_self] at hrel'
        exact_mod_cast hrel'
      have hpos :
          0 < ((chapter04RealLowerGroup F v).relIndex (F.lower 0) : ℝ) :=
        lt_of_lt_of_le zero_lt_one hrel
      simpa [chapter04HerbrandIntegrand, chapter04RealLowerGroup, huneg] using
        (inv_le_inv₀ hpos zero_lt_one).2 hrel
    · have hu0 : 0 ≤ u := le_of_not_gt huneg
      have hcu : 0 ≤ Int.ceil u := Int.ceil_nonneg hu0
      have hcv : 0 ≤ Int.ceil v := Int.ceil_nonneg hv0
      have hgu :
          chapter04RealLowerGroup F u = chapter04LowerGroup F (Int.ceil u) := by
        simp [chapter04RealLowerGroup, huneg,
          chapter04LowerGroup_of_nonnegative F hcu]
      have hgv :
          chapter04RealLowerGroup F v = chapter04LowerGroup F (Int.ceil v) := by
        simp [chapter04RealLowerGroup, hvneg,
          chapter04LowerGroup_of_nonnegative F hcv]
      have hgv_le : chapter04RealLowerGroup F v ≤ chapter04RealLowerGroup F u := by
        rw [hgu, hgv]
        exact chapter04LowerGroup_mono_anti F (by omega) (Int.ceil_mono huv)
      have hne_u :
          (chapter04RealLowerGroup F u).relIndex (F.lower 0) ≠ 0 := by
        have hfin :
            (chapter04RealLowerGroup F u).IsFiniteRelIndex (F.lower 0) :=
          Subgroup.isFiniteRelIndex_of_finiteIndex
        exact hfin.relIndex_ne_zero
      have hne_v :
          (chapter04RealLowerGroup F v).relIndex (F.lower 0) ≠ 0 := by
        have hfin :
            (chapter04RealLowerGroup F v).IsFiniteRelIndex (F.lower 0) :=
          Subgroup.isFiniteRelIndex_of_finiteIndex
        exact hfin.relIndex_ne_zero
      have hrel :
          (chapter04RealLowerGroup F u).relIndex (F.lower 0) ≤
            (chapter04RealLowerGroup F v).relIndex (F.lower 0) :=
        Subgroup.relIndex_le_of_le_left hgv_le hne_v
      have hpos_u :
          0 < ((chapter04RealLowerGroup F u).relIndex (F.lower 0) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hne_u
      have hpos_v :
          0 < ((chapter04RealLowerGroup F v).relIndex (F.lower 0) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hne_v
      exact (inv_le_inv₀ hpos_v hpos_u).2 (by exact_mod_cast hrel)

private theorem chapter04_herbrand_integrand_on_unit
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (n : ℕ) {t : ℝ}
    (ht : (n : ℝ) < t) (ht' : t ≤ (n + 1 : ℕ)) :
    chapter04HerbrandIntegrand F t = chapter04HerbrandSlope F n := by
  have hnat : ∀ a b : ℕ, a ≤ b → F.lower b ≤ F.lower a := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | @step b hab ih => exact (F.descending b).trans ih
  have hsub : F.lower (n + 1) ≤ F.lower 0 := by
    exact hnat 0 (n + 1) (Nat.zero_le _)
  have hrel := Subgroup.relIndex_mul_index hsub
  have hA := Subgroup.index_mul_card (F.lower (n + 1))
  have hB := Subgroup.index_mul_card (F.lower 0)
  have hidxpos : 0 < (F.lower 0).index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := F.lower 0))
  have hcard :
      (F.lower (n + 1)).relIndex (F.lower 0) * Nat.card (F.lower (n + 1)) =
        Nat.card (F.lower 0) := by
    apply Nat.eq_of_mul_eq_mul_left hidxpos
    calc
      (F.lower 0).index *
          ((F.lower (n + 1)).relIndex (F.lower 0) * Nat.card (F.lower (n + 1))) =
          ((F.lower (n + 1)).relIndex (F.lower 0) * (F.lower 0).index) *
            Nat.card (F.lower (n + 1)) := by ring
      _ = (F.lower (n + 1)).index * Nat.card (F.lower (n + 1)) := by rw [hrel]
      _ = Nat.card G := hA
      _ = (F.lower 0).index * Nat.card (F.lower 0) := hB.symm
  have hrelpos : 0 < (F.lower (n + 1)).relIndex (F.lower 0) := by
    have hcard0pos : 0 < Nat.card (F.lower 0) := Nat.card_pos
    apply Nat.pos_of_ne_zero
    intro hzero
    have : Nat.card (F.lower 0) = 0 := by simpa [hzero] using hcard.symm
    exact (Nat.ne_of_gt hcard0pos) this
  have hcard_real :
      ((F.lower (n + 1)).relIndex (F.lower 0) : ℝ) * Nat.card (F.lower (n + 1)) =
        Nat.card (F.lower 0) := by
    exact_mod_cast hcard
  rw [chapter04HerbrandIntegrand,
    chapter04RealLowerGroup_on_right_closed_unit_interval F n ht ht']
  unfold chapter04HerbrandSlope
  have hcard0ne : (Nat.card (F.lower 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < Nat.card (F.lower 0) from Nat.card_pos))
  apply (eq_div_iff hcard0ne).2
  rw [← hcard_real]
  field_simp [ne_of_gt hrelpos]

/-- The closed piecewise-linear formula on the interval `[m,m+1]`. -/
theorem chapter04_herbrand_function_piecewise_formula
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (m : ℕ) {u : ℝ}
    (hm : (m : ℝ) ≤ u) (hm' : u ≤ (m + 1 : ℕ)) :
    chapter04HerbrandFunction F u =
      chapter04HerbrandPiecewiseValue F m u := by
  have hunit : ∀ n : ℕ,
      (∫ t in (n : ℝ)..(n + 1 : ℕ), chapter04HerbrandIntegrand F t) =
        chapter04HerbrandSlope F n := by
    intro n
    calc
      (∫ t in (n : ℝ)..(n + 1 : ℕ), chapter04HerbrandIntegrand F t) =
          ∫ t in (n : ℝ)..(n + 1 : ℕ), (fun _ => chapter04HerbrandSlope F n) t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        have ht' : (n : ℝ) < t := by simpa using ht.1
        have ht'' : t ≤ (n + 1 : ℕ) := by simpa using ht.2
        exact chapter04_herbrand_integrand_on_unit F n ht' ht''
      _ = chapter04HerbrandSlope F n := by simp
  have hsum_integrals :
      (∑ n ∈ Finset.range m,
          ∫ t in (n : ℝ)..(n + 1 : ℕ), chapter04HerbrandIntegrand F t) =
        ∫ t in (0 : ℝ)..(m : ℝ), chapter04HerbrandIntegrand F t := by
    simpa only [Nat.cast_zero] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := chapter04HerbrandIntegrand F)
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (a := fun n : ℕ => (n : ℝ)) (n := m) (by
          intro n hn
          exact (chapter04_herbrand_integrand_antitone F).intervalIntegrable))
  have hsum_slopes : ∀ q : ℕ,
      (∑ n ∈ Finset.range q, chapter04HerbrandSlope F n) =
        (1 / (Nat.card (F.lower 0) : ℝ)) *
          ∑ j ∈ Finset.Icc 1 q, (Nat.card (F.lower j) : ℝ) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]
        unfold chapter04HerbrandSlope
        ring
  have hsum_unit :
      (∑ n ∈ Finset.range m,
          ∫ t in (n : ℝ)..(n + 1 : ℕ), chapter04HerbrandIntegrand F t) =
        ∑ n ∈ Finset.range m, chapter04HerbrandSlope F n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hunit n
  have hlast :
      (∫ t in (m : ℝ)..u, chapter04HerbrandIntegrand F t) =
        (u - m) * chapter04HerbrandSlope F m := by
    calc
      (∫ t in (m : ℝ)..u, chapter04HerbrandIntegrand F t) =
          ∫ t in (m : ℝ)..u, (fun _ => chapter04HerbrandSlope F m) t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        have ht' : (m : ℝ) < t := by simpa [hm] using ht.1
        have ht2 : t ≤ u := by simpa [hm] using ht.2
        have ht'' : t ≤ (m + 1 : ℕ) := ht2.trans hm'
        exact chapter04_herbrand_integrand_on_unit F m ht' ht''
      _ = (u - m) * chapter04HerbrandSlope F m := by simp
  calc
    chapter04HerbrandFunction F u =
        ∫ t in (0 : ℝ)..u, chapter04HerbrandIntegrand F t :=
      chapter04_herbrand_function_integral_formula F
        (le_trans (Nat.cast_nonneg m) hm)
    _ = (∫ t in (0 : ℝ)..(m : ℝ), chapter04HerbrandIntegrand F t) +
          ∫ t in (m : ℝ)..u, chapter04HerbrandIntegrand F t := by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals
        (chapter04_herbrand_integrand_antitone F).intervalIntegrable
        (chapter04_herbrand_integrand_antitone F).intervalIntegrable
    _ = (∑ n ∈ Finset.range m,
          ∫ t in (n : ℝ)..(n + 1 : ℕ), chapter04HerbrandIntegrand F t) +
          ∫ t in (m : ℝ)..u, chapter04HerbrandIntegrand F t := by
      rw [hsum_integrals]
    _ = (∑ n ∈ Finset.range m, chapter04HerbrandSlope F n) +
          (u - m) * chapter04HerbrandSlope F m := by
      rw [hsum_unit, hlast]
    _ = chapter04HerbrandPiecewiseValue F m u := by
      rw [hsum_slopes]
      unfold chapter04HerbrandPiecewiseValue chapter04HerbrandSlope
      ring

/-- The slope on `(m,m+1)` is the ratio `|G_(m+1)| / |G₀|`. -/
theorem chapter04_herbrand_slope_on_interval
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (m : ℕ) {u v : ℝ}
    (hu : (m : ℝ) ≤ u) (hu' : u ≤ (m + 1 : ℕ))
    (hv : (m : ℝ) ≤ v) (hv' : v ≤ (m + 1 : ℕ)) :
    chapter04HerbrandFunction F u - chapter04HerbrandFunction F v =
      (u - v) * chapter04HerbrandSlope F m := by
  rw [chapter04_herbrand_function_piecewise_formula F m hu hu',
    chapter04_herbrand_function_piecewise_formula F m hv hv']
  unfold chapter04HerbrandPiecewiseValue chapter04HerbrandSlope
  ring

theorem chapter04_herbrand_slope_eq_first_ratio
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    chapter04HerbrandFunction F 1 =
      (Nat.card (F.lower 1) : ℝ) / Nat.card (F.lower 0) := by
  rw [chapter04_herbrand_function_piecewise_formula F 0 (u := 1) (by norm_num)
    (by norm_num)]
  unfold chapter04HerbrandPiecewiseValue
  simp
  rw [div_eq_mul_inv]
  ring

/-- Herbrand slopes decrease when the lower groups shrink. -/
theorem chapter04_herbrand_slope_antitone
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {m n : ℕ} (hmn : m ≤ n) :
    chapter04HerbrandSlope F n ≤ chapter04HerbrandSlope F m := by
  have hnat : ∀ a b : ℕ, a ≤ b → F.lower b ≤ F.lower a := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | @step b hab ih => exact (F.descending b).trans ih
  have hcard : Nat.card (F.lower (n + 1)) ≤ Nat.card (F.lower (m + 1)) := by
    apply Subgroup.card_le_of_le
    exact hnat (m + 1) (n + 1) (Nat.add_le_add_right hmn 1)
  have hcard_real :
      (Nat.card (F.lower (n + 1)) : ℝ) ≤ Nat.card (F.lower (m + 1)) := by
    exact_mod_cast hcard
  have hden : 0 ≤ (Nat.card (F.lower 0) : ℝ) := by
    exact_mod_cast (Nat.zero_le (Nat.card (F.lower 0)))
  unfold chapter04HerbrandSlope
  exact div_le_div_of_nonneg_right hcard_real hden

/-- The clock never runs faster than the lower clock: every positive slope is
at most one. -/
theorem chapter04_herbrand_slope_le_one
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (m : ℕ) :
    chapter04HerbrandSlope F m ≤ 1 := by
  have hnat : ∀ a b : ℕ, a ≤ b → F.lower b ≤ F.lower a := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | @step b hab ih => exact (F.descending b).trans ih
  have hcard : Nat.card (F.lower (m + 1)) ≤ Nat.card (F.lower 0) := by
    apply Subgroup.card_le_of_le
    exact hnat 0 (m + 1) (Nat.zero_le _)
  have hcard_real :
      (Nat.card (F.lower (m + 1)) : ℝ) ≤ Nat.card (F.lower 0) := by
    exact_mod_cast hcard
  have hden : 0 ≤ (Nat.card (F.lower 0) : ℝ) := by
    exact_mod_cast (Nat.zero_le (Nat.card (F.lower 0)))
  unfold chapter04HerbrandSlope
  exact div_le_one_of_le₀ hcard_real hden

/-- Positivity of the reciprocal index is the monotonicity input for the
Herbrand map. -/
theorem chapter04_herbrand_integrand_pos
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) (u : ℝ) :
    0 < chapter04HerbrandIntegrand F u := by
  by_cases hu : u < 0
  · simp [chapter04HerbrandIntegrand, chapter04RealLowerGroup, hu]
  · have hne :
        (chapter04RealLowerGroup F u).relIndex (F.lower 0) ≠ 0 := by
      have hfin :
          (chapter04RealLowerGroup F u).IsFiniteRelIndex (F.lower 0) :=
        Subgroup.isFiniteRelIndex_of_finiteIndex
      exact hfin.relIndex_ne_zero
    rw [chapter04HerbrandIntegrand]
    exact inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hne)

private theorem chapter04_herbrand_integral_continuous_on_nonnegative
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    ContinuousOn
      (fun u : ℝ => ∫ t in (0 : ℝ)..u, chapter04HerbrandIntegrand F t)
      (Set.Ici 0) := by
  intro x hx
  obtain ⟨b, hxb⟩ : ∃ b : ℝ, x < b := ⟨x + 1, by linarith⟩
  have hxb' : x ≤ b := hxb.le
  have hInt :
      MeasureTheory.IntegrableOn (chapter04HerbrandIntegrand F) (Set.Icc (0 : ℝ) b)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have hx0 : 0 ≤ x := hx
    have hxb0 : 0 ≤ b := hx0.trans hxb.le
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        hxb0).mp
        (chapter04_herbrand_integrand_antitone F).intervalIntegrable
  have hInt' :
      MeasureTheory.IntegrableOn (chapter04HerbrandIntegrand F) (Set.uIcc (0 : ℝ) b)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have hx0 : 0 ≤ x := hx
    have hxb0 : 0 ≤ b := hx0.trans hxb.le
    simpa [Set.uIcc_of_le hxb0] using hInt
  have hcont :=
    intervalIntegral.continuousOn_primitive_interval
      (f := chapter04HerbrandIntegrand F)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (a := (0 : ℝ)) (b := b) hInt'
  have hx' : x ∈ Set.Icc (0 : ℝ) b := ⟨hx, hxb'⟩
  have hx'' : x ∈ Set.uIcc (0 : ℝ) b := by
    have hx0 : 0 ≤ x := hx
    have hxb0 : 0 ≤ b := hx0.trans hxb.le
    simpa [Set.uIcc_of_le hxb0] using hx'
  refine (hcont.continuousWithinAt hx'').mono_of_mem_nhdsWithin ?_
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Set.Iio b, Iio_mem_nhds hxb, ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := hy.2
  have hyb : y ≤ b := hy.1.le
  have hx0 : 0 ≤ x := hx
  have hxb0 : 0 ≤ b := hx0.trans hxb.le
  simpa [Set.uIcc_of_le hxb0] using ⟨hy0, hyb⟩

private theorem chapter04_herbrand_integrand_lower_bound
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {t : ℝ} (ht : 0 ≤ t) :
    1 / (Nat.card (F.lower 0) : ℝ) ≤ chapter04HerbrandIntegrand F t := by
  have hsub : chapter04RealLowerGroup F t ≤ F.lower 0 := by
    have h := chapter04_real_lower_group_antitone F ht
    rw [chapter04RealLowerGroup_zero] at h
    exact h
  have hne :
      (chapter04RealLowerGroup F t).relIndex (F.lower 0) ≠ 0 := by
    have hfin :
        (chapter04RealLowerGroup F t).IsFiniteRelIndex (F.lower 0) :=
      Subgroup.isFiniteRelIndex_of_finiteIndex
    exact hfin.relIndex_ne_zero
  have hdvd :
      (chapter04RealLowerGroup F t).relIndex (F.lower 0) ∣ Nat.card (F.lower 0) :=
    Subgroup.relIndex_dvd_card (chapter04RealLowerGroup F t) (F.lower 0)
  have hrle :
      (chapter04RealLowerGroup F t).relIndex (F.lower 0) ≤ Nat.card (F.lower 0) :=
    Nat.le_of_dvd Nat.card_pos hdvd
  have hrpos :
      0 < ((chapter04RealLowerGroup F t).relIndex (F.lower 0) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hrle' :
      ((chapter04RealLowerGroup F t).relIndex (F.lower 0) : ℝ) ≤
        Nat.card (F.lower 0) := by
    exact_mod_cast hrle
  have hdiv := one_div_le_one_div_of_le hrpos hrle'
  simpa [chapter04HerbrandIntegrand, one_div] using hdiv

/-- The integral map is continuous and strictly increasing on the full
ramification domain, and its range is the same half-line. -/
theorem chapter04_herbrand_is_homeomorphism_on_domain
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    ContinuousOn (chapter04HerbrandFunction F) (Set.Ici (-1 : ℝ)) ∧
    StrictMonoOn (chapter04HerbrandFunction F) (Set.Ici (-1 : ℝ)) ∧
      Set.range (fun u : Set.Ici (-1 : ℝ) => chapter04HerbrandFunction F u) =
        Set.Ici (-1 : ℝ) := by
  have hcont_nonneg := chapter04_herbrand_integral_continuous_on_nonnegative F
  have hcont : ContinuousOn (chapter04HerbrandFunction F) (Set.Ici (-1 : ℝ)) := by
    change ContinuousOn
      (fun u : ℝ => if 0 ≤ u then
        ∫ t in (0 : ℝ)..u, chapter04HerbrandIntegrand F t else u)
      (Set.Ici (-1 : ℝ))
    apply ContinuousOn.if
    · intro a ha
      have ha' : a ∈ frontier (Set.Ici (0 : ℝ)) := by
        change a ∈ frontier {a : ℝ | 0 ≤ a}
        exact ha.2
      rw [frontier_Ici] at ha'
      have ha0 : a = 0 := by simpa using ha'
      subst a
      simp
    · refine hcont_nonneg.mono ?_
      intro a ha
      have ha' : a ∈ closure (Set.Ici (0 : ℝ)) := by
        change a ∈ closure {a : ℝ | 0 ≤ a}
        exact ha.2
      rw [isClosed_Ici.closure_eq] at ha'
      exact ha'
    · exact continuousOn_id.mono (fun a ha => ha.1)
  have hmono :
      StrictMonoOn (chapter04HerbrandFunction F) (Set.Ici (-1 : ℝ)) := by
    intro x hx y hy hxy
    by_cases hy0 : y ≤ 0
    · rw [chapter04HerbrandFunction_of_nonpositive F hy0,
        chapter04HerbrandFunction_of_nonpositive F (le_trans hxy.le hy0)]
      exact hxy
    · have hypos : 0 < y := lt_of_not_ge hy0
      by_cases hxneg : x < 0
      · have hfypos : 0 < chapter04HerbrandFunction F y := by
          rw [chapter04_herbrand_function_integral_formula F hypos.le]
          exact intervalIntegral.intervalIntegral_pos_of_pos
            (a := (0 : ℝ)) (b := y)
            (chapter04_herbrand_integrand_antitone F).intervalIntegrable
            (chapter04_herbrand_integrand_pos F) hypos
        rw [chapter04HerbrandFunction_of_nonpositive F hxneg.le]
        exact lt_of_le_of_lt hxneg.le hfypos
      · have hx0 : 0 ≤ x := le_of_not_gt hxneg
        have hdiff :
            chapter04HerbrandFunction F y - chapter04HerbrandFunction F x =
              ∫ t in x..y, chapter04HerbrandIntegrand F t := by
          rw [chapter04_herbrand_function_integral_formula F hypos.le,
            chapter04_herbrand_function_integral_formula F hx0]
          have hadd := intervalIntegral.integral_add_adjacent_intervals
            (f := chapter04HerbrandIntegrand F)
            (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
            (a := (0 : ℝ)) (b := x) (c := y)
            (chapter04_herbrand_integrand_antitone F).intervalIntegrable
            (chapter04_herbrand_integrand_antitone F).intervalIntegrable
          linarith
        have hpos : 0 < ∫ t in x..y, chapter04HerbrandIntegrand F t :=
          intervalIntegral.intervalIntegral_pos_of_pos
            (a := x) (b := y)
            (chapter04_herbrand_integrand_antitone F).intervalIntegrable
            (chapter04_herbrand_integrand_pos F) hxy
        exact sub_pos.mp (hdiff ▸ hpos)
  have hbound : ∀ {u : ℝ}, 0 ≤ u →
      u / (Nat.card (F.lower 0) : ℝ) ≤ chapter04HerbrandFunction F u := by
    intro u hu
    rw [chapter04_herbrand_function_integral_formula F hu]
    have hmono_int := intervalIntegral.integral_mono_on
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (a := (0 : ℝ)) (b := u)
      (f := fun _ : ℝ => 1 / (Nat.card (F.lower 0) : ℝ))
      (g := chapter04HerbrandIntegrand F) hu
      intervalIntegrable_const
      (chapter04_herbrand_integrand_antitone F).intervalIntegrable (by
        intro t ht
        exact chapter04_herbrand_integrand_lower_bound F ht.1)
    simpa [div_eq_mul_inv, mul_comm] using hmono_int
  have htendsto :
      Filter.Tendsto (chapter04HerbrandFunction F) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono' Filter.atTop
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
      exact hbound hu
    · have hden : 0 < (Nat.card (F.lower 0) : ℝ) := by
        exact_mod_cast (show 0 < Nat.card (F.lower 0) from Nat.card_pos)
      simpa using
        (Filter.tendsto_div_const_atTop_of_pos hden).mpr Filter.tendsto_id
  have hrange_subset :
      Set.range (fun u : Set.Ici (-1 : ℝ) => chapter04HerbrandFunction F u) ⊆
      Set.Ici (-1 : ℝ) := by
    rintro y ⟨u, rfl⟩
    change -1 ≤ chapter04HerbrandFunction F (u : ℝ)
    by_cases hu0 : (u : ℝ) ≤ 0
    · rw [chapter04HerbrandFunction_of_nonpositive F hu0]
      exact u.property
    · have hu0' : 0 ≤ (u : ℝ) := (lt_of_not_ge hu0).le
      have hnonneg : 0 ≤ chapter04HerbrandFunction F (u : ℝ) := by
        exact le_trans (div_nonneg hu0' (by positivity)) (hbound hu0')
      exact le_trans (by norm_num) hnonneg
  have hcont_nonneg' :
      ContinuousOn (chapter04HerbrandFunction F) (Set.Ici (0 : ℝ)) := by
    apply hcont_nonneg.congr
    intro x hx
    exact chapter04_herbrand_function_integral_formula F hx
  have hrange_superset :
      Set.Ici (-1 : ℝ) ⊆
        Set.range (fun u : Set.Ici (-1 : ℝ) => chapter04HerbrandFunction F u) := by
    intro y hy
    by_cases hy0 : y ≤ 0
    · refine ⟨⟨y, hy⟩, ?_⟩
      change chapter04HerbrandFunction F y = y
      rw [chapter04HerbrandFunction_of_nonpositive F hy0]
    · have hy0' : 0 ≤ y := (lt_of_not_ge hy0).le
      have hy0'' : y ∈ Set.Ici (chapter04HerbrandFunction F 0) := by
        rw [chapter04HerbrandFunction_zero F]
        exact hy0'
      rcases intermediate_value_Ici
          (a := (0 : ℝ))
          (f := chapter04HerbrandFunction F)
          hcont_nonneg' htendsto hy0'' with ⟨u, hu, hfu⟩
      have hu_domain : (-1 : ℝ) ≤ u := le_trans (by norm_num) hu
      refine ⟨⟨u, hu_domain⟩, ?_⟩
      exact hfu
  exact ⟨hcont, hmono, Set.Subset.antisymm hrange_subset hrange_superset⟩

private theorem chapter04_herbrand_function_strictMono
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    StrictMono (chapter04HerbrandFunction F) := by
  intro x y hxy
  by_cases hy0 : y ≤ 0
  · rw [chapter04HerbrandFunction_of_nonpositive F hy0,
      chapter04HerbrandFunction_of_nonpositive F (le_trans hxy.le hy0)]
    exact hxy
  · have hypos : 0 < y := lt_of_not_ge hy0
    by_cases hxneg : x < 0
    · have hfypos : 0 < chapter04HerbrandFunction F y := by
        rw [chapter04_herbrand_function_integral_formula F hypos.le]
        exact intervalIntegral.intervalIntegral_pos_of_pos
          (a := (0 : ℝ)) (b := y)
          (chapter04_herbrand_integrand_antitone F).intervalIntegrable
          (chapter04_herbrand_integrand_pos F) hypos
      rw [chapter04HerbrandFunction_of_nonpositive F hxneg.le]
      exact lt_of_le_of_lt hxneg.le hfypos
    · have hx0 : 0 ≤ x := le_of_not_gt hxneg
      have hdiff :
          chapter04HerbrandFunction F y - chapter04HerbrandFunction F x =
            ∫ t in x..y, chapter04HerbrandIntegrand F t := by
        rw [chapter04_herbrand_function_integral_formula F hypos.le,
          chapter04_herbrand_function_integral_formula F hx0]
        have hadd := intervalIntegral.integral_add_adjacent_intervals
          (f := chapter04HerbrandIntegrand F)
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          (a := (0 : ℝ)) (b := x) (c := y)
          (chapter04_herbrand_integrand_antitone F).intervalIntegrable
          (chapter04_herbrand_integrand_antitone F).intervalIntegrable
        linarith
      have hpos : 0 < (∫ t in x..y, chapter04HerbrandIntegrand F t) :=
        intervalIntegral.intervalIntegral_pos_of_pos
          (a := x) (b := y)
          (chapter04_herbrand_integrand_antitone F).intervalIntegrable
          (chapter04_herbrand_integrand_pos F) hxy
      exact sub_pos.mp (hdiff ▸ hpos)

private theorem chapter04_herbrand_function_injective
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    Function.Injective (chapter04HerbrandFunction F) :=
  (chapter04_herbrand_function_strictMono F).injective

private theorem chapter04_herbrand_function_surjective
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) :
    Function.Surjective (chapter04HerbrandFunction F) := by
  intro y
  by_cases hy : y < -1
  · refine ⟨y, ?_⟩
    rw [chapter04HerbrandFunction_of_nonpositive F (le_trans hy.le (by norm_num))]
  · have hy' : -1 ≤ y := le_of_not_gt hy
    have hmem : y ∈ Set.range
        (fun u : Set.Ici (-1 : ℝ) => chapter04HerbrandFunction F u) := by
      rw [(chapter04_herbrand_is_homeomorphism_on_domain F).2.2]
      exact hy'
    rcases hmem with ⟨u, hfu⟩
    exact ⟨u, hfu⟩

/-- The inverse notation is a genuine two-sided inverse on the book's domain. -/
theorem chapter04_herbrand_inverse_left_inverse
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {u : ℝ} (hu : -1 ≤ u) :
    chapter04HerbrandInverse F (chapter04HerbrandFunction F u) = u := by
  have hdomain : u ∈ Set.Ici (-1 : ℝ) := hu
  change Function.invFun (chapter04HerbrandFunction F)
      (chapter04HerbrandFunction F u) = u
  exact Function.leftInverse_invFun (chapter04_herbrand_function_injective F) u

theorem chapter04_herbrand_inverse_right_inverse
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G) {u : ℝ} (hu : -1 ≤ u) :
    chapter04HerbrandFunction F (chapter04HerbrandInverse F u) = u := by
  have hdomain : u ∈ Set.Ici (-1 : ℝ) := hu
  change chapter04HerbrandFunction F
      (Function.invFun (chapter04HerbrandFunction F) u) = u
  exact Function.rightInverse_invFun (chapter04_herbrand_function_surjective F) u

/-- The Herbrand function only sees the inertia group and the positive lower
filtration.  Changes in the unramified quotient leave it unchanged. -/
theorem chapter04_herbrand_depends_only_on_inertia_and_positive_filtration
    {G : Type*} [Group G] [Finite G]
    (F F' : Chapter04LowerFiltration G)
    (hzero : F.lower 0 = F'.lower 0)
    (hpositive : ∀ n : ℕ, 1 ≤ n → F.lower n = F'.lower n) :
    ∀ u : ℝ, chapter04HerbrandFunction F u = chapter04HerbrandFunction F' u := by
  have hgroup : ∀ t : ℝ,
      chapter04RealLowerGroup F t = chapter04RealLowerGroup F' t := by
    intro t
    by_cases htneg : t < 0
    · simp [chapter04RealLowerGroup, htneg]
    · have ht0 : 0 ≤ t := le_of_not_gt htneg
      by_cases htzero : t = 0
      · subst t
        rw [chapter04RealLowerGroup_zero F,
          chapter04RealLowerGroup_zero F', hzero]
      · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
        have hceil_nonneg : 0 ≤ Int.ceil t := Int.ceil_nonneg ht0
        have hceil_pos : 0 < Int.ceil t := Int.ceil_pos.mpr htpos
        have hto_cast : ((Int.ceil t).toNat : ℤ) = Int.ceil t :=
          Int.toNat_of_nonneg hceil_nonneg
        have hto_pos : 0 < (Int.ceil t).toNat := by
          by_contra hnot
          have hto_zero : (Int.ceil t).toNat = 0 :=
            Nat.eq_zero_of_not_pos hnot
          rw [hto_zero] at hto_cast
          omega
        have hto_one : 1 ≤ (Int.ceil t).toNat := hto_pos
        have hF :
            chapter04RealLowerGroup F t = F.lower (Int.ceil t).toNat := by
          simp [chapter04RealLowerGroup, htneg]
        have hF' :
            chapter04RealLowerGroup F' t = F'.lower (Int.ceil t).toNat := by
          simp [chapter04RealLowerGroup, htneg]
        rw [hF, hF', hpositive _ hto_one]
  have hintegrand : ∀ t : ℝ,
      chapter04HerbrandIntegrand F t = chapter04HerbrandIntegrand F' t := by
    intro t
    unfold chapter04HerbrandIntegrand
    rw [hgroup t, hzero]
  intro u
  by_cases hu : u ≤ 0
  · rw [chapter04HerbrandFunction_of_nonpositive F hu,
      chapter04HerbrandFunction_of_nonpositive F' hu]
  · have hu0 : 0 ≤ u := (lt_of_not_ge hu).le
    rw [chapter04_herbrand_function_integral_formula F hu0,
      chapter04_herbrand_function_integral_formula F' hu0]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with t ht
    exact hintegrand t

private theorem chapter04_ceil_toNat_pos {t : ℝ} (ht : 0 < t) :
    1 ≤ (Int.ceil t).toNat := by
  have ht0 : 0 ≤ t := ht.le
  have hceil_nonneg : 0 ≤ Int.ceil t := Int.ceil_nonneg ht0
  have hceil_pos : 0 < Int.ceil t := Int.ceil_pos.mpr ht
  have hto_cast : ((Int.ceil t).toNat : ℤ) = Int.ceil t :=
    Int.toNat_of_nonneg hceil_nonneg
  have hto_pos : 0 < (Int.ceil t).toNat := by
    by_contra hnot
    have hto_zero : (Int.ceil t).toNat = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hto_zero] at hto_cast
    omega
  exact hto_pos

/-- In the tame totally ramified case, the positive filtration is trivial and
the Herbrand clock has constant slope `1 / |G₀|`. -/
theorem chapter04_tame_totally_ramified_herbrand_formula
    {G : Type*} [Group G] [Finite G]
    (F : Chapter04LowerFiltration G)
    (hzero : F.lower 0 = ⊤) (hone : F.lower 1 = ⊥)
    {u : ℝ} (hu : 0 < u) :
    chapter04HerbrandFunction F u =
      u / Nat.card (F.lower 0) := by
  have hnat : ∀ a b : ℕ, a ≤ b → F.lower b ≤ F.lower a := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | @step b hab ih => exact (F.descending b).trans ih
  have hbot : ∀ n : ℕ, 1 ≤ n → F.lower n = ⊥ := by
    intro n hn
    apply bot_unique
    rw [← hone]
    exact hnat 1 n hn
  have hu0 : 0 ≤ u := hu.le
  calc
    chapter04HerbrandFunction F u =
        ∫ t in (0 : ℝ)..u, chapter04HerbrandIntegrand F t :=
      chapter04_herbrand_function_integral_formula F hu0
    _ = ∫ t in (0 : ℝ)..u,
        (fun _ => 1 / (Nat.card (F.lower 0) : ℝ)) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with t ht
      have ht' : t ∈ Set.Ioc (0 : ℝ) u := by
        simpa [Set.uIoc_of_le hu0] using ht
      have htpos : 0 < t := ht'.1
      have hto_one : 1 ≤ (Int.ceil t).toNat :=
        chapter04_ceil_toNat_pos htpos
      rw [chapter04HerbrandIntegrand, chapter04RealLowerGroup]
      simp [not_lt.mpr htpos.le, hbot _ hto_one, hzero]
    _ = u / Nat.card (F.lower 0) := by simp [div_eq_mul_inv]

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
  have hzero : F.lower 0 = ⊤ :=
    hprofile.full_through_break 0 (Nat.zero_le _)
  have hp_real : 0 < (p : ℝ) := by
    exact_mod_cast hp
  have hcard : Nat.card G = p := by
    simpa [hzero] using hprofile.card_zero
  have hfull : ∀ {t : ℝ}, 0 < t → t ≤ (m : ℝ) →
      chapter04HerbrandIntegrand F t = 1 := by
    intro t htpos htm
    have hgroup :
        chapter04RealLowerGroup F (m : ℝ) ≤ chapter04RealLowerGroup F t := by
      exact chapter04_real_lower_group_antitone F htm
    rw [chapter04RealLowerGroup_at_integer F m,
      hprofile.full_through_break m le_rfl] at hgroup
    have htop : chapter04RealLowerGroup F t = ⊤ := top_unique hgroup
    simp [chapter04HerbrandIntegrand, htop, hzero]
  have htrivial : ∀ {t : ℝ}, (m : ℝ) < t →
      chapter04HerbrandIntegrand F t = 1 / p := by
    intro t htm
    have htpos : 0 < t :=
      lt_of_le_of_lt (Nat.cast_nonneg m) htm
    have hceil_nonneg : 0 ≤ Int.ceil t :=
      Int.ceil_nonneg htpos.le
    have hceil_ge : (m + 1 : ℤ) ≤ Int.ceil t := by
      rw [Int.le_ceil_iff]
      calc
        ((m + 1 : ℤ) : ℝ) - 1 = (m : ℝ) := by norm_num
        _ < t := htm
    have hcast_ge : ((m + 1 : ℕ) : ℤ) ≤ (Int.ceil t).toNat := by
      rw [Int.toNat_of_nonneg hceil_nonneg]
      exact hceil_ge
    have hnat_ge : m + 1 ≤ (Int.ceil t).toNat := by
      exact_mod_cast hcast_ge
    have hgroup : chapter04RealLowerGroup F t = ⊥ := by
      rw [chapter04RealLowerGroup, if_neg (not_lt.mpr htpos.le),
        hprofile.trivial_after_break _ hnat_ge]
    simp [chapter04HerbrandIntegrand, hgroup, hzero, hcard]
  have hleft : ∀ {v : ℝ}, 0 ≤ v → v ≤ (m : ℝ) →
      chapter04HerbrandFunction F v = v := by
    intro v hv0 hvm
    calc
      chapter04HerbrandFunction F v =
          ∫ t in (0 : ℝ)..v, chapter04HerbrandIntegrand F t :=
        chapter04_herbrand_function_integral_formula F hv0
      _ = ∫ t in (0 : ℝ)..v, (fun _ => (1 : ℝ)) t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        have ht' : t ∈ Set.Ioc (0 : ℝ) v := by
          simpa [Set.uIoc_of_le hv0] using ht
        exact hfull ht'.1 (ht'.2.trans hvm)
      _ = v := by simp
  constructor
  · intro hum
    exact hleft hu hum
  · intro hmu
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hleft_integral :
        (∫ t in (0 : ℝ)..(m : ℝ), chapter04HerbrandIntegrand F t) = m := by
      rw [← chapter04_herbrand_function_integral_formula F hm0]
      exact hleft hm0 le_rfl
    have hright_integral :
        (∫ t in (m : ℝ)..u, chapter04HerbrandIntegrand F t) =
          ∫ t in (m : ℝ)..u, (fun _ => (1 : ℝ) / p) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with t ht
      have ht' : t ∈ Set.Ioc (m : ℝ) u := by
        simpa [Set.uIoc_of_le hmu] using ht
      exact htrivial ht'.1
    calc
      chapter04HerbrandFunction F u =
          ∫ t in (0 : ℝ)..u, chapter04HerbrandIntegrand F t :=
        chapter04_herbrand_function_integral_formula F hu
      _ = (∫ t in (0 : ℝ)..(m : ℝ), chapter04HerbrandIntegrand F t) +
            ∫ t in (m : ℝ)..u, chapter04HerbrandIntegrand F t := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals
          (chapter04_herbrand_integrand_antitone F).intervalIntegrable
          (chapter04_herbrand_integrand_antitone F).intervalIntegrable
      _ = m + ∫ t in (m : ℝ)..u, (fun _ => (1 : ℝ) / p) t := by
        rw [hleft_integral, hright_integral]
      _ = m + (u - m) / p := by
        have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_real
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        field_simp [hp_ne]

end
end LastLib.Book03RamificationTheory.Chapter04
