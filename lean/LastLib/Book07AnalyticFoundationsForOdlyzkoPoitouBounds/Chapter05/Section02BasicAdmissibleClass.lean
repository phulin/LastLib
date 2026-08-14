import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Core
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05.Section01TransformConventions
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Section04PolesZerosAndGrowth
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Data.Finset.Sort

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

/-! ## 5.2. The basic admissible class -/

theorem chapter05_oneSidedDerivativeBV_iff
    {F : ℝ → ℝ} :
    Chapter05OneSidedDerivativeBV F ↔
      ∃ leftDerivative rightDerivative : ℝ → ℝ,
        (∀ x, HasDerivWithinAt F (leftDerivative x) (Iic x) x) ∧
          (∀ x, HasDerivWithinAt F (rightDerivative x) (Ici x) x) ∧
          BoundedVariationOn leftDerivative univ ∧
            BoundedVariationOn rightDerivative univ := Iff.rfl

/-!
The unit tent is the standard triangular example referred to in §5.2.  The
choice of width one is only a normalization of that example.
-/
def chapter05Triangle (x : ℝ) : ℝ := max (1 - |x|) 0

private theorem chapter05_boundedVariationOn_add {f g : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) :
    BoundedVariationOn (fun x => f x + g x) univ := by
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    (∑ i ∈ Finset.range n,
        edist ((fun x => f x + g x) (u (i + 1)))
          ((fun x => f x + g x) (u i))) ≤
      ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) +
          edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using
        (edist_add_add_le (f (u (i + 1))) (g (u (i + 1)))
          (f (u i)) (g (u i)))
    _ = (∑ i ∈ Finset.range n,
          edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn f univ + eVariationOn g univ := by
      gcongr
      · exact eVariationOn.sum_le hu hus
      · exact eVariationOn.sum_le hu hus

private theorem chapter05_boundedVariationOn_sub {f g : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) :
    BoundedVariationOn (fun x => f x - g x) univ := by
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    (∑ i ∈ Finset.range n,
        edist ((f - g) (u (i + 1))) ((f - g) (u i))) ≤
      ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) +
          edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [Pi.sub_apply, sub_eq_add_neg] using
        (edist_add_add_le (f (u (i + 1))) (-g (u (i + 1)))
          (f (u i)) (-g (u i)))
    _ = (∑ i ∈ Finset.range n,
          edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn f univ + eVariationOn g univ := by
      gcongr
      · exact eVariationOn.sum_le hu hus
      · exact eVariationOn.sum_le hu hus

private theorem chapter05_step_boundedVariationOn_le {r c : ℝ} (hc : 0 ≤ c) :
    BoundedVariationOn (fun x : ℝ => if r ≤ x then c else 0) univ := by
  have hmono : Monotone (fun x : ℝ => if r ≤ x then c else 0) := by
    intro x y hxy
    by_cases hx : r ≤ x
    · simp [hx, le_trans hx hxy]
    · by_cases hy : r ≤ y
      · simp [hx, hy, hc]
      · simp [hx, hy]
  apply (hmono.monotoneOn univ).boundedVariationOn (C := c)
  intro x hx
  by_cases h : r ≤ x
  · simp [h, abs_of_nonneg hc]
  · simpa [h] using hc

private theorem chapter05_step_boundedVariationOn_lt {r c : ℝ} (hc : 0 ≤ c) :
    BoundedVariationOn (fun x : ℝ => if r < x then c else 0) univ := by
  have hmono : Monotone (fun x : ℝ => if r < x then c else 0) := by
    intro x y hxy
    by_cases hx : r < x
    · simp [hx, lt_of_lt_of_le hx hxy]
    · by_cases hy : r < y
      · simp [hx, hy, hc]
      · simp [hx, hy]
  apply (hmono.monotoneOn univ).boundedVariationOn (C := c)
  intro x hx
  by_cases h : r < x
  · simp [h, abs_of_nonneg hc]
  · simpa [h] using hc

theorem chapter05_triangle_basically_admissible :
    Chapter05BasicallyAdmissible chapter05Triangle := by
  refine
    { even := ?_
      continuous := ?_
      compactSupport := ?_
      piecewiseC2 := ?_
      valueAtZero := ?_
      oneSidedDerivativeBV := ?_
      originCondition := ?_ }
  · intro x
    simp [chapter05Triangle, abs_neg]
  · change Continuous (fun x : ℝ => max (1 - |x|) 0)
    exact (continuous_const.sub continuous_abs).max continuous_const
  · apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
    apply Function.support_subset_iff'.mpr
    intro x hx
    by_cases hxleft : x < -1
    · have hxabs : 1 ≤ |x| := by
        rw [abs_of_neg (by linarith : x < 0)]
        linarith
      simp [chapter05Triangle, max_eq_right (by linarith : 1 - |x| ≤ 0)]
    · by_cases hxright : 1 < x
      · have hxabs : 1 ≤ |x| := by
          rw [abs_of_pos (by linarith : 0 < x)]
          linarith
        simp [chapter05Triangle, max_eq_right (by linarith : 1 - |x| ≤ 0)]
      · exact False.elim (hx ⟨le_of_not_gt hxleft, le_of_not_gt hxright⟩)
  · refine ⟨{-1, 0, 1}, by simp, ?_⟩
    intro x hx
    have hxneg1 : x ≠ -1 := by
      intro h
      apply hx
      simp [h]
    have hxzero : x ≠ 0 := by
      intro h
      apply hx
      simp [h]
    have hxone : x ≠ 1 := by
      intro h
      apply hx
      simp [h]
    by_cases hleft : x < -1
    · have heq : (fun y : ℝ => chapter05Triangle y) =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
        filter_upwards [Iio_mem_nhds hleft] with y hy
        have hy' : y < -1 := hy
        have hyabs : 1 ≤ |y| := by
          rw [abs_of_neg (by linarith : y < 0)]
          linarith
        simp [chapter05Triangle, max_eq_right (by linarith : 1 - |y| ≤ 0)]
      exact contDiffAt_const.congr_of_eventuallyEq heq
    · have hgtneg1 : -1 < x :=
        lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hxneg1)
      by_cases hmid : x < 0
      · have heq : (fun y : ℝ => chapter05Triangle y) =ᶠ[𝓝 x]
            (fun y : ℝ => 1 + y) := by
          filter_upwards [isOpen_Ioo.mem_nhds ⟨hgtneg1, hmid⟩] with y hy
          rcases hy with ⟨hylo, hyhi⟩
          have hyabs : |y| = -y := abs_of_neg hyhi
          have hnonneg : 0 ≤ 1 + y := by linarith
          simp [chapter05Triangle, hyabs, max_eq_left hnonneg]
        exact (contDiffAt_const.add contDiffAt_id).congr_of_eventuallyEq heq
      · have hgtzero : 0 < x := lt_of_le_of_ne (le_of_not_gt hmid) (Ne.symm hxzero)
        by_cases hright : x < 1
        · have heq : (fun y : ℝ => chapter05Triangle y) =ᶠ[𝓝 x]
              (fun y : ℝ => 1 - y) := by
            filter_upwards [isOpen_Ioo.mem_nhds ⟨hgtzero, hright⟩] with y hy
            rcases hy with ⟨hylo, hyhi⟩
            have hyabs : |y| = y := abs_of_pos hylo
            have hnonneg : 0 ≤ 1 - y := by linarith
            simp [chapter05Triangle, hyabs, max_eq_left hnonneg]
          exact (contDiffAt_const.sub contDiffAt_id).congr_of_eventuallyEq heq
        · have hgtone : 1 < x := lt_of_le_of_ne (le_of_not_gt hright) (Ne.symm hxone)
          have heq : (fun y : ℝ => chapter05Triangle y) =ᶠ[𝓝 x]
              (fun _ : ℝ => 0) := by
            filter_upwards [Ioi_mem_nhds hgtone] with y hy
            have hy' : 1 < y := hy
            have hyabs : 1 ≤ |y| := by
              rw [abs_of_pos (by linarith : 0 < y)]
              linarith
            simp [chapter05Triangle, max_eq_right (by linarith : 1 - |y| ≤ 0)]
          exact contDiffAt_const.congr_of_eventuallyEq heq
  · norm_num [chapter05Triangle]
  · let Dleft : ℝ → ℝ := fun x =>
      (if (-1 : ℝ) < x then 1 else 0) +
        (if (1 : ℝ) < x then 1 else 0) -
          (if (0 : ℝ) < x then 2 else 0)
    let Dright : ℝ → ℝ := fun x =>
      (if (-1 : ℝ) ≤ x then 1 else 0) +
        (if (1 : ℝ) ≤ x then 1 else 0) -
          (if (0 : ℝ) ≤ x then 2 else 0)
    have hleft_BV : BoundedVariationOn Dleft univ := by
      have hsum : BoundedVariationOn
          (fun x : ℝ => (if (-1 : ℝ) < x then (1 : ℝ) else 0) +
            (if (1 : ℝ) < x then (1 : ℝ) else 0)) univ :=
        chapter05_boundedVariationOn_add
          (f := fun x : ℝ => if (-1 : ℝ) < x then 1 else 0)
          (g := fun x : ℝ => if (1 : ℝ) < x then 1 else 0)
          (chapter05_step_boundedVariationOn_lt (r := -1) (c := 1) (by norm_num))
          (chapter05_step_boundedVariationOn_lt (r := 1) (c := 1) (by norm_num))
      simpa [Dleft] using
        chapter05_boundedVariationOn_sub
          (f := fun x : ℝ => (if (-1 : ℝ) < x then 1 else 0) +
            (if (1 : ℝ) < x then 1 else 0))
          (g := fun x : ℝ => if (0 : ℝ) < x then 2 else 0) hsum
          (chapter05_step_boundedVariationOn_lt (r := 0) (c := 2) (by norm_num))
    have hright_BV : BoundedVariationOn Dright univ := by
      have hsum : BoundedVariationOn
          (fun x : ℝ => (if (-1 : ℝ) ≤ x then (1 : ℝ) else 0) +
            (if (1 : ℝ) ≤ x then (1 : ℝ) else 0)) univ :=
        chapter05_boundedVariationOn_add
          (f := fun x : ℝ => if (-1 : ℝ) ≤ x then 1 else 0)
          (g := fun x : ℝ => if (1 : ℝ) ≤ x then 1 else 0)
          (chapter05_step_boundedVariationOn_le (r := -1) (c := 1) (by norm_num))
          (chapter05_step_boundedVariationOn_le (r := 1) (c := 1) (by norm_num))
      simpa [Dright] using
        chapter05_boundedVariationOn_sub
          (f := fun x : ℝ => (if (-1 : ℝ) ≤ x then 1 else 0) +
            (if (1 : ℝ) ≤ x then 1 else 0))
          (g := fun x : ℝ => if (0 : ℝ) ≤ x then 2 else 0) hsum
          (chapter05_step_boundedVariationOn_le (r := 0) (c := 2) (by norm_num))
    have hzeroL : ∀ y : ℝ, y ≤ -1 → chapter05Triangle y = 0 := by
      intro y hy
      unfold chapter05Triangle
      have hyneg : y < 0 := by linarith
      rw [abs_of_neg hyneg]
      apply max_eq_right
      linarith
    have hneg : ∀ y : ℝ, -1 ≤ y → y ≤ 0 →
        chapter05Triangle y = 1 + y := by
      intro y hyl hyu
      unfold chapter05Triangle
      rw [abs_of_nonpos hyu]
      rw [show 1 - -y = 1 + y by ring]
      apply max_eq_left
      linarith
    have hpos : ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
        chapter05Triangle y = 1 - y := by
      intro y hyl hyu
      unfold chapter05Triangle
      rw [abs_of_nonneg hyl]
      apply max_eq_left
      linarith
    have hzeroR : ∀ y : ℝ, 1 ≤ y → chapter05Triangle y = 0 := by
      intro y hy
      unfold chapter05Triangle
      rw [abs_of_nonneg (by linarith : 0 ≤ y)]
      apply max_eq_right
      linarith
    refine ⟨Dleft, Dright, ?_, ?_, hleft_BV, hright_BV⟩
    · intro x
      by_cases hleft : x ≤ -1
      · have hEq : chapter05Triangle =ᶠ[nhdsWithin x (Iic x)]
            (fun _ : ℝ => (0 : ℝ)) := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith : x < 0))]
            with y hy₁ hy₂
          exact hzeroL y (hy₁.trans hleft)
        have hder : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Iic x) x :=
          (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
        have hxEq := hzeroL x hleft
        have hleftnot : ¬ -1 < x := by linarith
        have h0not : ¬ 0 < x := by linarith
        have h1not : ¬ 1 < x := by linarith
        simpa [Dleft, hleftnot, h0not, h1not] using
          hder.congr_of_eventuallyEq hEq hxEq
      · have hleft' : -1 < x := lt_of_not_ge hleft
        by_cases hnonpos : x ≤ 0
        · have hEq : chapter05Triangle =ᶠ[nhdsWithin x (Iic x)]
              (fun y : ℝ => 1 + y) := by
            filter_upwards [self_mem_nhdsWithin,
              mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hleft')] with y hy₁ hy₂
            exact hneg y hy₂.le (hy₁.trans hnonpos)
          have hder : HasDerivWithinAt (fun y : ℝ => 1 + y) 1 (Iic x) x := by
            convert ((hasDerivAt_const x (1 : ℝ)).add
              (hasDerivAt_id x)).hasDerivWithinAt using 1
            · rfl
            · rfl
            · funext y
              simp [id]
            · ring
          have hxEq := hneg x hleft'.le hnonpos
          have h1not : ¬ 1 < x := by linarith
          have h0not : ¬ 0 < x := by linarith
          simpa [Dleft, hleft', h1not, h0not] using
            hder.congr_of_eventuallyEq hEq hxEq
        · have hxpositive : 0 < x := lt_of_not_ge hnonpos
          by_cases hinside : x ≤ 1
          · have hEq : chapter05Triangle =ᶠ[nhdsWithin x (Iic x)]
                (fun y : ℝ => 1 - y) := by
              filter_upwards [self_mem_nhdsWithin,
                mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hxpositive)] with y hy₁ hy₂
              exact hpos y hy₂.le (hy₁.trans hinside)
            have hder : HasDerivWithinAt (fun y : ℝ => 1 - y) (-1)
                (Iic x) x := by
              convert ((hasDerivAt_const x (1 : ℝ)).sub
                (hasDerivAt_id x)).hasDerivWithinAt using 1
              · rfl
              · rfl
              · funext y
                simp [id]
              · ring
            have hxEq := hpos x hxpositive.le hinside
            have h1not : ¬ 1 < x := by linarith
            have hcoef : Dleft x = -1 := by
              simp [Dleft, hleft', hxpositive, h1not]
              ring
            rw [hcoef]
            exact hder.congr_of_eventuallyEq hEq hxEq
          · have houtside : 1 < x := lt_of_not_ge hinside
            have hEq : chapter05Triangle =ᶠ[nhdsWithin x (Iic x)]
                (fun _ : ℝ => (0 : ℝ)) := by
              filter_upwards [self_mem_nhdsWithin,
                mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds houtside)] with y hy₁ hy₂
              exact hzeroR y hy₂.le
            have hder : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0
                (Iic x) x := (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
            have hxEq := hzeroR x houtside.le
            have hcoef : Dleft x = 0 := by
              simp [Dleft, hleft', houtside, hxpositive]
              ring
            rw [hcoef]
            exact hder.congr_of_eventuallyEq hEq hxEq
    · intro x
      by_cases hleft : x < -1
      · have hEq : chapter05Triangle =ᶠ[nhdsWithin x (Ici x)]
            (fun _ : ℝ => (0 : ℝ)) := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hleft)] with y hy₁ hy₂
          exact hzeroL y (le_of_lt hy₂)
        have hder : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Ici x) x :=
          (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
        have hxEq := hzeroL x (le_of_lt hleft)
        have hminus : ¬ (-1 : ℝ) ≤ x := by linarith
        have hzero : ¬ (0 : ℝ) ≤ x := by linarith
        have hone : ¬ (1 : ℝ) ≤ x := by linarith
        simpa [Dright, hminus, hzero, hone] using
          hder.congr_of_eventuallyEq hEq hxEq
      · have hleft' : -1 ≤ x := le_of_not_gt hleft
        by_cases hnegative : x < 0
        · have hEq : chapter05Triangle =ᶠ[nhdsWithin x (Ici x)]
              (fun y : ℝ => 1 + y) := by
            filter_upwards [self_mem_nhdsWithin,
              mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hnegative)] with y hy₁ hy₂
            exact hneg y (hleft'.trans hy₁) hy₂.le
          have hder : HasDerivWithinAt (fun y : ℝ => 1 + y) 1 (Ici x) x := by
            convert ((hasDerivAt_const x (1 : ℝ)).add
              (hasDerivAt_id x)).hasDerivWithinAt using 1
            · rfl
            · rfl
            · funext y
              simp [id]
            · ring
          have hxEq := hneg x hleft' (le_of_lt hnegative)
          have h1not : ¬ 1 ≤ x := by linarith
          have h0not : ¬ 0 ≤ x := by linarith
          simpa [Dright, hleft', h1not, h0not] using
            hder.congr_of_eventuallyEq hEq hxEq
        · have hxnonnegative : 0 ≤ x := le_of_not_gt hnegative
          by_cases hxzero : x = 0
          · subst x
            have hEq : chapter05Triangle =ᶠ[nhdsWithin 0 (Ici (0 : ℝ))]
                (fun y : ℝ => 1 - y) := by
              filter_upwards [self_mem_nhdsWithin,
                mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
                with y hy₁ hy₂
              exact hpos y hy₁ hy₂.le
            have hder : HasDerivWithinAt (fun y : ℝ => 1 - y) (-1)
                (Ici (0 : ℝ)) 0 := by
              convert ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
                (hasDerivAt_id (0 : ℝ))).hasDerivWithinAt using 1
              · rfl
              · rfl
              · funext y
                simp [id]
              · ring
            have hxEq := hpos 0 (by norm_num) (by norm_num)
            have hcoef : Dright 0 = -1 := by
              norm_num [Dright]
            rw [hcoef]
            exact hder.congr_of_eventuallyEq hEq hxEq
          · have hxpositive : 0 < x := lt_of_le_of_ne hxnonnegative (Ne.symm hxzero)
            by_cases hinside : x < 1
            · have hEq : chapter05Triangle =ᶠ[nhdsWithin x (Ici x)]
                  (fun y : ℝ => 1 - y) := by
                filter_upwards [mem_nhdsWithin_of_mem_nhds
                  (Ioo_mem_nhds hxpositive hinside)] with y hy
                exact hpos y (le_of_lt hy.1) (le_of_lt hy.2)
              have hder : HasDerivWithinAt (fun y : ℝ => 1 - y) (-1)
                  (Ici x) x := by
                convert ((hasDerivAt_const x (1 : ℝ)).sub
                  (hasDerivAt_id x)).hasDerivWithinAt using 1
                · rfl
                · rfl
                · funext y
                  simp [id]
                · ring
              have hxEq := hpos x hxpositive.le (le_of_lt hinside)
              have h1not : ¬ (1 : ℝ) ≤ x := by linarith
              have hcoef : Dright x = -1 := by
                norm_num [Dright, hleft', h1not, hxpositive.le]
              rw [hcoef]
              exact hder.congr_of_eventuallyEq hEq hxEq
            · have houtside : 1 ≤ x := le_of_not_gt hinside
              have hEq : chapter05Triangle =ᶠ[nhdsWithin x (Ici x)]
                  (fun _ : ℝ => (0 : ℝ)) := by
                filter_upwards [self_mem_nhdsWithin] with y hy
                exact hzeroR y (houtside.trans hy)
              have hder : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0
                  (Ici x) x := (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
              have hxEq := hzeroR x houtside
              have hcoef : Dright x = 0 := by
                simp [Dright, hleft', hxnonnegative, houtside]
                ring
              rw [hcoef]
              exact hder.congr_of_eventuallyEq hEq hxEq
  · unfold chapter05OriginCondition chapter05OriginIntegral
    have hEq :
        (fun x : ℝ => ENNReal.ofReal (|1 - chapter05Triangle x| / x)) =ᶠ[
          MeasureTheory.ae (volume.restrict (Ioc (0 : ℝ) 1))]
          (fun _ : ℝ => ENNReal.ofReal 1) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hxabs : |x| = x := abs_of_pos hx.1
      have hnonneg : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
      have htriangle : chapter05Triangle x = 1 - x := by
        simp [chapter05Triangle, hxabs, max_eq_left hnonneg]
      rw [htriangle]
      have hquot : |1 - (1 - x)| / x = (1 : ℝ) := by
        rw [show 1 - (1 - x) = x by ring, abs_of_pos hx.1]
        exact div_self (ne_of_gt hx.1)
      rw [hquot]
    rw [lintegral_congr_ae hEq]
    simp

theorem chapter05_origin_condition_iff_integrableOn
    {F : ℝ → ℝ} (hContinuous : Continuous F) :
    chapter05OriginCondition F ↔
      IntegrableOn (fun x : ℝ => |1 - F x| / x) (Ioc (0 : ℝ) 1) volume := by
  unfold chapter05OriginCondition chapter05OriginIntegral
  change
    (∫⁻ x, ENNReal.ofReal (|1 - F x| / x) ∂(volume.restrict (Ioc (0 : ℝ) 1))) < ⊤ ↔
      Integrable (fun x : ℝ => |1 - F x| / x)
        (volume.restrict (Ioc (0 : ℝ) 1))
  rw [lt_top_iff_ne_top]
  apply lintegral_ofReal_ne_top_iff_integrable
  · have hnum : Measurable (fun x : ℝ => |1 - F x|) := by
      simpa [Real.norm_eq_abs] using
        (measurable_const.sub hContinuous.measurable).norm
    exact (hnum.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact div_nonneg (abs_nonneg _) (le_of_lt hx.1)

theorem chapter05_smooth_even_is_quadratic_at_zero
    {F : ℝ → ℝ} (hEven : Function.Even F) (hF0 : F 0 = 1)
    (hC2 : ContDiffAt ℝ 2 F 0) :
    (fun x : ℝ => 1 - F x) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ 2) := by
  have hderiv : HasDerivAt F (deriv F 0) 0 :=
    (hC2.differentiableAt (by norm_num)).hasDerivAt
  have hderiv_neg : HasDerivAt (fun x : ℝ => F (-x)) (-(deriv F 0)) 0 := by
    convert! HasDerivAt.comp_of_eq 0 hderiv (hasDerivAt_neg' 0) (by simp) using 1
    ring
  have hderiv_even : HasDerivAt F (-(deriv F 0)) 0 := by
    convert hderiv_neg using 1
    funext x
    exact (hEven x).symm
  have hderiv0 : deriv F 0 = 0 := by
    have := hderiv.unique hderiv_even
    linarith
  obtain ⟨u, hu, hFu⟩ := hC2.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
  let s : Set ℝ := Metric.ball 0 (r / 2)
  have hs_mem : s ∈ 𝓝 (0 : ℝ) := by
    dsimp [s]
    exact Metric.ball_mem_nhds _ (half_pos hr)
  have hs_open : IsOpen s := by
    dsimp [s]
    exact Metric.isOpen_ball
  have hs_sub : s ⊆ u := by
    intro x hx
    apply hru
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_ball.mp hx
    rw [Real.dist_eq] at hx' ⊢
    have hxabs : |x| < r / 2 := by simpa using hx'
    have : |x| < r := lt_of_lt_of_le hxabs (by linarith)
    simpa using this
  have hFs : ContDiffOn ℝ 2 F s := hFu.mono hs_sub
  have hTaylor :
      (fun x : ℝ => F x - taylorWithinEval F 2 s 0 x) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => (x - 0) ^ 2) := by
    have h := taylor_isLittleO (convex_ball (0 : ℝ) (r / 2))
      (Metric.mem_ball_self (half_pos hr)) hFs
    rw [nhdsWithin_eq_nhds.mpr hs_mem] at h
    exact h
  have hiter1 : iteratedDerivWithin 1 F s 0 = 0 := by
    have h := iteratedDerivWithin_of_isOpen (f := F) (n := 1) hs_open
      (Metric.mem_ball_self (half_pos hr))
    simpa [iteratedDeriv_one, hderiv0] using h
  let c : ℝ := (1 / 2) * iteratedDerivWithin 2 F s 0
  have hpoly (x : ℝ) : taylorWithinEval F 2 s 0 x = 1 + c * x ^ 2 := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, c, hderiv0, hF0,
      iteratedDerivWithin_of_isOpen hs_open
        (Metric.mem_ball_self (half_pos hr))]
    ring
  have hRem : (fun x : ℝ => F x - taylorWithinEval F 2 s 0 x) =O[𝓝 (0 : ℝ)]
      (fun x : ℝ => x ^ 2) := by
    simpa using hTaylor.isBigO
  have hPoly : (fun x : ℝ => -c * x ^ 2) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ 2) :=
    Asymptotics.isBigO_const_mul_self (-c) (fun x : ℝ => x ^ 2) (𝓝 (0 : ℝ))
  exact (hRem.neg_left.add hPoly).congr_left fun x => by
    rw [hpoly x]
    ring_nf

theorem chapter05_origin_condition_of_quadratic_bound
    {F : ℝ → ℝ} (hContinuous : Continuous F)
    (hQuadratic : (fun x : ℝ => 1 - F x) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ 2)) :
    chapter05OriginCondition F := by
  apply (chapter05_origin_condition_iff_integrableOn hContinuous).2
  obtain ⟨C, hCpos, hC⟩ := hQuadratic.exists_pos
  obtain ⟨r, hr, hbound⟩ := Metric.mem_nhds_iff.mp hC.bound
  let a : ℝ := min (r / 2) 1
  have ha_pos : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) zero_lt_one
  have ha_le_one : a ≤ 1 := min_le_right _ _
  have ha_lt_r : a < r := by
    dsimp [a]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have haway_cont : ContinuousOn (fun x : ℝ => |1 - F x| / x) (Icc a 1) := by
    have hnum : Continuous (fun x : ℝ => |1 - F x|) := by
      simpa [Real.norm_eq_abs] using
        (continuous_const.sub hContinuous).norm
    exact hnum.continuousOn.div continuousOn_id fun x hx =>
      ne_of_gt (lt_of_lt_of_le ha_pos hx.1)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc a 1)).exists_bound_of_continuousOn
    haway_cont
  have hmeas : AEStronglyMeasurable (fun x : ℝ => |1 - F x| / x) volume := by
    have hnum : Measurable (fun x : ℝ => |1 - F x|) := by
      simpa [Real.norm_eq_abs] using
        (measurable_const.sub hContinuous.measurable).norm
    exact (hnum.div measurable_id).aestronglyMeasurable
  have hbound_all : ∀ x ∈ Ioc (0 : ℝ) 1,
      ‖|1 - F x| / x‖ ≤ max C M := by
    intro x hx
    by_cases hxa : x < a
    · have hxball : x ∈ Metric.ball (0 : ℝ) r := by
        apply Metric.mem_ball.mpr
        have hxhalf : x < r / 2 := lt_of_lt_of_le hxa (min_le_left _ _)
        have hxabs : |x| < r / 2 := by
          simpa [abs_of_pos hx.1] using hxhalf
        have hxr : |x| < r := lt_trans hxabs (by linarith)
        simpa [Real.dist_eq, abs_of_pos hx.1] using hxr
      have hquad : |1 - F x| ≤ C * x ^ 2 := by
        simpa [Real.norm_eq_abs, abs_of_pos hx.1, abs_pow] using hbound hxball
      have hg_nonneg : 0 ≤ |1 - F x| / x := div_nonneg (abs_nonneg _) hx.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg hg_nonneg]
      apply le_max_of_le_left
      apply (div_le_iff₀ hx.1).2
      calc
        |1 - F x| ≤ C * x ^ 2 := hquad
        _ ≤ C * x := by
          gcongr
          nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hx.2)]
    · have hxaway : x ∈ Icc a 1 := ⟨le_of_not_gt hxa, hx.2⟩
      exact le_max_of_le_right (hM x hxaway)
  exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmeas
    (ae_restrict_of_forall_mem measurableSet_Ioc hbound_all)

theorem chapter05_smooth_even_origin_condition
    {F : ℝ → ℝ} (hEven : Function.Even F) (hF0 : F 0 = 1)
    (hContinuous : Continuous F) (hC2 : ContDiffAt ℝ 2 F 0) :
    chapter05OriginCondition F := by
  exact chapter05_origin_condition_of_quadratic_bound hContinuous
    (chapter05_smooth_even_is_quadratic_at_zero hEven hF0 hC2)

theorem chapter05_right_corner_is_linear_at_zero
    {F : ℝ → ℝ} (hF0 : F 0 = 1) {d : ℝ}
    (hRightDerivative : HasDerivWithinAt F d (Ici (0 : ℝ)) 0) :
    (fun x : ℝ => 1 - F x) =O[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)] (fun x : ℝ => x) := by
  have hRem :
      (fun x : ℝ => F x - F 0 - (x - 0) • d) =o[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)]
        (fun x : ℝ => x - 0) := hRightDerivative.isLittleO
  have hRemO :
      (fun x : ℝ => F x - F 0 - (x - 0) • d) =O[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)]
        (fun x : ℝ => x) := by
    simpa using hRem.isBigO
  have hLinear : (fun x : ℝ => (-d) * x) =O[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)]
      (fun x : ℝ => x) :=
    Asymptotics.isBigO_const_mul_self (-d) (fun x : ℝ => x)
      (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ))
  exact (hRemO.neg_left.add hLinear).congr_left fun x => by
    rw [hF0]
    simp only [smul_eq_mul]
    ring

theorem chapter05_origin_condition_of_right_linear_bound
    {F : ℝ → ℝ} (hContinuous : Continuous F)
    (hLinear : (fun x : ℝ => 1 - F x) =O[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)]
      (fun x : ℝ => x)) :
    chapter05OriginCondition F := by
  apply (chapter05_origin_condition_iff_integrableOn hContinuous).2
  obtain ⟨C, hCpos, hC⟩ := hLinear.exists_pos
  obtain ⟨r, hr, hbound⟩ := Metric.mem_nhdsWithin_iff.mp hC.bound
  let a : ℝ := min (r / 2) 1
  have ha_pos : 0 < a := by
    dsimp [a]
    exact lt_min (by linarith) zero_lt_one
  have ha_le_one : a ≤ 1 := min_le_right _ _
  have haway_cont : ContinuousOn (fun x : ℝ => |1 - F x| / x) (Icc a 1) := by
    have hnum : Continuous (fun x : ℝ => |1 - F x|) := by
      simpa [Real.norm_eq_abs] using
        (continuous_const.sub hContinuous).norm
    exact hnum.continuousOn.div continuousOn_id fun x hx =>
      ne_of_gt (lt_of_lt_of_le ha_pos hx.1)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc a 1)).exists_bound_of_continuousOn
    haway_cont
  have hmeas : AEStronglyMeasurable (fun x : ℝ => |1 - F x| / x) volume := by
    have hnum : Measurable (fun x : ℝ => |1 - F x|) := by
      simpa [Real.norm_eq_abs] using
        (measurable_const.sub hContinuous.measurable).norm
    exact (hnum.div measurable_id).aestronglyMeasurable
  have hbound_all : ∀ x ∈ Ioc (0 : ℝ) 1,
      ‖|1 - F x| / x‖ ≤ max C M := by
    intro x hx
    by_cases hxa : x < a
    · have hxhalf : x < r / 2 := lt_of_lt_of_le hxa (min_le_left _ _)
      have hxball : x ∈ Metric.ball (0 : ℝ) r := by
        apply Metric.mem_ball.mpr
        have hxabs : |x| < r := by
          have : |x| < r / 2 := by simpa [abs_of_pos hx.1] using hxhalf
          exact lt_trans this (by linarith)
        simpa [Real.dist_eq, abs_of_pos hx.1] using hxabs
      have hquad : |1 - F x| ≤ C * x := by
        simpa [Real.norm_eq_abs, abs_of_pos hx.1] using
          hbound ⟨hxball, hx.1.le⟩
      have hg_nonneg : 0 ≤ |1 - F x| / x := div_nonneg (abs_nonneg _) hx.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg hg_nonneg]
      apply le_max_of_le_left
      exact (div_le_iff₀ hx.1).2 hquad
    · have hxaway : x ∈ Icc a 1 := ⟨le_of_not_gt hxa, hx.2⟩
      exact le_max_of_le_right (hM x hxaway)
  exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmeas
    (ae_restrict_of_forall_mem measurableSet_Ioc hbound_all)

theorem chapter05_right_corner_origin_condition
    {F : ℝ → ℝ} (hF0 : F 0 = 1) (hContinuous : Continuous F) {d : ℝ}
    (hRightDerivative : HasDerivWithinAt F d (Ici (0 : ℝ)) 0) :
    chapter05OriginCondition F := by
  exact chapter05_origin_condition_of_right_linear_bound hContinuous
    (chapter05_right_corner_is_linear_at_zero hF0 hRightDerivative)

private noncomputable def chapter05IntervalIntegralListSum
    (f : ℝ → ℂ) : List ℝ → ℂ
  | [] => 0
  | [_] => 0
  | a :: b :: l => (∫ x in a..b, f x) +
      chapter05IntervalIntegralListSum f (b :: l)

private theorem chapter05_intervalIntegralListSum_eq
    (f : ℝ → ℂ) (l : List ℝ) (hl : l ≠ [])
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    chapter05IntervalIntegralListSum f l =
      ∫ x in (l.head!)..(l.getLast hl), f x := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons a l ih =>
    cases l with
    | nil => simp [chapter05IntervalIntegralListSum]
    | cons b l =>
      let c : ℝ := (b :: l).getLast (by simp)
      calc
        chapter05IntervalIntegralListSum f (a :: b :: l) =
            (∫ x in a..b, f x) +
              chapter05IntervalIntegralListSum f (b :: l) := by rfl
        _ = (∫ x in a..b, f x) + ∫ x in b..c, f x := by
          rw [ih (by simp)]
          simp [c]
        _ = ∫ x in a..c, f x :=
          intervalIntegral.integral_add_adjacent_intervals (hf a b) (hf b c)
        _ = ∫ x in (a :: b :: l).head!..(a :: b :: l).getLast (by simp), f x := by
          simp [c]

private noncomputable def chapter05IntervalBoundaryListSum
    (u v : ℝ → ℂ) : List ℝ → ℂ
  | [] => 0
  | [_] => 0
  | a :: b :: l => (u b - v a) +
      chapter05IntervalBoundaryListSum u v (b :: l)

private def chapter05IntervalBoundaryWeight
    (left right : ℝ → ℝ) : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: l => left b + right a +
      chapter05IntervalBoundaryWeight left right (b :: l)

theorem chapter05_basically_admissible_vertical_decay
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    chapter05VerticalTransformDecay2 F := by
  classical
  rcases (chapter05_oneSidedDerivativeBV_iff.mp hF.oneSidedDerivativeBV) with
    ⟨leftDerivative, rightDerivative, hleft, hright, hleftBV, hrightBV⟩
  rcases hF.piecewiseC2 with ⟨s, hs, hC2⟩
  obtain ⟨r, hr⟩ := hF.compactSupport.isBounded.subset_closedBall (0 : ℝ)
  let A : ℝ := |r| + 1
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith [abs_nonneg r]
  have hAr : r < A := by
    dsimp [A]
    linarith [le_abs_self r]
  have hsupport : tsupport F ⊆ Icc (-A) A := by
    intro x hx
    have hxball : x ∈ Metric.closedBall (0 : ℝ) r := hr hx
    have hxabs : |x| ≤ r := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    constructor <;> dsimp [A] <;>
      linarith [le_abs_self x, neg_le_abs x, hxabs, abs_nonneg r]
  have hleftnot : -A ∉ tsupport F := by
    intro hx
    have hxball : -A ∈ Metric.closedBall (0 : ℝ) r := hr hx
    have hxabs : |-A| ≤ r := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    rw [abs_neg, abs_of_nonneg hA] at hxabs
    linarith
  have hrightnot : A ∉ tsupport F := by
    intro hx
    have hxball : A ∈ Metric.closedBall (0 : ℝ) r := hr hx
    have hxabs : |A| ≤ r := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hxball
    rw [abs_of_nonneg hA] at hxabs
    linarith
  have hFzero_left : F (-A) = 0 :=
    image_eq_zero_of_notMem_tsupport hleftnot
  have hFzero_right : F A = 0 :=
    image_eq_zero_of_notMem_tsupport hrightnot
  have hrightBV' : ∀ a b : ℝ, BoundedVariationOn rightDerivative (uIcc a b) := by
    intro a b
    exact ne_top_of_le_ne_top hrightBV
      (eVariationOn.mono _ (subset_univ _))
  have hrightInt : ∀ a b : ℝ, IntervalIntegrable rightDerivative volume a b := by
    intro a b
    obtain ⟨p, q, hp, hq, hpq⟩ :=
      (hrightBV' a b).locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
    rw [hpq]
    exact hp.intervalIntegrable.sub hq.intervalIntegrable
  have hrightIntC : ∀ a b : ℝ,
      IntervalIntegrable (fun x : ℝ => (rightDerivative x : ℂ)) volume a b := by
    intro a b
    exact ⟨(hrightInt a b).1.ofReal, (hrightInt a b).2.ofReal⟩
  have hkcont (z : ℂ) : Continuous (fun x : ℝ => chapter05LaplaceKernel z x) := by
    unfold chapter05LaplaceKernel
    fun_prop
  have hkderiv (z : ℂ) (x : ℝ) :
      HasDerivAt (fun y : ℝ => chapter05LaplaceKernel z y)
        ((z - (1 / 2 : ℂ)) * chapter05LaplaceKernel z x) x := by
    unfold chapter05LaplaceKernel
    have hlin := (hasDerivAt_id x).ofReal_comp.const_mul (z - (1 / 2 : ℂ))
    have hexp := hlin.cexp
    convert hexp using 1 <;> simp [mul_comm]
  have hfirst (z : ℂ) :
      ∫ x in (-A)..A,
        (rightDerivative x : ℂ) * chapter05LaplaceKernel z x +
          (F x : ℂ) * ((z - (1 / 2 : ℂ)) * chapter05LaplaceKernel z x) =
        (F A : ℂ) * chapter05LaplaceKernel z A -
          (F (-A) : ℂ) * chapter05LaplaceKernel z (-A) := by
    apply intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    · exact (Complex.continuous_ofReal.comp hF.continuous).continuousOn
    · exact (hkcont z).continuousOn
    · intro x hx
      exact ((hright x).ofReal_comp).mono (Ioi_subset_Ici_self)
    · intro x hx
      exact (hkderiv z x).hasDerivWithinAt
    · exact hrightIntC _ _
    · exact (Continuous.intervalIntegrable (μ := volume)
        (continuous_const.mul (hkcont z)) (-A) A)
  have hfirst' (z : ℂ) :
      ∫ x in (-A)..A,
        (rightDerivative x : ℂ) * chapter05LaplaceKernel z x +
          (F x : ℂ) * ((z - (1 / 2 : ℂ)) * chapter05LaplaceKernel z x) = 0 := by
    simpa [hFzero_left, hFzero_right] using hfirst z
  have hrightEq : ∀ x ∉ s, deriv F x = rightDerivative x := by
    intro x hx
    have hdiff : DifferentiableAt ℝ F x :=
      (hC2 x hx).differentiableAt (by norm_num)
    have hfull : HasDerivWithinAt F (deriv F x) (Ici x) x :=
      hdiff.hasDerivAt.hasDerivWithinAt
    exact (uniqueDiffWithinAt_Ici x).eq_deriv _ hfull (hright x)
  have hsecond (x : ℝ) (hx : x ∉ s) :
      HasDerivAt (fun y : ℝ => rightDerivative y)
        (deriv (deriv F) x) x := by
    have hderivF : HasDerivAt (fun y : ℝ => deriv F y)
        (deriv (deriv F) x) x := by
      exact ((hC2 x hx).derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num) |>.hasDerivAt
    have heq : ∀ᶠ y in 𝓝 x, rightDerivative y = deriv F y := by
      filter_upwards [hs.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact (hrightEq y hy).symm
    exact hderivF.congr_of_eventuallyEq heq
  have hq2deriv (z : ℂ) (x : ℝ) (hx : x ∉ s) :
      HasDerivAt
        (fun y : ℝ => (rightDerivative y : ℂ) * chapter05LaplaceKernel z y)
        (((deriv (deriv F) x : ℝ) : ℂ) * chapter05LaplaceKernel z x +
          (rightDerivative x : ℂ) *
            ((z - (1 / 2 : ℂ)) * chapter05LaplaceKernel z x)) x := by
    exact (hsecond x hx).ofReal_comp.mul (hkderiv z x)
  have hq2right (z : ℂ) (x : ℝ) :
      Tendsto
        (fun y : ℝ => (rightDerivative y : ℂ) * chapter05LaplaceKernel z y)
        (𝓝[>] x)
        (𝓝 ((rightDerivative.rightLim x : ℂ) * chapter05LaplaceKernel z x)) := by
    exact
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (hrightBV.tendsto_rightLim x)).mul
        ((hkcont z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hq2left (z : ℂ) (x : ℝ) :
      Tendsto
        (fun y : ℝ => (rightDerivative y : ℂ) * chapter05LaplaceKernel z y)
        (𝓝[<] x)
        (𝓝 ((rightDerivative.leftLim x : ℂ) * chapter05LaplaceKernel z x)) := by
    exact
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (hrightBV.tendsto_leftLim x)).mul
        ((hkcont z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hq2int (z : ℂ) (a b : ℝ) :
      IntervalIntegrable
        (fun x : ℝ =>
          (((deriv rightDerivative x : ℝ) : ℂ) * chapter05LaplaceKernel z x +
            (rightDerivative x : ℂ) *
              ((z - (1 / 2 : ℂ)) * chapter05LaplaceKernel z x))) volume a b := by
    have hderivR : IntervalIntegrable (deriv rightDerivative) volume a b :=
      (hrightBV' a b).intervalIntegrable_deriv
    have hderivC : IntervalIntegrable
        (fun x : ℝ => ((deriv rightDerivative x : ℝ) : ℂ)) volume a b :=
      ⟨hderivR.1.ofReal, hderivR.2.ofReal⟩
    have h₁ := hderivC.mul_continuousOn (hkcont z).continuousOn
    have hc : Continuous
        (fun x : ℝ => (z - (1 / 2 : ℂ)) * chapter05LaplaceKernel z x) :=
      continuous_const.mul (hkcont z)
    have h₂ := hrightIntC a b |>.mul_continuousOn hc.continuousOn
    exact h₁.add h₂
  have hsecondIBP (z : ℂ) (a b : ℝ) (hab : a < b)
      (hsab : ∀ x ∈ Ioo a b, x ∉ s) :
      ∫ x in a..b,
        (((deriv rightDerivative x : ℝ) : ℂ) * chapter05LaplaceKernel z x +
          (rightDerivative x : ℂ) *
            ((z - (1 / 2 : ℂ)) * chapter05LaplaceKernel z x)) =
        (rightDerivative.leftLim b : ℂ) * chapter05LaplaceKernel z b -
          (rightDerivative.rightLim a : ℂ) * chapter05LaplaceKernel z a := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (f :=
        fun x : ℝ => (rightDerivative x : ℂ) * chapter05LaplaceKernel z x)
        (f' := fun x : ℝ =>
          (((deriv rightDerivative x : ℝ) : ℂ) * chapter05LaplaceKernel z x +
            (rightDerivative x : ℂ) *
              ((z - (1 / 2 : ℂ)) * chapter05LaplaceKernel z x)))
        hab
        (fun x hx => by
          have hx' : x ∉ s := hsab x hx
          have heqR : deriv rightDerivative x = deriv (deriv F) x := by
            simpa only [Function.comp_def] using (hsecond x hx').deriv
          have heq : ((deriv rightDerivative x : ℝ) : ℂ) =
              ((deriv (deriv F) x : ℝ) : ℂ) :=
            congrArg (fun y : ℝ => (y : ℂ)) heqR
          simpa [heq] using hq2deriv z x hx')
        (hq2int z a b) (hq2right z a) (hq2left z b))
  let s₀ : Set ℝ := s ∩ Ioo (-A) A
  have hs₀ : s₀.Finite := hs.subset inter_subset_left
  let points : Finset ℝ := insert (-A) (insert A hs₀.toFinset)
  let l : List ℝ := points.sort (· ≤ ·)
  have hpoints_mem : ∀ x, x ∈ l ↔ x ∈ points := by
    intro x
    simp [l]
  have hls : l.Pairwise (· < ·) :=
    (Finset.sortedLT_sort points).pairwise
  have hminus_mem : (-A : ℝ) ∈ l := by
    rw [hpoints_mem]
    simp [points]
  have hplus_mem : A ∈ l := by
    rw [hpoints_mem]
    simp [points]
  have hl : l ≠ [] := by
    intro hl
    simp [hl] at hminus_mem
  have hpoint_bounds : ∀ x ∈ l, x ∈ Icc (-A) A := by
    intro x hx
    rw [hpoints_mem] at hx
    simp only [points, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · constructor <;> linarith
    · constructor <;> linarith
    · have hx₀ : x ∈ s₀ := (Set.Finite.mem_toFinset hs₀).1 hx
      exact ⟨le_of_lt hx₀.2.1, le_of_lt hx₀.2.2⟩
  have hhead : l.head! = (-A : ℝ) := by
    have hls_le : l.Pairwise (· ≤ ·) := hls.imp LT.lt.le
    apply le_antisymm
    · exact hls_le.head!_le hminus_mem
    · exact (hpoint_bounds _ (List.head!_mem_self hl)).1
  have hlast : l.getLast hl = A := by
    have hlastmem : l.getLast hl ∈ l := List.getLast_mem hl
    have hls_le : l.Pairwise (· ≤ ·) := hls.imp LT.lt.le
    have hle : A ≤ l.getLast hl := hls_le.rel_getLast hplus_mem
    exact le_antisymm (hpoint_bounds _ hlastmem).2 hle
  intro R hR
  let M : ℝ := Real.exp ((R + 1 / 2) * A)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Real.exp_nonneg _
  let D : ℝ := ∫ x in (-A)..A, ‖deriv rightDerivative x‖
  have hinterval : -A ≤ A := by linarith
  have hderivInt : IntervalIntegrable (deriv rightDerivative) volume (-A) A :=
    (hrightBV' (-A) A).intervalIntegrable_deriv
  have hD : 0 ≤ D := by
    dsimp [D]
    exact intervalIntegral.integral_nonneg_of_forall hinterval
      (fun _ => abs_nonneg _)
  let E : ℝ := ∫ x in (-A)..A, ‖(F x : ℂ)‖
  have hFintC : IntervalIntegrable (fun x : ℝ => (F x : ℂ)) volume (-A) A := by
    exact (Continuous.intervalIntegrable (μ := volume)
      (Complex.continuous_ofReal.comp hF.continuous) (-A) A)
  have hE : 0 ≤ E := by
    dsimp [E]
    exact intervalIntegral.integral_nonneg_of_forall hinterval
      (fun _ => norm_nonneg _)
  have hkernel_bound (σ t x : ℝ) (hσ : |σ| ≤ R)
      (hx : x ∈ Icc (-A) A) :
      ‖chapter05LaplaceKernel ((σ : ℂ) + (t : ℂ) * Complex.I) x‖ ≤ M := by
    rw [chapter05LaplaceKernel, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hσ' : -R ≤ σ ∧ σ ≤ R := (abs_le.mp hσ)
    have hσabs : |σ - 1 / 2| ≤ R + 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hσ'.1, hσ'.2]
    have hxabs : |x| ≤ A := by
      rw [abs_le]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    calc
      (((σ : ℂ) + (t : ℂ) * Complex.I - (1 / 2 : ℂ)) * (x : ℂ)).re
          = (σ - 1 / 2) * x := by norm_num [Complex.mul_re]
      _ ≤ |σ - 1 / 2| * |x| := by
        exact le_trans (le_abs_self _) (by rw [abs_mul])
      _ ≤ (R + 1 / 2) * A := by
        exact mul_le_mul hσabs hxabs (abs_nonneg _) (by linarith [hσ'.1, hσ'.2])
      _ = ((R + 1 / 2) * A) := rfl
  let B : ℝ :=
    (l.map (fun x => ‖(rightDerivative.leftLim x : ℂ)‖ +
      ‖(rightDerivative.rightLim x : ℂ)‖)).sum
  have hB : 0 ≤ B := by
    dsimp [B]
    apply List.sum_nonneg
    intro x hx
    rcases List.mem_map.1 hx with ⟨y, hy, rfl⟩
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  let C : ℝ := 4 * M * (E + D + B + 1)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro σ t hσ
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  let c : ℂ := z - (1 / 2 : ℂ)
  have hkernel_bound_z (x : ℝ) (hx : x ∈ Icc (-A) A) :
      ‖chapter05LaplaceKernel z x‖ ≤ M := by
    exact hkernel_bound σ t x hσ hx
  let f₂ : ℝ → ℂ := fun x =>
    (((deriv rightDerivative x : ℝ) : ℂ) * chapter05LaplaceKernel z x +
      (rightDerivative x : ℂ) *
        ((z - (1 / 2 : ℂ)) * chapter05LaplaceKernel z x))
  let u : ℝ → ℂ := fun x =>
    (rightDerivative.leftLim x : ℂ) * chapter05LaplaceKernel z x
  let v : ℝ → ℂ := fun x =>
    (rightDerivative.rightLim x : ℂ) * chapter05LaplaceKernel z x
  have hsecondAB :
      ∀ a b : ℝ, a < b → (∀ x ∈ Ioo a b, x ∉ s) →
        ∫ x in a..b, f₂ x = u b - v a := by
    intro a b hab hsab
    simpa [f₂, u, v, c] using hsecondIBP z a b hab hsab
  have hsumIBP :
      ∀ (pre cur : List ℝ),
        l = pre ++ cur →
        cur.Pairwise (· < ·) →
        (∀ x ∈ cur, x ∈ points) →
        (∀ x ∈ pre, ∀ y ∈ cur, x < y) →
        chapter05IntervalIntegralListSum f₂ cur =
          chapter05IntervalBoundaryListSum u v cur := by
    intro pre cur
    induction cur generalizing pre with
    | nil =>
        intro hconcat hcur hmem hcross
        simp [chapter05IntervalIntegralListSum, chapter05IntervalBoundaryListSum]
    | cons a cur ih =>
        cases cur with
        | nil =>
            intro hconcat hcur hmem hcross
            simp [chapter05IntervalIntegralListSum, chapter05IntervalBoundaryListSum]
        | cons b tail =>
            intro hconcat hcur hmem hcross
            have hab : a < b := (List.pairwise_cons.mp hcur).1 b (by simp)
            have htail : (b :: tail).Pairwise (· < ·) :=
              (List.pairwise_cons.mp hcur).2
            have hmem_tail : ∀ x ∈ b :: tail, x ∈ points := by
              intro x hx
              exact hmem x (by simp [hx])
            have hno : ∀ x ∈ Ioo a b, x ∉ s := by
              intro x hx hxs
              have ha_l : a ∈ l := (hpoints_mem a).2 (hmem a (by simp))
              have hb_l : b ∈ l := (hpoints_mem b).2 (hmem b (by simp))
              have haIcc : a ∈ Icc (-A) A := hpoint_bounds a ha_l
              have hbIcc : b ∈ Icc (-A) A := hpoint_bounds b hb_l
              have hxs₀ : x ∈ s₀ := by
                exact ⟨hxs, ⟨lt_of_le_of_lt haIcc.1 hx.1,
                  lt_of_lt_of_le hx.2 hbIcc.2⟩⟩
              have hxpoints : x ∈ points := by
                exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2
                  (Or.inr ((Set.Finite.mem_toFinset hs₀).2 hxs₀))))
              have hxglobal : x ∈ l := (hpoints_mem x).2 hxpoints
              rw [hconcat] at hxglobal
              rcases List.mem_append.mp hxglobal with hxpre | hxcur
              · have hxa := hcross x hxpre a (by simp)
                linarith [hxa, hx.1]
              · have hxcur' : x = a ∨ x = b ∨ x ∈ tail := by
                  simpa using hxcur
                rcases hxcur' with rfl | rfl | hxcur
                · linarith [hx.1]
                · linarith [hx.2]
                · have hbtail := (List.pairwise_cons.mp htail).1 x hxcur
                  linarith [hbtail, hx.2]
            have hfirst := hsecondAB a b hab hno
            have hcross' : ∀ x ∈ pre ++ [a], ∀ y ∈ b :: tail, x < y := by
              intro x hx y hy
              rcases List.mem_append.mp hx with hxpre | hxone
              · exact hcross x hxpre y (by simp [hy])
              · have hxa : x = a := by simpa using hxone
                subst x
                exact (List.pairwise_cons.mp hcur).1 y (by exact hy)
            have hconcat' : l = (pre ++ [a]) ++ (b :: tail) := by
              simpa [List.append_assoc] using hconcat
            have hrec := ih (pre := pre ++ [a]) hconcat' htail hmem_tail hcross'
            calc
              chapter05IntervalIntegralListSum f₂ (a :: b :: tail) =
                  (∫ x in a..b, f₂ x) +
                    chapter05IntervalIntegralListSum f₂ (b :: tail) := by rfl
              _ = (u b - v a) +
                    chapter05IntervalBoundaryListSum u v (b :: tail) := by
                rw [hfirst, hrec]
              _ = chapter05IntervalBoundaryListSum u v (a :: b :: tail) := by rfl
  have hmem_all : ∀ x ∈ l, x ∈ points := by
    intro x hx
    exact (hpoints_mem x).1 hx
  have hsum_list :
      chapter05IntervalIntegralListSum f₂ l =
        chapter05IntervalBoundaryListSum u v l := by
    exact hsumIBP [] l (by simp) hls hmem_all (by simp)
  have hsum_interval :
      chapter05IntervalIntegralListSum f₂ l = ∫ x in (-A)..A, f₂ x := by
    simpa [hhead, hlast] using
      (chapter05_intervalIntegralListSum_eq f₂ l hl (fun a b => hq2int z a b))
  have hq2global :
      ∫ x in (-A)..A, f₂ x =
        chapter05IntervalBoundaryListSum u v l := by
    rw [← hsum_interval, hsum_list]
  have hLaplaceInterval (w : ℂ) :
      chapter05BilateralLaplaceTransform F w =
        ∫ x in (-A)..A, (F x : ℂ) * chapter05LaplaceKernel w x := by
    unfold chapter05BilateralLaplaceTransform
    symm
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have hxF : F x ≠ 0 := by
      intro hFx
      apply hx
      simp [hFx]
    have hxTs : x ∈ tsupport F := (subset_tsupport (f := F)) hxF
    have hxIcc : x ∈ Icc (-A) A := hsupport hxTs
    have hneq : x ≠ -A := by
      intro hxa
      apply hleftnot
      simpa [hxa] using hxTs
    exact ⟨lt_of_le_of_ne hxIcc.1 hneq.symm, hxIcc.2⟩
  let k : ℝ → ℂ := fun x =>
    (F x : ℂ) * chapter05LaplaceKernel z x
  let rK : ℝ → ℂ := fun x =>
    (rightDerivative x : ℂ) * chapter05LaplaceKernel z x
  let drK : ℝ → ℂ := fun x =>
    ((deriv rightDerivative x : ℝ) : ℂ) * chapter05LaplaceKernel z x
  have hck : Continuous (fun x : ℝ => c * chapter05LaplaceKernel z x) := by
    exact continuous_const.mul (hkcont z)
  have hkInt : IntervalIntegrable k volume (-A) A := by
    exact (Continuous.intervalIntegrable (μ := volume)
      ((Complex.continuous_ofReal.comp hF.continuous).mul (hkcont z)) (-A) A)
  have hrKInt : IntervalIntegrable rK volume (-A) A := by
    exact hrightIntC (-A) A |>.mul_continuousOn (hkcont z).continuousOn
  have hrcInt : IntervalIntegrable
      (fun x : ℝ => (rightDerivative x : ℂ) *
        (c * chapter05LaplaceKernel z x)) volume (-A) A := by
    exact hrightIntC (-A) A |>.mul_continuousOn hck.continuousOn
  have hFkInt : IntervalIntegrable
      (fun x : ℝ => (F x : ℂ) *
        (c * chapter05LaplaceKernel z x)) volume (-A) A := by
    exact (Continuous.intervalIntegrable (μ := volume)
      ((Complex.continuous_ofReal.comp hF.continuous).mul hck) (-A) A)
  have hderivC : IntervalIntegrable
      (fun x : ℝ => ((deriv rightDerivative x : ℝ) : ℂ)) volume (-A) A := by
    exact ⟨hderivInt.1.ofReal, hderivInt.2.ofReal⟩
  have hdrKInt : IntervalIntegrable drK volume (-A) A := by
    exact hderivC.mul_continuousOn (hkcont z).continuousOn
  let IF : ℂ := ∫ x in (-A)..A, k x
  let IR : ℂ := ∫ x in (-A)..A, rK x
  let ID : ℂ := ∫ x in (-A)..A, drK x
  let JB : ℂ := chapter05IntervalBoundaryListSum u v l
  have hfirst_split : IR + c * IF = 0 := by
    have hf : ∫ x in (-A)..A,
        (rK x + (F x : ℂ) * (c * chapter05LaplaceKernel z x)) = 0 := by
      simpa [rK, c, mul_assoc, mul_left_comm, mul_comm] using hfirst' z
    rw [intervalIntegral.integral_add hrKInt hFkInt] at hf
    have hFkEq :
        (fun x : ℝ => (F x : ℂ) * (c * chapter05LaplaceKernel z x)) =
          (fun x => c * k x) := by
      funext x
      dsimp [k]
      ring
    have hFkIntegral :
        (∫ x in (-A)..A, (F x : ℂ) *
          (c * chapter05LaplaceKernel z x)) = c * IF := by
      rw [hFkEq]
      simp [IF]
    rw [hFkIntegral] at hf
    simpa [IR, rK] using hf
  have hsecond_split : ID + c * IR = JB := by
    have hq : ∫ x in (-A)..A,
        (drK x + (rightDerivative x : ℂ) *
          (c * chapter05LaplaceKernel z x)) = JB := by
      simpa [f₂, drK, c, JB, mul_assoc, mul_left_comm, mul_comm] using hq2global
    rw [intervalIntegral.integral_add hdrKInt hrcInt] at hq
    have hrcEq :
        (fun x : ℝ => (rightDerivative x : ℂ) *
          (c * chapter05LaplaceKernel z x)) =
          (fun x => c * rK x) := by
      funext x
      dsimp [rK]
      ring
    have hrcIntegral :
        (∫ x in (-A)..A, (rightDerivative x : ℂ) *
          (c * chapter05LaplaceKernel z x)) = c * IR := by
      rw [hrcEq]
      simp [IR]
    rw [hrcIntegral] at hq
    simpa [ID, drK] using hq
  let L : ℝ → ℝ := fun x => ‖(rightDerivative.leftLim x : ℂ)‖
  let V : ℝ → ℝ := fun x => ‖(rightDerivative.rightLim x : ℂ)‖
  let W : List ℝ → ℝ := chapter05IntervalBoundaryWeight L V
  have hweight_norm :
      ∀ q : List ℝ, (∀ x ∈ q, x ∈ l) →
        ‖chapter05IntervalBoundaryListSum u v q‖ ≤ M * W q := by
    intro q
    induction q with
    | nil =>
        intro hq
        simp [chapter05IntervalBoundaryListSum, W,
          chapter05IntervalBoundaryWeight]
    | cons a q ih =>
        cases q with
        | nil =>
            intro hq
            simp [chapter05IntervalBoundaryListSum, W,
              chapter05IntervalBoundaryWeight]
        | cons b tail =>
            intro hq
            have ha_l : a ∈ l := hq a (by simp)
            have hb_l : b ∈ l := hq b (by simp)
            have htail : ∀ x ∈ b :: tail, x ∈ l := by
              intro x hx
              exact hq x (by simp [hx])
            have haIcc : a ∈ Icc (-A) A := hpoint_bounds a ha_l
            have hbIcc : b ∈ Icc (-A) A := hpoint_bounds b hb_l
            have hu : ‖u b‖ ≤ M * L b := by
              calc
                ‖u b‖ = L b * ‖chapter05LaplaceKernel z b‖ := by
                  simp [u, L]
                _ ≤ L b * M := by
                  exact mul_le_mul_of_nonneg_left
                    (hkernel_bound_z b hbIcc) (by positivity)
                _ = M * L b := by ring
            have hv : ‖v a‖ ≤ M * V a := by
              calc
                ‖v a‖ = V a * ‖chapter05LaplaceKernel z a‖ := by
                  simp [v, V]
                _ ≤ V a * M := by
                  exact mul_le_mul_of_nonneg_left
                    (hkernel_bound_z a haIcc) (by positivity)
                _ = M * V a := by ring
            have htail' := ih htail
            calc
              ‖chapter05IntervalBoundaryListSum u v (a :: b :: tail)‖ =
                  ‖(u b - v a) +
                    chapter05IntervalBoundaryListSum u v (b :: tail)‖ := by rfl
              _ ≤ ‖u b - v a‖ +
                    ‖chapter05IntervalBoundaryListSum u v (b :: tail)‖ :=
                norm_add_le _ _
              _ ≤ (‖u b‖ + ‖v a‖) + M * W (b :: tail) := by
                exact add_le_add (norm_sub_le _ _) htail'
              _ ≤ (M * L b + M * V a) + M * W (b :: tail) := by
                exact add_le_add (add_le_add hu hv) (le_refl _)
              _ = M * W (a :: b :: tail) := by
                simp [W, chapter05IntervalBoundaryWeight]
                ring
  have hweight_identity :
      ∀ (q : List ℝ) (hq : q ≠ []),
        W q + L q.head! + V (q.getLast hq) =
          (q.map (fun x => L x + V x)).sum := by
    intro q
    induction q with
    | nil =>
        intro hq
        exact False.elim (hq rfl)
    | cons a q ih =>
        intro hq
        cases q with
        | nil =>
            simp [W, chapter05IntervalBoundaryWeight]
        | cons b tail =>
            have htail : (b :: tail) ≠ [] := by simp
            have hi := ih htail
            have hi' : W (b :: tail) + L b +
                V ((b :: tail).getLast htail) =
                  ((b :: tail).map (fun x => L x + V x)).sum := by
              simpa using hi
            have hcalc :
                (L b + V a + W (b :: tail)) + L a +
                    V ((b :: tail).getLast htail) =
                  (L a + V a) +
                    ((b :: tail).map (fun x => L x + V x)).sum := by
              calc
                (L b + V a + W (b :: tail)) + L a +
                    V ((b :: tail).getLast htail) =
                    (L a + V a) +
                      (W (b :: tail) + L b +
                        V ((b :: tail).getLast htail)) := by ring
                _ = (L a + V a) +
                    ((b :: tail).map (fun x => L x + V x)).sum := by
                  rw [hi']
            simpa [W, chapter05IntervalBoundaryWeight] using hcalc
  have hweight_le : W l ≤ B := by
    have hi := hweight_identity l hl
    have hnonneg : 0 ≤ L l.head! + V (l.getLast hl) := by
      exact add_nonneg (by positivity) (by positivity)
    have hi' : W l + L l.head! + V (l.getLast hl) =
        (l.map (fun x => L x + V x)).sum := hi
    have hle : W l ≤ (l.map (fun x => L x + V x)).sum := by
      linarith
    simpa [B, L, V] using hle
  have hboundary :
      ‖chapter05IntervalBoundaryListSum u v l‖ ≤ M * B := by
    calc
      ‖chapter05IntervalBoundaryListSum u v l‖ ≤ M * W l :=
        hweight_norm l (by simp)
      _ ≤ M * B := mul_le_mul_of_nonneg_left hweight_le hM
  have hID : ‖ID‖ ≤ M * D := by
    calc
      ‖ID‖ = ‖∫ x in (-A)..A, drK x‖ := by rfl
      _ ≤ ∫ x in (-A)..A, ‖drK x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hinterval
      _ ≤ ∫ x in (-A)..A, M * ‖deriv rightDerivative x‖ := by
        apply intervalIntegral.integral_mono_on hinterval
        · exact hdrKInt.norm
        · exact hderivInt.norm.const_mul M
        · intro x hx
          dsimp [drK]
          rw [norm_mul]
          calc
            ‖((deriv rightDerivative x : ℝ) : ℂ)‖ *
                ‖chapter05LaplaceKernel z x‖ ≤
                ‖((deriv rightDerivative x : ℝ) : ℂ)‖ * M :=
              mul_le_mul_of_nonneg_left (hkernel_bound_z x hx)
                (norm_nonneg ((deriv rightDerivative x : ℝ) : ℂ))
            _ = M * |deriv rightDerivative x| := by
              simp [Real.norm_eq_abs]
              ring
      _ = M * D := by
        simp [D]
  have hIF : ‖IF‖ ≤ M * E := by
    calc
      ‖IF‖ = ‖∫ x in (-A)..A, k x‖ := by rfl
      _ ≤ ∫ x in (-A)..A, ‖k x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hinterval
      _ ≤ ∫ x in (-A)..A, M * ‖(F x : ℂ)‖ := by
        apply intervalIntegral.integral_mono_on hinterval
        · exact hkInt.norm
        · exact hFintC.norm.const_mul M
        · intro x hx
          dsimp [k]
          rw [norm_mul]
          calc
            ‖(F x : ℂ)‖ * ‖chapter05LaplaceKernel z x‖ ≤
                ‖(F x : ℂ)‖ * M :=
              mul_le_mul_of_nonneg_left (hkernel_bound_z x hx)
                (norm_nonneg (F x : ℂ))
            _ = M * ‖(F x : ℂ)‖ := by ring
      _ = M * E := by simp [E]
  have htransform :
      chapter05BilateralLaplaceTransform F z = IF := by
    simpa [IF, k] using hLaplaceInterval z
  have hN : ‖ID - JB‖ ≤ M * (D + B) := by
    calc
      ‖ID - JB‖ ≤ ‖ID‖ + ‖JB‖ := norm_sub_le _ _
      _ ≤ M * D + M * B := add_le_add hID hboundary
      _ = M * (D + B) := by ring
  have hquad : c ^ 2 * IF = ID - JB := by
    linear_combination c * hfirst_split - hsecond_split
  have hprod : ‖c‖ ^ 2 * ‖IF‖ ≤ M * (D + B) := by
    calc
      ‖c‖ ^ 2 * ‖IF‖ = ‖c ^ 2 * IF‖ := by simp
      _ = ‖ID - JB‖ := by rw [hquad]
      _ ≤ M * (D + B) := hN
  have hc_im : c.im = t := by
    dsimp [c, z]
    norm_num
  have ht_norm : |t| ≤ ‖c‖ := by
    have h := Complex.abs_im_le_norm c
    simpa [hc_im] using h
  have hlarge_bound (hlarge : 1 ≤ |t|) :
      ‖IF‖ ≤ 4 * M * (D + B) / (1 + |t|) ^ 2 := by
    have hdenom_pos : 0 < (1 + |t|) ^ 2 := by
      positivity
    have hsum_le : 1 + |t| ≤ 2 * ‖c‖ := by
      linarith [ht_norm]
    have hsq_le : (1 + |t|) ^ 2 ≤ 4 * ‖c‖ ^ 2 := by
      have hprod_nonneg : 0 ≤
          (2 * ‖c‖ - (1 + |t|)) * (2 * ‖c‖ + (1 + |t|)) := by
        apply mul_nonneg
        · linarith
        · positivity
      nlinarith
    have hmul : ‖IF‖ * (1 + |t|) ^ 2 ≤ 4 * M * (D + B) := by
      calc
        ‖IF‖ * (1 + |t|) ^ 2 ≤
            ‖IF‖ * (4 * ‖c‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq_le (norm_nonneg _)
        _ = 4 * (‖c‖ ^ 2 * ‖IF‖) := by ring
        _ ≤ 4 * (M * (D + B)) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ = 4 * M * (D + B) := by ring
    exact (le_div_iff₀ hdenom_pos).2 hmul
  have hsmall_bound (hsmall : |t| ≤ 1) :
      ‖IF‖ ≤ 4 * M * E / (1 + |t|) ^ 2 := by
    have hdenom_pos : 0 < (1 + |t|) ^ 2 := by
      positivity
    have hsq_le : (1 + |t|) ^ 2 ≤ 4 := by
      nlinarith [abs_nonneg t]
    have hmul : ‖IF‖ * (1 + |t|) ^ 2 ≤ 4 * M * E := by
      calc
        ‖IF‖ * (1 + |t|) ^ 2 ≤
            (M * E) * (1 + |t|) ^ 2 :=
          mul_le_mul_of_nonneg_right hIF (sq_nonneg _)
        _ ≤ (M * E) * 4 := by
          exact mul_le_mul_of_nonneg_left hsq_le (mul_nonneg hM hE)
        _ = 4 * M * E := by ring
    exact (le_div_iff₀ hdenom_pos).2 hmul
  have hClarge : 4 * M * (D + B) ≤ C := by
    dsimp [C]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [hE]
  have hCsmall : 4 * M * E ≤ C := by
    dsimp [C]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [hD, hB]
  change ‖chapter05BilateralLaplaceTransform F z‖ ≤ C / (1 + |t|) ^ 2
  by_cases hlarge : 1 ≤ |t|
  · have hdenom_pos : 0 < (1 + |t|) ^ 2 := by positivity
    calc
      ‖chapter05BilateralLaplaceTransform F z‖ = ‖IF‖ := by rw [htransform]
      _ ≤ 4 * M * (D + B) / (1 + |t|) ^ 2 := hlarge_bound hlarge
      _ ≤ C / (1 + |t|) ^ 2 :=
        div_le_div_of_nonneg_right hClarge hdenom_pos.le
  · have hsmall : |t| ≤ 1 := le_of_not_ge hlarge
    have hdenom_pos : 0 < (1 + |t|) ^ 2 := by positivity
    calc
      ‖chapter05BilateralLaplaceTransform F z‖ = ‖IF‖ := by rw [htransform]
      _ ≤ 4 * M * E / (1 + |t|) ^ 2 := hsmall_bound hsmall
      _ ≤ C / (1 + |t|) ^ 2 :=
        div_le_div_of_nonneg_right hCsmall hdenom_pos.le

theorem chapter05_basically_admissible_fourier_decay
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖chapter05FourierTransform F t‖ ≤ C / (1 + |t|) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    chapter05_basically_admissible_vertical_decay hF 1 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro t
  have hline := hbound (1 / 2) t (by norm_num)
  have hEq := chapter05_laplace_on_critical_line
    (chapter05_basically_admissible_integrable hF) hF.even t
  have hline' :
      ‖chapter05BilateralLaplaceTransform F
          ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + |t|) ^ 2 := by
    convert hline using 1; norm_num
  rw [hEq] at hline'
  exact hline'

/-- The convergent sum over the Chapter 4 zero set, weighted by analytic
multiplicity. -/
noncomputable def chapter05SymmetricZeroSum
    (K : Type*) [Field K] [NumberField K] (F : ℝ → ℝ) : ℂ :=
  ∑' ρ : ℂ,
    (chapter04ZeroMultiplicity K ρ : ℂ) *
      chapter05BilateralLaplaceTransform F ρ

/-- The finite symmetric truncation at height `T`; the zero value for negative
`T` keeps the definition total. -/
noncomputable def chapter05SymmetricZeroPartialSum
    (K : Type*) [Field K] [NumberField K]
    (F : ℝ → ℝ) (T : ℝ) : ℂ :=
  if _hT : 0 ≤ T then
    Finset.sum (chapter04_zero_band_finite K T).toFinset
      (fun ρ => (chapter04ZeroMultiplicity K ρ : ℂ) *
        chapter05BilateralLaplaceTransform F ρ)
  else 0

theorem chapter05_symmetric_zero_sum_summable
    (K : Type*) [Field K] [NumberField K]
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    Summable (fun ρ : ℂ =>
      (chapter04ZeroMultiplicity K ρ : ℂ) *
        chapter05BilateralLaplaceTransform F ρ) := by
  classical
  let Z : Set ℂ := {ρ | chapter04NontrivialZero K ρ}
  let S : ℕ → Set ℂ := fun n => {ρ | (ρ ∉ Z ∧ n = 0) ∨
    (ρ ∈ Z ∧ Nat.ceil |ρ.im| = n)}
  have hpartition : ∀ ρ : ℂ, ∃! n : ℕ, ρ ∈ S n := by
    intro ρ
    by_cases hz : ρ ∈ Z
    · refine ⟨Nat.ceil |ρ.im|, ?_, ?_⟩
      · exact Or.inr ⟨hz, rfl⟩
      · intro n hn
        change (ρ ∉ Z ∧ n = 0) ∨
          (ρ ∈ Z ∧ Nat.ceil |ρ.im| = n) at hn
        rcases hn with ⟨hnz, hn0⟩ | hn
        · exact False.elim (hnz hz)
        · exact hn.2.symm
    · refine ⟨0, ?_, ?_⟩
      · exact Or.inl ⟨hz, rfl⟩
      · intro n hn
        change (ρ ∉ Z ∧ n = 0) ∨
          (ρ ∈ Z ∧ Nat.ceil |ρ.im| = n) at hn
        rcases hn with ⟨hnz, hn0⟩ | hn
        · exact hn0
        · exact False.elim (hz hn.1)
  let f : ℂ → ℂ := fun ρ =>
    (chapter04ZeroMultiplicity K ρ : ℂ) *
      chapter05BilateralLaplaceTransform F ρ
  let b : ℂ → ℝ := fun ρ => ‖f ρ‖
  have hfiniteS : ∀ n : ℕ, 0 < n → (S n).Finite := by
    intro n hn
    apply (chapter04_zero_band_finite K n).subset
    intro ρ hρ
    change (ρ ∉ Z ∧ n = 0) ∨
      (ρ ∈ Z ∧ Nat.ceil |ρ.im| = n) at hρ
    rcases hρ with ⟨hnot, hn0⟩ | hρ
    · omega
    · refine ⟨hρ.1, ?_⟩
      exact (Nat.ceil_le).mp hρ.2.le
  have hfinite_component : ∀ n : ℕ, Summable (fun ρ : S n => b ρ) := by
    intro n
    by_cases hn : n = 0
    · subst n
      let P : Set (S 0) :=
        Subtype.val ⁻¹' chapter04ZeroBand K 0
      have hP : P.Finite := by
        apply (chapter04_zero_band_finite K 0).preimage
        intro x hx y hy hxy
        exact Subtype.ext hxy
      exact summable_of_ne_finset_zero (s := hP.toFinset) (by
        intro ρ hρ
        have hmzero : chapter04ZeroMultiplicity K (ρ : ℂ) = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro hmpos
          have hz := (chapter04_zero_multiplicity_pos_iff K).mp hmpos
          have hS := ρ.property
          change ((ρ : ℂ) ∉ Z ∧ 0 = 0) ∨
            ((ρ : ℂ) ∈ Z ∧ Nat.ceil |(ρ : ℂ).im| = 0) at hS
          rcases hS with ⟨hnot, _⟩ | hS
          · exact hnot hz
          · have hheight : |(ρ : ℂ).im| ≤ (0 : ℝ) := by
              simpa using (Nat.ceil_le).mp hS.2.le
            apply hρ
            exact hP.mem_toFinset.mpr ⟨hz, hheight⟩
        simp [b, f, hmzero])
    · let hFintype : Fintype (S n) := (hfiniteS n (Nat.pos_of_ne_zero hn)).fintype
      exact summable_of_ne_finset_zero (s := @Finset.univ (S n) hFintype)
        (fun ρ hρ => False.elim (hρ (by simp)))
  have htsum_finite : ∀ (T : Set ℂ) (hT : T.Finite),
      (∑' ρ : T, b ρ) = hT.toFinset.sum b := by
    intro T hT
    rw [tsum_subtype]
    have hsum : hT.toFinset.sum (T.indicator b) = hT.toFinset.sum b := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [Set.indicator_of_mem]
      exact hT.mem_toFinset.mp hρ
    rw [← hsum]
    exact (hasSum_sum_of_ne_finset_zero (f := T.indicator b)
      (s := hT.toFinset) (by
        intro ρ hρ
        have hmem : ρ ∉ T := by
          intro hmem
          exact hρ (hT.mem_toFinset.mpr hmem)
        simp [Set.indicator, hmem])).tsum_eq
  obtain ⟨Cdec, hCdec, hdecay⟩ :=
    chapter05_basically_admissible_vertical_decay hF 1 (by norm_num)
  have hrepr : ∀ ρ : ℂ, ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := by
    intro ρ
    apply Complex.ext <;> simp
  have hnorm : ∀ ρ : ℂ, b ρ =
      (chapter04ZeroMultiplicity K ρ : ℝ) *
        ‖chapter05BilateralLaplaceTransform F ρ‖ := by
    intro ρ
    simp [b, f]
  have hterm : ∀ (n : ℕ), 0 < n → ∀ ρ : ℂ,
      ρ ∈ chapter04ZeroBand K n \ chapter04ZeroBand K ((n : ℝ) - 1) →
      b ρ ≤ (chapter04ZeroMultiplicity K ρ : ℝ) *
        (Cdec / (n : ℝ) ^ 2) := by
    intro n hn ρ hρ
    have hstrip := chapter04_nontrivial_zero_in_critical_strip K hρ.1.1
    have hre : |ρ.re| ≤ (1 : ℝ) := by
      rw [abs_of_nonneg hstrip.1]
      exact hstrip.2
    have htrans := hdecay ρ.re ρ.im hre
    have htrans' :
        ‖chapter05BilateralLaplaceTransform F ρ‖ ≤
          Cdec / (1 + |ρ.im|) ^ 2 := by
      calc
        ‖chapter05BilateralLaplaceTransform F ρ‖ =
            ‖chapter05BilateralLaplaceTransform F
              ((ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I)‖ := by
          exact congrArg norm
            (congrArg (chapter05BilateralLaplaceTransform F) (hrepr ρ))
        _ ≤ Cdec / (1 + |ρ.im|) ^ 2 := htrans
    have hlow : (n : ℝ) ≤ 1 + |ρ.im| := by
      have hsmall := hρ.2
      have hsmall' : ¬ |ρ.im| ≤ (n : ℝ) - 1 := by
        intro hle
        exact hsmall ⟨hρ.1.1, hle⟩
      linarith
    have hden : (n : ℝ) ^ 2 ≤ (1 + |ρ.im|) ^ 2 := by
      nlinarith [abs_nonneg ρ.im]
    have hdiv : Cdec / (1 + |ρ.im|) ^ 2 ≤ Cdec / (n : ℝ) ^ 2 := by
      by_cases hCdecpos : 0 < Cdec
      · apply (div_le_div_iff_of_pos_left hCdecpos (by positivity) (by positivity)).2
        exact hden
      · have hCdec0 : Cdec = 0 :=
          le_antisymm (le_of_not_gt hCdecpos) hCdec
        simp [hCdec0]
    rw [hnorm]
    have hfinal :
        ‖chapter05BilateralLaplaceTransform F ρ‖ ≤ Cdec / (n : ℝ) ^ 2 :=
      htrans'.trans hdiv
    exact mul_le_mul_of_nonneg_left hfinal (by positivity)
  obtain ⟨Ccount, hCcount, hcount⟩ := chapter04_zero_counting_unit_band_bound
  have hcountdiff : ∀ n : ℕ, 0 < n →
      ((chapter04ZeroCounting K n -
          chapter04ZeroCounting K ((n : ℝ) - 1) : ℕ) : ℝ) ≤
        Ccount * (Real.log (chapter04AbsoluteDiscriminant K) +
          (chapter04Degree K : ℝ) * Real.log ((n : ℝ) + 2)) := by
    intro n hn
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hraw := hcount ((n : ℝ) - 1) (by linarith) K
    have harg1 : (n : ℝ) - 1 + 1 = (n : ℝ) := by ring
    have harg3 : (n : ℝ) - 1 + 3 = (n : ℝ) + 2 := by ring
    rw [harg1, harg3] at hraw
    exact hraw
  have hshell_le :
      ∀ n : ℕ, 0 < n →
        (∑' ρ : S n, b ρ) ≤
          (Cdec / (n : ℝ) ^ 2) *
            ((chapter04ZeroCounting K n -
              chapter04ZeroCounting K ((n : ℝ) - 1) : ℕ) : ℝ) := by
    intro n hn
    let A : Set ℂ := chapter04ZeroBand K n
    let B : Set ℂ := chapter04ZeroBand K ((n : ℝ) - 1)
    let D : Set ℂ := A \ B
    have hA : A.Finite := by exact chapter04_zero_band_finite K n
    have hB : B.Finite := by
      exact chapter04_zero_band_finite K ((n : ℝ) - 1)
    have hBA : B ⊆ A := by
      intro ρ hρ
      have hρ' : ρ ∈ chapter04ZeroBand K ((n : ℝ) - 1) := by
        simpa [B] using hρ
      have hsmall : chapter04NontrivialZero K ρ ∧
          |ρ.im| ≤ (n : ℝ) - 1 := by
        simpa [chapter04ZeroBand] using hρ'
      have hupper : |ρ.im| ≤ (n : ℝ) := by linarith
      simpa [A, chapter04ZeroBand] using ⟨hsmall.1, hupper⟩
    have hD : D.Finite := hA.subset sdiff_subset
    have hsub : S n ⊆ D := by
      intro ρ hρ
      change (ρ ∉ Z ∧ n = 0) ∨
        (ρ ∈ Z ∧ Nat.ceil |ρ.im| = n) at hρ
      rcases hρ with ⟨hnot, hn0⟩ | hρ
      · omega
      · have hupper : |ρ.im| ≤ (n : ℝ) := (Nat.ceil_le).mp hρ.2.le
        have hnat : n - 1 < Nat.ceil |ρ.im| := by
          rw [hρ.2]
          omega
        have hlow0 : ((n - 1 : ℕ) : ℝ) < |ρ.im| :=
          (Nat.lt_ceil).mp hnat
        have hlow : (n : ℝ) - 1 < |ρ.im| := by
          have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub hn]
            norm_num
          rw [hcast] at hlow0
          exact hlow0
        have hAρ : ρ ∈ A := by
          simpa [A, chapter04ZeroBand] using ⟨hρ.1, hupper⟩
        have hnotB : ρ ∉ B := by
          intro hBρ
          have hBρ' : chapter04NontrivialZero K ρ ∧
              |ρ.im| ≤ (n : ℝ) - 1 := by
            simpa [B, chapter04ZeroBand] using hBρ
          exact (not_le_of_gt hlow) hBρ'.2
        exact ⟨hAρ, hnotB⟩
    have hsubfin : (hfiniteS n hn).toFinset ⊆ hD.toFinset :=
      (Set.Finite.toFinset_subset_toFinset).2 hsub
    have hsubsum :
        (hfiniteS n hn).toFinset.sum b ≤ hD.toFinset.sum b := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubfin
        (fun _ _ _ => norm_nonneg _)
    have hsumD :
        hD.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) =
          hA.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) -
            hB.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) := by
      have hsubAB : hB.toFinset ⊆ hA.toFinset :=
        (Set.Finite.toFinset_subset_toFinset).2 hBA
      rw [hA.toFinset_sdiff hB hD]
      have hsumAdd :
          hA.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) =
            (hA.toFinset \ hB.toFinset).sum
                (fun ρ => chapter04ZeroMultiplicity K ρ) +
              hB.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) := by
        rw [Finset.sum_sdiff hsubAB]
      omega
    rw [htsum_finite (S n) (hfiniteS n hn)]
    calc
      (hfiniteS n hn).toFinset.sum b ≤ hD.toFinset.sum b := hsubsum
      _ ≤ hD.toFinset.sum (fun ρ =>
          (chapter04ZeroMultiplicity K ρ : ℝ) *
            (Cdec / (n : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        apply hterm n hn ρ
        exact hD.mem_toFinset.mp hρ
      _ = (Cdec / (n : ℝ) ^ 2) *
          hD.toFinset.sum (fun ρ => (chapter04ZeroMultiplicity K ρ : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ hρ
        ring
      _ = (Cdec / (n : ℝ) ^ 2) *
          ((chapter04ZeroCounting K n -
            chapter04ZeroCounting K ((n : ℝ) - 1) : ℕ) : ℝ) := by
        rw [show chapter04ZeroCounting K n =
            hA.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) by rfl]
        rw [show chapter04ZeroCounting K ((n : ℝ) - 1) =
            hB.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) by rfl]
        rw [← hsumD]
        norm_num
  have hconst : ∀ n : ℕ, 0 < n →
      1 / (n : ℝ) ^ 2 ≤ 4 / ((n : ℝ) + 1) ^ 2 := by
    intro n hn
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hsqrt : ∀ n : ℕ, 0 < n →
      ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    intro n hn
    have hbase : (n : ℝ) + 2 ≤ 4 * (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc
      ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ (4 * (n : ℝ)) ^ (1 / 2 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) hbase
        norm_num
      _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        norm_num
  have hsqrt2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hp2 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num)]
    norm_num
    nlinarith [hsqrt2]
  have hratio : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 ≤
        4 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
    intro n hn
    have hnreal : (0 : ℝ) < n := by positivity
    have hbase : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hz : ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤
        4 * (n : ℝ) ^ (3 / 2 : ℝ) := by
      calc
        ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤
            (2 * (n : ℝ)) ^ (3 / 2 : ℝ) := by
          apply Real.rpow_le_rpow (by positivity) hbase
          norm_num
        _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
        _ ≤ 4 * (n : ℝ) ^ (3 / 2 : ℝ) := by
          gcongr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hprod : (n : ℝ) ^ (1 / 2 : ℝ) *
          ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
      calc
        _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) *
            (4 * (n : ℝ) ^ (3 / 2 : ℝ)) := by
          gcongr
        _ = 4 * ((n : ℝ) ^ (1 / 2 : ℝ) *
            (n : ℝ) ^ (3 / 2 : ℝ)) := by ring
        _ = 4 * (n : ℝ) ^ 2 := by
          rw [← Real.rpow_add hnreal]
          norm_num
    exact hprod
  have hlog : ∀ n : ℕ,
      Real.log ((n : ℝ) + 2) ≤ 2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ) := by
    intro n
    have h := Real.log_le_rpow_div (show 0 ≤ (n : ℝ) + 2 by positivity)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    convert h using 1; norm_num; ring
  let v : ℕ → ℝ := fun n => ∑' ρ : S n, b ρ
  have hA0 : 0 ≤ v 0 := by
    dsimp [v]
    exact tsum_nonneg (fun ρ => norm_nonneg (f (ρ : ℂ)))
  let A : ℝ := v 0 + 4 * Cdec * Ccount *
    |Real.log (chapter04AbsoluteDiscriminant K)|
  let B : ℝ := 16 * Cdec * Ccount * (chapter04Degree K : ℝ)
  let q : ℕ → ℝ := fun n =>
    A / ((n : ℝ) + 1) ^ 2 + B / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hq1 : Summable (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    convert h using 1
    funext n
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    rw [abs_of_nonneg hn]
    norm_num [Real.rpow_natCast]
  have hq2 : Summable (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
    convert h using 1
    funext n
    rw [abs_of_nonneg (by positivity)]
  have hq : Summable q := by
    dsimp [q]
    simpa [div_eq_mul_inv] using (hq1.mul_left A).add (hq2.mul_left B)
  have hvq : ∀ n : ℕ, v n ≤ q n := by
    intro n
    by_cases hn : n = 0
    · subst n
      dsimp [q, A]
      norm_num
      have htermA : 0 ≤ 4 * Cdec * Ccount *
          |Real.log (chapter04AbsoluteDiscriminant K)| := by positivity
      have htermB : 0 ≤ 16 * Cdec * Ccount *
          (chapter04Degree K : ℝ) := by positivity
      linarith
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hinner :
          Real.log (chapter04AbsoluteDiscriminant K) +
            (chapter04Degree K : ℝ) * Real.log ((n : ℝ) + 2) ≤
            |Real.log (chapter04AbsoluteDiscriminant K)| +
              (chapter04Degree K : ℝ) *
                (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)) := by
        gcongr
        · exact le_abs_self _
        · exact hlog n
      have hbase : v n ≤
          (Cdec / (n : ℝ) ^ 2) *
            (Ccount * (Real.log (chapter04AbsoluteDiscriminant K) +
              (chapter04Degree K : ℝ) * Real.log ((n : ℝ) + 2))) := by
        exact (hshell_le n hnpos).trans
          (mul_le_mul_of_nonneg_left (hcountdiff n hnpos) (by positivity))
      have harith :
          (Cdec / (n : ℝ) ^ 2) *
              (Ccount * (Real.log (chapter04AbsoluteDiscriminant K) +
                (chapter04Degree K : ℝ) * Real.log ((n : ℝ) + 2))) ≤
            (v 0 + 4 * Cdec * Ccount *
                |Real.log (chapter04AbsoluteDiscriminant K)|) /
                ((n : ℝ) + 1) ^ 2 +
              (16 * Cdec * Ccount * (chapter04Degree K : ℝ)) /
                ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
        have hleft :
            (Cdec / (n : ℝ) ^ 2) *
                (Ccount * (Real.log (chapter04AbsoluteDiscriminant K) +
                  (chapter04Degree K : ℝ) * Real.log ((n : ℝ) + 2))) ≤
              (Cdec / (n : ℝ) ^ 2) *
                (Ccount * (|Real.log (chapter04AbsoluteDiscriminant K)| +
                  (chapter04Degree K : ℝ) *
                    (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner hCcount) (by positivity)
        calc
          _ ≤ (Cdec / (n : ℝ) ^ 2) *
              (Ccount * (|Real.log (chapter04AbsoluteDiscriminant K)| +
                (chapter04Degree K : ℝ) *
                  (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)))) := hleft
          _ = (Cdec * Ccount *
                |Real.log (chapter04AbsoluteDiscriminant K)|) /
                (n : ℝ) ^ 2 +
              (2 * Cdec * Ccount * (chapter04Degree K : ℝ)) *
                (((n : ℝ) + 2) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2) := by ring
          _ ≤ (4 * Cdec * Ccount *
                |Real.log (chapter04AbsoluteDiscriminant K)|) /
                ((n : ℝ) + 1) ^ 2 +
              (2 * Cdec * Ccount * (chapter04Degree K : ℝ)) *
                (8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
            have hfirst :
                (Cdec * Ccount *
                  |Real.log (chapter04AbsoluteDiscriminant K)|) /
                    (n : ℝ) ^ 2 ≤
                  (4 * Cdec * Ccount *
                    |Real.log (chapter04AbsoluteDiscriminant K)|) /
                    ((n : ℝ) + 1) ^ 2 := by
              have hcoef : 0 ≤ Cdec * Ccount *
                  |Real.log (chapter04AbsoluteDiscriminant K)| := by positivity
              calc
                _ = (Cdec * Ccount *
                    |Real.log (chapter04AbsoluteDiscriminant K)|) *
                      (1 / (n : ℝ) ^ 2) := by ring
                _ ≤ (Cdec * Ccount *
                    |Real.log (chapter04AbsoluteDiscriminant K)|) *
                      (4 / ((n : ℝ) + 1) ^ 2) := by
                  exact mul_le_mul_of_nonneg_left (hconst n hnpos) hcoef
                _ = _ := by ring
            have hsqrtbound :
                ((n : ℝ) + 2) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 ≤
                  8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
              calc
                _ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 :=
                  div_le_div_of_nonneg_right (hsqrt n hnpos) (by positivity)
                _ = 2 * ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2) := by ring
                _ ≤ 2 * (4 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
                  exact mul_le_mul_of_nonneg_left (hratio n hnpos) (by norm_num)
                _ = 8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by ring
            have hcoef2 : 0 ≤ 2 * Cdec * Ccount *
                (chapter04Degree K : ℝ) := by positivity
            exact add_le_add hfirst
              (mul_le_mul_of_nonneg_left hsqrtbound hcoef2)
          _ ≤ (v 0 + 4 * Cdec * Ccount *
                |Real.log (chapter04AbsoluteDiscriminant K)|) /
                ((n : ℝ) + 1) ^ 2 +
              (16 * Cdec * Ccount * (chapter04Degree K : ℝ)) /
                ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
            have hfirst :
                (4 * Cdec * Ccount *
                  |Real.log (chapter04AbsoluteDiscriminant K)|) /
                    ((n : ℝ) + 1) ^ 2 ≤
                  (v 0 + 4 * Cdec * Ccount *
                    |Real.log (chapter04AbsoluteDiscriminant K)|) /
                    ((n : ℝ) + 1) ^ 2 := by
              exact (div_le_div_of_nonneg_right
                (le_add_of_nonneg_left hA0) (by positivity))
            have hsecond :
                (2 * Cdec * Ccount * (chapter04Degree K : ℝ)) *
                    (8 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) =
                  (16 * Cdec * Ccount * (chapter04Degree K : ℝ)) /
                    ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by ring
            exact add_le_add hfirst (le_of_eq hsecond)
      exact hbase.trans harith
  have hv : Summable v := by
    apply Summable.of_norm_bounded hq
    intro n
    have hv_nonneg : 0 ≤ v n := by
      dsimp [v]
      exact tsum_nonneg (fun ρ => norm_nonneg (f (ρ : ℂ)))
    rw [Real.norm_eq_abs, abs_of_nonneg hv_nonneg]
    exact hvq n
  have hpart := summable_partition (f := b)
    (fun ρ => norm_nonneg (f ρ)) hpartition
  have hb : Summable b := by
    apply hpart.mpr
    refine ⟨hfinite_component, ?_⟩
    simpa [v] using hv
  have hnormsum : Summable (fun ρ : ℂ => ‖f ρ‖) := by
    simpa [b] using hb
  have hf : Summable f := hnormsum.of_norm
  simpa [f] using hf

theorem chapter05_symmetric_zero_sum_converges
    (K : Type*) [Field K] [NumberField K]
    {F : ℝ → ℝ} (hF : Chapter05BasicallyAdmissible F) :
    Tendsto (chapter05SymmetricZeroPartialSum K F) atTop
      (𝓝 (chapter05SymmetricZeroSum K F)) := by
  classical
  let f : ℂ → ℂ := fun ρ =>
    (chapter04ZeroMultiplicity K ρ : ℂ) *
      chapter05BilateralLaplaceTransform F ρ
  have hf : Summable f := by
    simpa only [f] using chapter05_symmetric_zero_sum_summable K hF
  have hsum : HasSum f (∑' ρ : ℂ, f ρ) := hf.hasSum
  have hlim : Tendsto
      (fun T : ℝ => if hT : 0 ≤ T then
        (chapter04_zero_band_finite K T).toFinset.sum f else 0) atTop
      (𝓝 (∑' ρ : ℂ, f ρ)) := by
    intro U hU
    change ∀ᶠ T : ℝ in atTop,
      (if hT : 0 ≤ T then
        (chapter04_zero_band_finite K T).toFinset.sum f else 0) ∈ U
    have hU' : {s : Finset ℂ | s.sum f ∈ U} ∈ (atTop : Filter (Finset ℂ)) :=
      hsum hU
    rcases mem_atTop_sets.mp hU' with ⟨s, hs⟩
    have hband : ∀ᶠ T : ℝ in atTop,
        0 ≤ T ∧ ∀ ρ ∈ s, |ρ.im| ≤ T := by
      refine (eventually_ge_atTop (0 : ℝ)).and ?_
      rw [eventually_all_finset]
      intro ρ hρ
      exact eventually_ge_atTop _
    filter_upwards [hband] with T hT
    have hsum_eq :
        ((chapter04_zero_band_finite K T).toFinset ∪ s).sum f =
          (chapter04_zero_band_finite K T).toFinset.sum f := by
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro ρ hρ hρnot
      have hρs : ρ ∈ s := by
        rcases Finset.mem_union.mp hρ with hρband | hρs
        · exact False.elim (hρnot hρband)
        · exact hρs
      have hρzero : ¬ chapter04NontrivialZero K ρ := by
        intro hρzero
        apply hρnot
        exact (chapter04_zero_band_finite K T).mem_toFinset.mpr
          ⟨hρzero, hT.2 ρ hρs⟩
      have hm : chapter04ZeroMultiplicity K ρ = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hmpos
        exact hρzero ((chapter04_zero_multiplicity_pos_iff K).mp hmpos)
      simp [hm]
    have hmem : (chapter04_zero_band_finite K T).toFinset ∪ s ∈
        {u : Finset ℂ | u.sum f ∈ U} := by
      apply hs
      exact Finset.subset_union_right
    simpa [hsum_eq, hT.1] using hmem
  change Tendsto
      (fun T : ℝ => if hT : 0 ≤ T then
        (chapter04_zero_band_finite K T).toFinset.sum f else 0) atTop
      (𝓝 (∑' ρ : ℂ, f ρ))
  exact hlim

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter05
