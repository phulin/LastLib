import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

open LastLib.Book04AdelesAndIdeles.Chapter01
open LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open scoped Topology

/-! ## 5.4. A local--global warning -/

/-! The real conic is the elementary warning in the source.  The named Selmer
curve below is an optional concrete example strengthening that warning; the
source does not rely on this particular counterexample. -/

def chapter05RealConicEquation (x y : ℝ) : Prop :=
  x ^ 2 + y ^ 2 = (-1 : ℝ)

theorem chapter05_real_conic_has_no_real_point :
    ¬ ∃ x y : ℝ, chapter05RealConicEquation x y := by
  sorry

def chapter05SelmerPlaneCubicEquation
    {F : Type*} [Ring F] (x : Fin 3 → F) : Prop :=
  3 * x 0 ^ 3 + 4 * x 1 ^ 3 + 5 * x 2 ^ 3 = 0

def chapter05SelmerPlaneCubic (x : Fin 3 → ℚ) : Prop :=
  chapter05SelmerPlaneCubicEquation x

def chapter05SelmerPlaneCubicLocalPoint
    (v : Chapter04Place ℚ) : Prop :=
  ∃ x : Fin 3 → chapter04LocalField ℚ v,
    chapter05SelmerPlaneCubicEquation x ∧ ∃ i, x i ≠ 0

def chapter05SelmerPlaneCubicGlobalPoint : Prop :=
  ∃ x : Fin 3 → ℚ,
    chapter05SelmerPlaneCubic x ∧ ∃ i, x i ≠ 0

theorem chapter05_selmer_plane_cubic_has_point_over_every_completion :
    ∀ v : Chapter04Place ℚ, chapter05SelmerPlaneCubicLocalPoint v := by
  sorry

theorem chapter05_selmer_plane_cubic_has_no_global_point :
    ¬ chapter05SelmerPlaneCubicGlobalPoint := by
  sorry

def chapter05IntegralTailCondition
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K)) (a : K) : Prop :=
  ∀ v : Chapter04FinitePlace K, v ∉ S →
    chapter05FiniteDiagonal K a v ∈
      chapter04FiniteLocalIntegerSet K v

theorem chapter05_global_elements_have_finite_nonintegral_tail
    (K : Type*) [Field K] [NumberField K] (a : K) :
    ({v : Chapter04FinitePlace K |
      chapter05FiniteDiagonal K a v ∉
        chapter04FiniteLocalIntegerSet K v}).Finite := by
  sorry

theorem chapter05_strong_tail_is_an_almost_everywhere_requirement
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K)) (a : K)
    (hS : ∀ v : Chapter04FinitePlace K, v ∉ S →
      chapter05FiniteDiagonal K a v ∈
        chapter04FiniteLocalIntegerSet K v) :
    chapter05IntegralTailCondition K S a := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
