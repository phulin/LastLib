import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open scoped Topology

/-! ## 5.4. A local--global warning -/

/-! The real conic in the source is an elementary warning before the genuine
Hasse-principle counterexample. -/

def chapter05RealConicEquation (x y : ℝ) : Prop :=
  x ^ 2 + y ^ 2 = (-1 : ℝ)

theorem chapter05_real_conic_has_no_real_point :
    ¬ ∃ x y : ℝ, chapter05RealConicEquation x y := by
  sorry

/- SOURCE_ISSUE (§5.4, paragraph beginning “The diagonal embedding records
compatibility”): the source says “while subtler varieties can have points over
every completion and none over $K$” but names no variety and gives no
local-point predicate.  The smallest mathematical repair is the named Selmer
plane cubic below, with its projective nontriviality condition stated
explicitly. -/

def chapter05SelmerPlaneCubicEquation
    {F : Type*} [Ring F] (x : Fin 3 → F) : Prop :=
  3 * x 0 ^ 3 + 4 * x 1 ^ 3 + 5 * x 2 ^ 3 = 0

def chapter05SelmerPlaneCubic (x : Fin 3 → ℚ) : Prop :=
  chapter05SelmerPlaneCubicEquation x

def chapter05SelmerPlaneCubicLocalPoint
    (v : Chapter05Place ℚ) : Prop :=
  ∃ x : Fin 3 → Chapter05LocalField ℚ v,
    chapter05SelmerPlaneCubicEquation x ∧ ∃ i, x i ≠ 0

def chapter05SelmerPlaneCubicGlobalPoint : Prop :=
  ∃ x : Fin 3 → ℚ,
    chapter05SelmerPlaneCubic x ∧ ∃ i, x i ≠ 0

theorem chapter05_selmer_plane_cubic_has_point_over_every_completion :
    ∀ v : Chapter05Place ℚ, chapter05SelmerPlaneCubicLocalPoint v := by
  sorry

theorem chapter05_selmer_plane_cubic_has_no_global_point :
    ¬ chapter05SelmerPlaneCubicGlobalPoint := by
  sorry

def chapter05IntegralTailCondition
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter05FinitePlace K)) (a : K) : Prop :=
  ∀ v : Chapter05FinitePlace K, v ∉ S →
    chapter05FiniteDiagonal K a v ∈
      (Chapter05FiniteLocalIntegerRing K v :
        Set (Chapter05FiniteLocalField K v))

theorem chapter05_global_elements_have_finite_nonintegral_tail
    (K : Type*) [Field K] [NumberField K] (a : K) :
    ({v : Chapter05FinitePlace K |
      chapter05FiniteDiagonal K a v ∉
        (Chapter05FiniteLocalIntegerRing K v :
          Set (Chapter05FiniteLocalField K v))}).Finite := by
  sorry

theorem chapter05_strong_tail_is_an_almost_everywhere_requirement
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter05FinitePlace K)) (a : K)
    (hS : ∀ v : Chapter05FinitePlace K, v ∉ S →
      chapter05FiniteDiagonal K a v ∈
        (Chapter05FiniteLocalIntegerRing K v :
          Set (Chapter05FiniteLocalField K v))) :
    chapter05IntegralTailCondition K S a := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
