import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open Filter
open NumberField
open scoped Topology nonZeroDivisors

/-! ## 5.1. The diagonal embedding -/

def chapter05FiniteLocalUnit
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter05FinitePlace K) (x : Chapter05FiniteLocalField K v) : Prop :=
  Valued.v x = 1

/-! The diagonal maps are the canonical algebra maps into Mathlib's finite and
full adele rings. -/

theorem chapter05Diagonal_apply
    (K : Type*) [Field K] [NumberField K] (a : K) :
    chapter05Diagonal K a = algebraMap K (Chapter05AdeleRing K) a := by
  sorry

theorem chapter05FiniteDiagonal_apply
    (K : Type*) [Field K] [NumberField K] (a : K) :
    chapter05FiniteDiagonal K a =
      IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K a := by
  sorry

theorem chapter05_diagonal_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (chapter05Diagonal K) := by
  sorry

theorem chapter05_finite_diagonal_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (chapter05FiniteDiagonal K) := by
  sorry

theorem chapter05_completion_map_injective
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter05FinitePlace K) :
    Function.Injective (NumberField.FinitePlace.embedding (K := K) v) := by
  sorry

theorem chapter05_diagonal_components
    (K : Type*) [Field K] [NumberField K] (a : K) :
    chapter05Diagonal K a =
      (chapter05InfiniteDiagonal K a, chapter05FiniteDiagonal K a) := by
  sorry

theorem chapter05_diagonal_is_integral_at_almost_all_finite_places
    (K : Type*) [Field K] [NumberField K] (a : K) :
    ({v : Chapter05FinitePlace K |
      chapter05FiniteDiagonal K a v ∉
        chapter05FiniteLocalIntegerSet K v}).Finite := by
  sorry

theorem chapter05_diagonal_is_unit_or_zero_at_almost_all_finite_places
    (K : Type*) [Field K] [NumberField K] (a : K) :
    ({v : Chapter05FinitePlace K |
      chapter05FiniteDiagonal K a v ≠ 0 ∧
        ¬ chapter05FiniteLocalUnit K v (chapter05FiniteDiagonal K a v)} :
      Set (Chapter05FinitePlace K)).Finite := by
  sorry

theorem chapter05_unit_or_zero_component_is_integral
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter05FinitePlace K) (x : Chapter05FiniteLocalField K v)
    (h : x = 0 ∨ chapter05FiniteLocalUnit K v x) :
    x ∈ chapter05FiniteLocalIntegerSet K v := by
  sorry

theorem chapter05_diagonal_integrality_iff
    (K : Type*) [Field K] [NumberField K] (a : K) :
    a ∈ chapter05RingOfIntegersSet K ↔
      ∀ v : Chapter05FinitePlace K,
        chapter05FiniteDiagonal K a v ∈
          chapter05FiniteLocalIntegerSet K v := by
  sorry

/-! A canonical formulation of the unit-escape warning.  The size is the
normalized absolute value supplied by the infinite-place API, rather than a
field of an ad hoc place system. -/

structure Chapter05UnitEscapeWitness
    (K : Type*) [Field K] [NumberField K] where
  unit : Kˣ
  unit_ne_zero : (unit : K) ≠ 0
  unit_mem_integer : (unit : K) ∈ chapter05RingOfIntegersSet K
  inverse_mem_integer : (unit⁻¹ : K) ∈ chapter05RingOfIntegersSet K
  shrinkingPlace : Chapter05InfinitePlace K
  growingPlace : Chapter05InfinitePlace K
  size_nonnegative :
    ∀ (v : Chapter05InfinitePlace K) (x : K), 0 ≤ v x
  size_one : ∀ (v : Chapter05InfinitePlace K), v (1 : K) = 1
  size_mul :
    ∀ (v : Chapter05InfinitePlace K) (x y : K),
      v (x * y) = v x * v y
  shrinking :
    Tendsto
      (fun n : ℕ => shrinkingPlace ((unit : K) ^ n)) atTop (𝓝 0)
  growing :
    Tendsto
      (fun n : ℕ => growingPlace ((unit : K) ^ n)) atTop atTop

def chapter05PartialArchimedeanControlWarning
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter05InfinitePlace K)) : Prop :=
  ∃ w : Chapter05UnitEscapeWitness K,
    w.shrinkingPlace ∉ T ∧ w.growingPlace ∉ T

def chapter05DiagonalImage
    (K : Type*) [Field K] [NumberField K] : Set (Chapter05AdeleRing K) :=
  Set.range (chapter05Diagonal K)

def chapter05FiniteDiagonalImage
    (K : Type*) [Field K] [NumberField K] :
    Set (Chapter05FiniteAdeleRing K) :=
  Set.range (chapter05FiniteDiagonal K)

theorem chapter05_diagonal_image_mem_iff
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter05AdeleRing K) :
    x ∈ chapter05DiagonalImage K ↔
      ∃ a : K, chapter05Diagonal K a = x := by
  sorry

theorem chapter05_finite_diagonal_image_mem_iff
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter05FiniteAdeleRing K) :
    x ∈ chapter05FiniteDiagonalImage K ↔
      ∃ a : K, chapter05FiniteDiagonal K a = x := by
  sorry

theorem chapter05_diagonal_image_eq_principal_subgroup
    (K : Type*) [Field K] [NumberField K] :
    chapter05DiagonalImage K =
      (NumberField.AdeleRing.principalSubgroup (𝓞 K) K :
        Set (Chapter05AdeleRing K)) := by
  sorry

theorem chapter05_finite_diagonal_image_eq_range_subgroup
    (K : Type*) [Field K] [NumberField K] :
    chapter05FiniteDiagonalImage K =
      ((chapter05FiniteDiagonal K).range.toAddSubgroup :
        Set (Chapter05FiniteAdeleRing K)) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
