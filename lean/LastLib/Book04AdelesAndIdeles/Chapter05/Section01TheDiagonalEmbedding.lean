import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

open LastLib.Book04AdelesAndIdeles.Chapter01
open LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Filter
open NumberField
open scoped Topology nonZeroDivisors

/-! ## 5.1. The diagonal embedding -/

def chapter05FiniteLocalUnit
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K) (x : Chapter04FiniteLocalField K v) : Prop :=
  Valued.v x = 1

/-! The diagonal maps are the canonical algebra maps into Mathlib's finite and
full adele rings. -/

theorem chapter05Diagonal_apply
    (K : Type*) [Field K] [NumberField K] (a : K) :
    chapter05Diagonal K a = algebraMap K (Chapter04AdeleRing K) a := by
  rfl

theorem chapter05FiniteDiagonal_apply
    (K : Type*) [Field K] [NumberField K] (a : K) :
    chapter05FiniteDiagonal K a =
      IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K a := by
  rfl

theorem chapter05_diagonal_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (chapter05Diagonal K) := by
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 K) K

theorem chapter05_finite_diagonal_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (chapter05FiniteDiagonal K) := by
  intro a b h
  have hnonempty : Nonempty (Chapter04FinitePlace K) := by
    obtain ⟨I, hI⟩ := Ideal.exists_maximal (𝓞 K)
    exact ⟨(IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum
      (RingOfIntegers.not_isField K)).symm ⟨I, hI⟩⟩
  obtain ⟨v⟩ := hnonempty
  apply FaithfulSMul.algebraMap_injective K (v.adicCompletion K)
  have hv := congrArg (fun z : Chapter04FiniteAdeleRing K => z v) h
  change (algebraMap K (v.adicCompletion K) a) =
    algebraMap K (v.adicCompletion K) b at hv
  exact hv

theorem chapter05_completion_map_injective
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K) :
    Function.Injective (NumberField.FinitePlace.embedding (K := K) v) := by
  exact FaithfulSMul.algebraMap_injective K (v.adicCompletion K)

theorem chapter05_diagonal_components
    (K : Type*) [Field K] [NumberField K] (a : K) :
    chapter05Diagonal K a =
      (chapter05InfiniteDiagonal K a, chapter05FiniteDiagonal K a) := by
  exact Prod.ext (by rfl) (by rfl)

theorem chapter05_diagonal_is_integral_at_almost_all_finite_places
    (K : Type*) [Field K] [NumberField K] (a : K) :
    ({v : Chapter04FinitePlace K |
      chapter05FiniteDiagonal K a v ∉
        chapter04FiniteLocalIntegerSet K v}).Finite := by
  exact chapter04_finiteAdele_exceptionalSet_finite K (chapter05FiniteDiagonal K a)

theorem chapter05_diagonal_is_unit_or_zero_at_almost_all_finite_places
    (K : Type*) [Field K] [NumberField K] (a : K) :
    ({v : Chapter04FinitePlace K |
      chapter05FiniteDiagonal K a v ≠ 0 ∧
        ¬ chapter05FiniteLocalUnit K v (chapter05FiniteDiagonal K a v)} :
      Set (Chapter04FinitePlace K)).Finite := by
  by_cases ha : a = 0
  · subst a
    have hset : {v : Chapter04FinitePlace K |
        chapter05FiniteDiagonal K 0 v ≠ 0 ∧
          ¬ chapter05FiniteLocalUnit K v (chapter05FiniteDiagonal K 0 v)} =
        (∅ : Set (Chapter04FinitePlace K)) := by
      ext v
      constructor
      · intro hv
        exact (hv.1 rfl).elim
      · intro hv
        exact hv.elim
    rw [hset]
    exact Set.finite_empty
  · apply (chapter01_order_finite_support K ha).subset
    intro v hv hzero
    apply hv.2
    change Valued.v ((a : K) : v.adicCompletion K) = 1
    change LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent v a = 0 at hzero
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
        v ha, hzero]
    simp

theorem chapter05_unit_or_zero_component_is_integral
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter04FinitePlace K) (x : Chapter04FiniteLocalField K v)
    (h : x = 0 ∨ chapter05FiniteLocalUnit K v x) :
    x ∈ chapter04FiniteLocalIntegerSet K v := by
  exact h.elim (fun hx => by subst x; simp [chapter04FiniteLocalIntegerSet]) (fun hu => by
    change Valued.v x ≤ 1
    change Valued.v x = 1 at hu
    exact hu.le)

theorem chapter05_diagonal_integrality_iff
    (K : Type*) [Field K] [NumberField K] (a : K) :
    a ∈ chapter05RingOfIntegersSet K ↔
      ∀ v : Chapter04FinitePlace K,
        chapter05FiniteDiagonal K a v ∈
          chapter04FiniteLocalIntegerSet K v := by
  constructor
  · rintro ⟨r, rfl⟩ v
    change (algebraMap (𝓞 K) K r : v.adicCompletion K) ∈
      v.adicCompletionIntegers K
    exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem _ _ v r
  · intro ha
    change a ∈ Set.range (algebraMap (𝓞 K) K)
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K
    intro v
    have hv := ha v
    change Valued.v ((a : K) : v.adicCompletion K) ≤ 1 at hv
    rw [chapter01_completion_valuation_agrees_with_global K v a] at hv
    exact hv

/-! A canonical formulation of the unit-escape warning.  The size is the
normalized absolute value supplied by the infinite-place API, rather than a
field of an ad hoc place system. -/

structure Chapter05UnitEscapeWitness
    (K : Type*) [Field K] [NumberField K] where
  unit : Kˣ
  unit_ne_zero : (unit : K) ≠ 0
  unit_mem_integer : (unit : K) ∈ chapter05RingOfIntegersSet K
  inverse_mem_integer : (unit⁻¹ : K) ∈ chapter05RingOfIntegersSet K
  shrinkingPlace : Chapter04InfinitePlace K
  growingPlace : Chapter04InfinitePlace K
  size_nonnegative :
    ∀ (v : Chapter04InfinitePlace K) (x : K), 0 ≤ v x
  size_one : ∀ (v : Chapter04InfinitePlace K), v (1 : K) = 1
  size_mul :
    ∀ (v : Chapter04InfinitePlace K) (x y : K),
      v (x * y) = v x * v y
  shrinking :
    Tendsto
      (fun n : ℕ => shrinkingPlace ((unit : K) ^ n)) atTop (𝓝 0)
  growing :
    Tendsto
      (fun n : ℕ => growingPlace ((unit : K) ^ n)) atTop atTop

def chapter05PartialArchimedeanControlWarning
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04InfinitePlace K)) : Prop :=
  ∃ w : Chapter05UnitEscapeWitness K,
    (w.shrinkingPlace ∈ T ∧ w.growingPlace ∉ T) ∨
      (w.growingPlace ∈ T ∧ w.shrinkingPlace ∉ T)

def chapter05DiagonalImage
    (K : Type*) [Field K] [NumberField K] : Set (Chapter04AdeleRing K) :=
  Set.range (chapter05Diagonal K)

def chapter05FiniteDiagonalImage
    (K : Type*) [Field K] [NumberField K] :
    Set (Chapter04FiniteAdeleRing K) :=
  Set.range (chapter05FiniteDiagonal K)

theorem chapter05_diagonal_image_mem_iff
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04AdeleRing K) :
    x ∈ chapter05DiagonalImage K ↔
      ∃ a : K, chapter05Diagonal K a = x := by
  simp [chapter05DiagonalImage]

theorem chapter05_finite_diagonal_image_mem_iff
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) :
    x ∈ chapter05FiniteDiagonalImage K ↔
      ∃ a : K, chapter05FiniteDiagonal K a = x := by
  simp [chapter05FiniteDiagonalImage]

theorem chapter05_diagonal_image_eq_principal_subgroup
    (K : Type*) [Field K] [NumberField K] :
    chapter05DiagonalImage K =
      (NumberField.AdeleRing.principalSubgroup (𝓞 K) K :
        Set (Chapter04AdeleRing K)) := by
  rfl

theorem chapter05_finite_diagonal_image_eq_range_subgroup
    (K : Type*) [Field K] [NumberField K] :
    chapter05FiniteDiagonalImage K =
      ((chapter05FiniteDiagonal K).range.toAddSubgroup :
        Set (Chapter04FiniteAdeleRing K)) := by
  simp [chapter05FiniteDiagonalImage]

end

end LastLib.Book04AdelesAndIdeles.Chapter05
