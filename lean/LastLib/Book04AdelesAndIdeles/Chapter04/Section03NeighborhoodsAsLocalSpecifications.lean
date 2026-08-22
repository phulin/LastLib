import LastLib.Book04AdelesAndIdeles.Chapter04.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open LastLib.Book04AdelesAndIdeles.Chapter01
open scoped BigOperators Topology RestrictedProduct nonZeroDivisors

/-! ### 4.3 Neighborhoods as local specifications -/

def chapter04FiniteBasicNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v)) :
    Set (Chapter04FiniteAdeleRing K) :=
  {x |
    (∀ v, v ∈ S → x v ∈ U v) ∧
    (∀ v, v ∉ S → x v ∈ chapter04FiniteLocalIntegerSet K v)}

def chapter04FiniteBasicNeighborhoodCondition
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v)) : Prop :=
  S.Finite ∧ ∀ v, v ∈ S → IsOpen (U v)

def chapter04FiniteDifferenceNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (x₀ : Chapter04FiniteAdeleRing K)
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v)) :
    Set (Chapter04FiniteAdeleRing K) :=
  {y |
    (∀ v, v ∈ S → y v ∈ U v) ∧
      (∀ v, v ∉ S → y v - x₀ v ∈ chapter04FiniteLocalIntegerSet K v)}

theorem chapter04_mem_finiteDifferenceNeighborhood_iff
    (K : Type*) [Field K] [NumberField K]
    (x₀ : Chapter04FiniteAdeleRing K)
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v))
    (y : Chapter04FiniteAdeleRing K) :
    y ∈ chapter04FiniteDifferenceNeighborhood K x₀ S U ↔
      (∀ v, v ∈ S → y v ∈ U v) ∧
        (∀ v, v ∉ S → y v - x₀ v ∈ chapter04FiniteLocalIntegerSet K v) :=
  Iff.rfl

theorem chapter04_finiteAdele_has_difference_local_specification_basis
    (K : Type*) [Field K] [NumberField K]
    (x₀ : Chapter04FiniteAdeleRing K) (V : Set (Chapter04FiniteAdeleRing K))
    (hV : V ∈ 𝓝 x₀) :
    ∃ S : Set (Chapter04FinitePlace K), ∃ U : ∀ v : Chapter04FinitePlace K,
      Set (Chapter04FiniteLocalField K v),
      chapter04FiniteBasicNeighborhoodCondition K S U ∧
        x₀ ∈ chapter04FiniteDifferenceNeighborhood K x₀ S U ∧
          chapter04FiniteDifferenceNeighborhood K x₀ S U ⊆ V := by
  sorry

theorem chapter04_difference_neighborhood_agrees_with_integral_tail
    (K : Type*) [Field K] [NumberField K]
    (x₀ : Chapter04FiniteAdeleRing K)
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v))
    (hS : ∀ v, v ∉ S → x₀ v ∈ chapter04FiniteLocalIntegerSet K v) :
    chapter04FiniteDifferenceNeighborhood K x₀ S U =
      chapter04FiniteBasicNeighborhood K S U := by
  sorry

theorem chapter04_mem_finiteBasicNeighborhood_iff
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v))
    (x : Chapter04FiniteAdeleRing K) :
    x ∈ chapter04FiniteBasicNeighborhood K S U ↔
      (∀ v, v ∈ S → x v ∈ U v) ∧
        (∀ v, v ∉ S → x v ∈ chapter04FiniteLocalIntegerSet K v) :=
  Iff.rfl

theorem chapter04_finiteBasicNeighborhood_isOpen
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04FinitePlace K))
    (U : ∀ v : Chapter04FinitePlace K, Set (Chapter04FiniteLocalField K v))
    (hU : chapter04FiniteBasicNeighborhoodCondition K S U) :
    IsOpen (chapter04FiniteBasicNeighborhood K S U) := by
  sorry

theorem chapter04_finiteAdele_has_local_specification_basis
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) (V : Set (Chapter04FiniteAdeleRing K))
    (hV : V ∈ 𝓝 x) :
    ∃ S : Set (Chapter04FinitePlace K), ∃ U : ∀ v : Chapter04FinitePlace K,
      Set (Chapter04FiniteLocalField K v),
      chapter04FiniteBasicNeighborhoodCondition K S U ∧
        x ∈ chapter04FiniteBasicNeighborhood K S U ∧
          chapter04FiniteBasicNeighborhood K S U ⊆ V := by
  sorry

def chapter04RationalLocalIntegerMultiple
    (m : ℤ) (v : Chapter04FinitePlace ℚ) :
    Set (Chapter04FiniteLocalField ℚ v) :=
  {x | ∃ z : Chapter04FiniteLocalIntegerRing ℚ v,
    x = (m : Chapter04FiniteLocalField ℚ v) * (z : Chapter04FiniteLocalField ℚ v)}

def chapter04RationalIntegerMultipleHatZ (m : ℤ) :
    Set (Chapter04FiniteAdeleRing ℚ) :=
  {x | ∀ v : Chapter04FinitePlace ℚ,
    x v ∈ chapter04RationalLocalIntegerMultiple m v}

theorem chapter04_rational_integer_multiple_hatZ_is_multiplication_by_m
    (m : ℤ) :
    chapter04RationalIntegerMultipleHatZ m =
      {x | ∃ z : Chapter04FiniteIntegralAdele ℚ,
        x = (m : Chapter04FiniteAdeleRing ℚ) *
          chapter04FiniteIntegralAdeleEmbedding ℚ z} := by
  sorry

theorem chapter04_rational_integer_multiple_hatZ_is_compact_open
    (m : ℤ) (hm : m ≠ 0) :
    IsCompact (chapter04RationalIntegerMultipleHatZ m) ∧
      IsOpen (chapter04RationalIntegerMultipleHatZ m) := by
  sorry

theorem chapter04_rational_integer_multiple_hatZ_is_a_neighborhood_subgroup
    (m : ℤ) (hm : m ≠ 0) :
    ∃ H : AddSubgroup (Chapter04FiniteAdeleRing ℚ),
      (H : Set (Chapter04FiniteAdeleRing ℚ)) =
        chapter04RationalIntegerMultipleHatZ m ∧
        IsCompact (H : Set (Chapter04FiniteAdeleRing ℚ)) ∧
        IsOpen (H : Set (Chapter04FiniteAdeleRing ℚ)) := by
  sorry

def chapter04FractionalIdealCompletion
    (K : Type*) [Field K] [NumberField K]
  (I : FractionalIdeal (𝓞 K)⁰ K) : Set (Chapter04FiniteAdeleRing K) :=
  {x | ∀ v : Chapter04FinitePlace K,
    x v ∈ chapter01LocalFractionalIdealBall v I}

theorem chapter04_fractionalIdealCompletion_is_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ H : AddSubgroup (Chapter04FiniteAdeleRing K),
      (H : Set (Chapter04FiniteAdeleRing K)) =
        chapter04FractionalIdealCompletion K I ∧
        IsCompact (H : Set (Chapter04FiniteAdeleRing K)) ∧
        IsOpen (H : Set (Chapter04FiniteAdeleRing K)) := by
  sorry

def chapter04FinitePrecisionNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ _ : S, ℤ) : Set (Chapter04FiniteAdeleRing K) :=
  {x |
    (∀ v : S,
      x v.1 ∈ chapter01LocalNeighborhood v.1 (m v)) ∧
      (∀ v : Chapter04FinitePlace K, v ∉ S →
        x v ∈ chapter04FiniteLocalIntegerSet K v)}

theorem chapter04_mem_finitePrecisionNeighborhood_iff
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ _ : S, ℤ) (x : Chapter04FiniteAdeleRing K) :
    x ∈ chapter04FinitePrecisionNeighborhood K S m ↔
      (∀ v : S,
        x v.1 ∈ chapter01LocalNeighborhood v.1 (m v)) ∧
        (∀ v : Chapter04FinitePlace K, v ∉ S →
          x v ∈ chapter04FiniteLocalIntegerSet K v) :=
  Iff.rfl

theorem chapter04_finitePrecisionNeighborhood_is_compact_open
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ v : S, ℤ) :
    IsCompact (chapter04FinitePrecisionNeighborhood K S m) ∧
      IsOpen (chapter04FinitePrecisionNeighborhood K S m) := by
  sorry

theorem chapter04_finitePrecisionNeighborhood_is_a_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ v : S, ℤ) :
    ∃ H : AddSubgroup (Chapter04FiniteAdeleRing K),
      (H : Set (Chapter04FiniteAdeleRing K)) =
        chapter04FinitePrecisionNeighborhood K S m ∧
        IsCompact (H : Set (Chapter04FiniteAdeleRing K)) ∧
        IsOpen (H : Set (Chapter04FiniteAdeleRing K)) := by
  sorry

theorem chapter04_finitePrecisionNeighborhoods_form_a_zero_basis
    (K : Type*) [Field K] [NumberField K]
    (V : Set (Chapter04FiniteAdeleRing K)) (hV : V ∈ 𝓝 0) :
    ∃ S : Finset (Chapter04FinitePlace K), ∃ m : ∀ v : S, ℤ,
      chapter04FinitePrecisionNeighborhood K S m ⊆ V := by
  sorry

theorem chapter04_independent_finite_exponents_are_fractional_ideal_completions
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) (m : ∀ v : S, ℤ) :
    ∃ I : FractionalIdeal (𝓞 K)⁰ K,
      chapter04FinitePrecisionNeighborhood K S m =
        chapter04FractionalIdealCompletion K I := by
  sorry

theorem chapter04_finiteAdele_neighborhoods_are_local_specifications_not_plain_product_neighborhoods
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) (V : Set (Chapter04FiniteAdeleRing K))
    (hV : V ∈ 𝓝 x) :
    ∃ S : Set (Chapter04FinitePlace K), ∃ U : ∀ v : Chapter04FinitePlace K,
      Set (Chapter04FiniteLocalField K v),
      S.Finite ∧
        (∀ v, IsOpen (U v)) ∧
        (∀ v, v ∉ S → U v = chapter04FiniteLocalIntegerSet K v) ∧
        x ∈ chapter04FiniteBasicNeighborhood K S U ∧
        chapter04FiniteBasicNeighborhood K S U ⊆ V := by
  sorry

abbrev chapter04FiniteAdeleUnrestrictedSubspaceTopology
    (K : Type*) [Field K] [NumberField K] :
    TopologicalSpace (Chapter04FiniteAdeleRing K) :=
  TopologicalSpace.induced
    (fun x : Chapter04FiniteAdeleRing K =>
      (x : ∀ v : Chapter04FinitePlace K, Chapter04FiniteLocalField K v))
    inferInstance

theorem chapter04_finiteAdele_restricted_topology_differs_from_plain_product_subspace
    (K : Type*) [Field K] [NumberField K] :
    (inferInstance : TopologicalSpace (Chapter04FiniteAdeleRing K)) ≠
      chapter04FiniteAdeleUnrestrictedSubspaceTopology K := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter04
