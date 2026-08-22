import LastLib.Book04AdelesAndIdeles.Chapter04.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open Set Filter
open NumberField IsDedekindDomain
open scoped BigOperators Topology RestrictedProduct

/-! ### 4.2 The full adele ring -/

theorem chapter04_adeleRing_is_infinite_times_finite
    (K : Type*) [Field K] [NumberField K] :
    Chapter04AdeleRing K =
      (Chapter04InfiniteAdeleRing K × Chapter04FiniteAdeleRing K) := by
  rfl

def chapter04AdeleRingProductEquiv
    (K : Type*) [Field K] [NumberField K] :
    Chapter04AdeleRing K ≃+*
      Chapter04InfiniteAdeleRing K × Chapter04FiniteAdeleRing K :=
  RingEquiv.refl _

theorem chapter04_adeleRing_productEquiv_apply
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04AdeleRing K) :
    chapter04AdeleRingProductEquiv K x = (x.1, x.2) := by
  rfl

theorem chapter04_all_place_restrictedProduct_equiv_adeleRing
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter04AllPlaceRestrictedProduct K ≃+*
      Chapter04AdeleRing K) := by
  sorry

theorem chapter04_adeleRing_is_locally_compact_topological_ring
    (K : Type*) [Field K] [NumberField K] :
    LocallyCompactSpace (Chapter04AdeleRing K) ∧
      IsTopologicalRing (Chapter04AdeleRing K) := by
  sorry

theorem chapter04_adeleRing_multiplication_is_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (fun p : Chapter04AdeleRing K × Chapter04AdeleRing K =>
      p.1 * p.2) := by
  exact continuous_mul

def chapter04FullBasicOpen
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v)) :
    Set (Chapter04AdeleRing K) :=
  {x |
    (∀ v, v ∈ S → chapter04AdeleCoordinate K x v ∈ U v) ∧
      (∀ v : Chapter04FinitePlace K, Sum.inl v ∉ S →
        x.2 v ∈ chapter04FiniteLocalIntegerSet K v)}

def chapter04FullBasicOpenCondition
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v)) : Prop :=
  S.Finite ∧
    (∀ v, v ∈ S → IsOpen (U v)) ∧
    (∀ w : Chapter04InfinitePlace K, Sum.inr w ∈ S)

theorem chapter04_mem_fullBasicOpen_iff
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v))
    (x : Chapter04AdeleRing K) :
    x ∈ chapter04FullBasicOpen K S U ↔
      (∀ v, v ∈ S → chapter04AdeleCoordinate K x v ∈ U v) ∧
        (∀ v : Chapter04FinitePlace K, Sum.inl v ∉ S →
          x.2 v ∈ chapter04FiniteLocalIntegerSet K v) :=
  Iff.rfl

theorem chapter04_fullBasicOpen_isOpen
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v))
    (hU : chapter04FullBasicOpenCondition K S U) :
    IsOpen (chapter04FullBasicOpen K S U) := by
  sorry

theorem chapter04_full_adele_has_local_specification_basis
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04AdeleRing K) (V : Set (Chapter04AdeleRing K))
    (hV : V ∈ 𝓝 x) :
    ∃ S : Set (Chapter04Place K), ∃ U : ∀ v : Chapter04Place K,
      Set (chapter04LocalField K v),
      chapter04FullBasicOpenCondition K S U ∧
        x ∈ chapter04FullBasicOpen K S U ∧
          chapter04FullBasicOpen K S U ⊆ V := by
  sorry

theorem chapter04_full_basic_open_has_finitely_many_delicate_coordinates
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (U : ∀ v : Chapter04Place K, Set (chapter04LocalField K v))
    (hU : chapter04FullBasicOpenCondition K S U) :
    S.Finite ∧
      (∀ w : Chapter04InfinitePlace K, Sum.inr w ∈ S) := by
  exact ⟨hU.1, hU.2.2⟩

def chapter04FullCompactProductSet
    (K : Type*) [Field K] [NumberField K]
    (CInf : Set (Chapter04InfiniteAdeleRing K)) :
    Set (Chapter04AdeleRing K) :=
  CInf ×ˢ (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K))

theorem chapter04_full_compact_product_is_compact
    (K : Type*) [Field K] [NumberField K]
    (CInf : Set (Chapter04InfiniteAdeleRing K))
    (hC : IsCompact CInf) :
    IsCompact (chapter04FullCompactProductSet K CInf) := by
  exact hC.prod (chapter04_finiteIntegralAdele_is_compact_open K).1

theorem chapter04_full_compact_product_is_a_zero_neighborhood_iff
    (K : Type*) [Field K] [NumberField K]
    (CInf : Set (Chapter04InfiniteAdeleRing K)) :
    chapter04FullCompactProductSet K CInf ∈ 𝓝 (0 : Chapter04AdeleRing K) ↔
      CInf ∈ 𝓝 (0 : Chapter04InfiniteAdeleRing K) := by
  sorry

theorem chapter04_full_adele_has_no_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K] :
    ¬ ∃ H : AddSubgroup (Chapter04AdeleRing K),
      IsCompact (H : Set (Chapter04AdeleRing K)) ∧
        IsOpen (H : Set (Chapter04AdeleRing K)) := by
  sorry

theorem chapter04_infiniteAdeleRing_has_no_compact_open_additive_subgroup
    (K : Type*) [Field K] [NumberField K] :
    ¬ ∃ H : AddSubgroup (Chapter04InfiniteAdeleRing K),
      IsCompact (H : Set (Chapter04InfiniteAdeleRing K)) ∧
        IsOpen (H : Set (Chapter04InfiniteAdeleRing K)) := by
  sorry

theorem chapter04_full_compact_product_neighborhood_is_not_a_subgroup
    (K : Type*) [Field K] [NumberField K]
    (CInf : Set (Chapter04InfiniteAdeleRing K))
    (hC : IsCompact CInf)
    (hnhds : chapter04FullCompactProductSet K CInf ∈
      𝓝 (0 : Chapter04AdeleRing K)) :
    ¬ ∃ H : AddSubgroup (Chapter04AdeleRing K),
      (H : Set (Chapter04AdeleRing K)) = chapter04FullCompactProductSet K CInf := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter04
