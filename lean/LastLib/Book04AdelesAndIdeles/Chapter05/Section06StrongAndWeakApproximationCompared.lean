import LastLib.Book04AdelesAndIdeles.Chapter05.Section03DiscretenessInTheFullAdeles

namespace LastLib.Book04AdelesAndIdeles.Chapter05

open LastLib.Book04AdelesAndIdeles.Chapter01
open LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open scoped Topology

/-! ## 5.6. Strong and weak approximation compared -/

theorem chapter05_away_complement_is_finite_place
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hSinf : chapter05InfinitePlaces K ⊆ S) :
    ∀ v : Chapter04Place K, v ∉ S →
      ∃ w : Chapter04FinitePlace K, v = Sum.inl w := by
  sorry

/-! For a finite set `S` containing every canonical infinite place, the
following is the restricted product away from `S`. -/

theorem chapter05_theorem_5_6_strong_approximation_away_from_S
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) (hSfinite : S.Finite)
    (hSinf : chapter05InfinitePlaces K ⊆ S) :
    chapter05StrongApproximationAwayFrom K S := by
  sorry

theorem chapter05_strong_approximation_away_neighborhood_form
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hstrong : chapter05StrongApproximationAwayFrom K S) :
    ∀ (T : Finset {v // v ∉ S})
      (x : ∀ v : T, chapter04LocalField K v.1)
      (W : ∀ v : T, Set (chapter04LocalField K v.1)),
      (∀ v : T, W v ∈ 𝓝 (0 : chapter04LocalField K v.1)) →
        ∃ a : K,
          (∀ v : T,
            chapter05LocalEmbedding K v.1 a - x v ∈ W v) ∧
          (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
            chapter05LocalEmbedding K v.1 a ∈
              (chapter04LocalIntegralSubring K v.1 :
                Set (chapter04LocalField K v.1))) := by
  sorry

theorem chapter05_away_restricted_product_has_canonical_basis
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) :
    chapter05RestrictedProductBasis K S := by
  sorry

theorem chapter05_away_diagonal_dense
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) (hSfinite : S.Finite)
    (hSinf : chapter05InfinitePlaces K ⊆ S)
    (hstrong : chapter05StrongApproximationAwayFrom K S) :
    DenseRange (chapter05AwayDiagonal K S hSinf) := by
  sorry

theorem chapter05_away_diagonal_closure_eq_univ
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) (hSfinite : S.Finite)
    (hSinf : chapter05InfinitePlaces K ⊆ S)
    (hstrong : chapter05StrongApproximationAwayFrom K S) :
    closure (Set.range (chapter05AwayDiagonal K S hSinf)) =
      (Set.univ : Set (Chapter05AdeleAwayFrom K S)) := by
  sorry

/-! The finite-to-away map is coordinate restriction on the canonical carrier;
the impossible infinite branch is retained only to make the dependent product
function total. -/

theorem chapter05_finite_to_away_projection_coordinate
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hfinite : ∀ v, v ∉ S → ∃ w : Chapter04FinitePlace K,
      v = Sum.inl w)
    (x : Chapter04FiniteAdeleRing K)
    (v : {v // v ∉ S}) :
    chapter05FiniteToAwayProjection K S hfinite x v =
      match h : v.1 with
      | Sum.inl w => x w
      | Sum.inr _ => 0 := by
  sorry

theorem chapter05_finite_to_away_projection_surjective
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hfinite : ∀ v, v ∉ S → ∃ w : Chapter04FinitePlace K,
      v = Sum.inl w) :
    Function.Surjective (chapter05FiniteToAwayProjection K S hfinite) := by
  sorry

theorem chapter05_finite_to_away_projection_diagonal
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hSinf : chapter05InfinitePlaces K ⊆ S)
    (hfinite : ∀ v, v ∉ S → ∃ w : Chapter04FinitePlace K,
      v = Sum.inl w) (a : K) :
    chapter05FiniteToAwayProjection K S hfinite (chapter05FiniteDiagonal K a) =
      chapter05AwayDiagonal K S hSinf a := by
  sorry

/-! With no places omitted, the canonical full-adele diagonal is discrete and
therefore cannot be dense in a nondiscrete full adele group. -/

theorem chapter05_full_adele_diagonal_not_dense
    (K : Type*) [Field K] [NumberField K] :
    ¬ DenseRange (chapter05Diagonal K) := by
  sorry

theorem chapter05_strong_approximation_with_no_omitted_places_is_false
    (K : Type*) [Field K] [NumberField K] :
    ¬ DenseRange (chapter05Diagonal K) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
