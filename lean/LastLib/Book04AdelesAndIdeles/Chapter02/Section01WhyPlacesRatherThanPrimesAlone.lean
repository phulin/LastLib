import LastLib.Book04AdelesAndIdeles.Chapter02.Core

namespace LastLib.Book04AdelesAndIdeles.Chapter02

noncomputable section

open NumberField
open NumberField.ComplexEmbedding
open scoped BigOperators

/-! ## 2.1. Why places rather than primes alone? -/

/-- The motivating local-global example: `X^2 + 1` has a root over at least one
`p`-adic field although it has no real root. -/
theorem chapter02_x_squared_plus_one_no_real_root :
    ¬ ∃ x : ℝ, x ^ 2 + 1 = 0 := by
  sorry

theorem chapter02_x_squared_plus_one_has_a_padic_root :
    ∃ p : Chapter02RationalPrime,
      letI : Fact p.1.Prime := ⟨p.2⟩
      ∃ x : ℚ_[p.1], x ^ 2 + 1 = 0 := by
  sorry

/-- Equivalence of absolute values is the order-equivalence relation used for
the topology of a place. -/
def Chapter02EquivalentAbsoluteValues {K : Type*} [Field K]
    (v w : AbsoluteValue K ℝ) : Prop := v.IsEquiv w

theorem chapter02_equivalent_absolute_values_iff_positive_power
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    Chapter02EquivalentAbsoluteValues v w ↔
      ∃ c : ℝ, 0 < c ∧ (v · ^ c) = w := by
  exact AbsoluteValue.isEquiv_iff_exists_rpow_eq

theorem chapter02_equivalent_absolute_values_iff_same_topology
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) :
    Chapter02EquivalentAbsoluteValues v w ↔
      IsHomeomorph (WithAbs.congr v w (.refl K)) := by
  exact AbsoluteValue.isEquiv_iff_isHomeomorph (F := K) v w

theorem chapter02_equivalent_absolute_values_preserves_nontriviality
    {K : Type*} [Field K] (v w : AbsoluteValue K ℝ)
    (hvw : Chapter02EquivalentAbsoluteValues v w) :
    v.IsNontrivial ↔ w.IsNontrivial := by
  exact hvw.isNontrivial_congr

theorem chapter02_equivalent_representatives_can_change_global_values
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (c : ℝ) (_hc : 0 < c) (x : K) :
    (v x) ^ c = (v · ^ c) x := by
  rfl

theorem chapter02_linearly_ordered_value_groups_have_no_torsion
    {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    {x : Γ} {n : ℕ} (hn : 0 < n) (h : n • x = 0) : x = 0 := by
  sorry

/-- A finite place is obtained from one nonzero prime ideal of the ring of
integers. -/
noncomputable def Chapter02FinitePlaceFromPrime
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Chapter02FinitePlace K :=
  NumberField.FinitePlace.mk v

/-- Mathlib's canonical indexing equivalence for finite places. -/
noncomputable def Chapter02FinitePlacePrimeIndexEquiv
    {K : Type*} [Field K] [NumberField K] :
    Chapter02FinitePlace K ≃ IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  NumberField.FinitePlace.equivHeightOneSpectrum

theorem chapter02_finite_place_recovered_from_prime
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Chapter02FinitePlacePrimeIndexEquiv (K := K)
        (Chapter02FinitePlaceFromPrime v) = v := by
  exact NumberField.FinitePlace.maximalIdeal_mk v

theorem chapter02_finite_place_completion_embedding_norm
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) :
    ‖NumberField.FinitePlace.embedding v x‖ =
      NumberField.HeightOneSpectrum.adicAbv K v x := by
  exact NumberField.FinitePlace.norm_embedding v x

/-- Real and complex embedding representatives for infinite places. -/
abbrev Chapter02RealEmbedding (K : Type*) [Field K] :=
  {φ : K →+* ℂ // ComplexEmbedding.IsReal φ}

abbrev Chapter02ComplexEmbedding (K : Type*) [Field K] :=
  {φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ}

noncomputable def Chapter02RealPlaceOfEmbedding
    {K : Type*} [Field K] [NumberField K] (φ : Chapter02RealEmbedding K) :
    Chapter02InfinitePlace K :=
  NumberField.InfinitePlace.mk φ.1

noncomputable def Chapter02ComplexPlaceOfEmbedding
    {K : Type*} [Field K] [NumberField K] (φ : Chapter02ComplexEmbedding K) :
    Chapter02InfinitePlace K :=
  NumberField.InfinitePlace.mk φ.1

/-- Real embeddings parametrize real infinite places. -/
noncomputable def Chapter02RealEmbeddingPlaceEquiv
    {K : Type*} [Field K] [NumberField K] :
    Chapter02RealEmbedding K ≃
      {w : Chapter02InfinitePlace K // w.IsReal} :=
  NumberField.InfinitePlace.mkReal

/-- Nonreal embeddings map onto complex places; the missing injectivity is
exactly conjugation. -/
noncomputable def Chapter02ComplexEmbeddingPlaceMap
    {K : Type*} [Field K] [NumberField K] :
    Chapter02ComplexEmbedding K →
      {w : Chapter02InfinitePlace K // w.IsComplex} :=
  NumberField.InfinitePlace.mkComplex

theorem chapter02_conjugate_embeddings_define_the_same_place
    {K : Type*} [Field K] (φ : K →+* ℂ) :
    NumberField.InfinitePlace.mk (ComplexEmbedding.conjugate φ) =
      NumberField.InfinitePlace.mk φ := by
  exact NumberField.InfinitePlace.mk_conjugate_eq φ

theorem chapter02_conjugate_embeddings_have_the_same_local_size
    {K : Type*} [Field K] (φ : K →+* ℂ) (x : K) :
    ‖ComplexEmbedding.conjugate φ x‖ = ‖φ x‖ := by
  sorry

theorem chapter02_complex_place_iff_conjugate_embedding_pair
    {K : Type*} [Field K] [NumberField K] (φ ψ : Chapter02ComplexEmbedding K) :
    Chapter02ComplexPlaceOfEmbedding φ = Chapter02ComplexPlaceOfEmbedding ψ ↔
      φ.1 = ψ.1 ∨ ComplexEmbedding.conjugate φ.1 = ψ.1 := by
  simp [Chapter02ComplexPlaceOfEmbedding]

theorem chapter02_infinite_place_is_real_or_complex
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) : w.IsReal ∨ w.IsComplex := by
  exact w.isReal_or_isComplex

noncomputable def chapter02_real_place_completion_is_real
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsReal) :
    Chapter02InfiniteCompletion w ≃+* ℝ := by
  exact NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw

noncomputable def chapter02_real_place_completion_isometric_to_real
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsReal) :
    Chapter02InfiniteCompletion w ≃ᵢ ℝ := by
  exact NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw

noncomputable def chapter02_complex_place_completion_is_complex
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsComplex) :
    Chapter02InfiniteCompletion w ≃+* ℂ := by
  exact NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw

noncomputable def chapter02_complex_place_completion_isometric_to_complex
    {K : Type*} [Field K] [NumberField K]
    (w : Chapter02InfinitePlace K) (hw : w.IsComplex) :
    Chapter02InfiniteCompletion w ≃ᵢ ℂ := by
  exact NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw

/-- Exhaustiveness of the finite/infinite classification, stated at the
absolute-value level so later users can choose their preferred representative. -/
theorem chapter02_finite_or_infinite_absolute_value
    {K : Type*} [Field K] [NumberField K]
    (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    NumberField.IsFinitePlace v ∨ NumberField.IsInfinitePlace v := by
  sorry

theorem chapter02_restriction_of_a_nontrivial_place_to_Q_is_nontrivial
    {K : Type*} [Field K] [NumberField K]
    (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    ∃ a : ℚ, a ≠ 0 ∧ v (algebraMap ℚ K a) ≠ 1 := by
  sorry

theorem chapter02_number_field_place_classification
    {K : Type*} [Field K] [NumberField K]
    (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    ∃ w : Chapter02Place K,
      Chapter02EquivalentAbsoluteValues v (Chapter02PlaceAbsoluteValue w) := by
  sorry

theorem chapter02_no_extra_places_beyond_prime_and_embedding_data
    {K : Type*} [Field K] [NumberField K]
    (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    (∃ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Chapter02EquivalentAbsoluteValues v (NumberField.FinitePlace.mk p).1) ∨
      (∃ φ : K →+* ℂ,
        Chapter02EquivalentAbsoluteValues v (NumberField.InfinitePlace.mk φ).1) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter02
