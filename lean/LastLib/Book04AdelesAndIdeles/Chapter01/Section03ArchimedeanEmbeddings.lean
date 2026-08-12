import LastLib.Book04AdelesAndIdeles.Chapter01.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter01

open NumberField NumberField.InfinitePlace
open scoped Classical

noncomputable section

/-! ## 1.3 Archimedean embeddings and the Minkowski space -/

variable (K : Type*) [Field K] [NumberField K]

theorem chapter01_signature_formula :
    chapter01RealPlaceCount K + 2 * chapter01ComplexPlaceCount K = chapter01Degree K := by
  simpa [chapter01RealPlaceCount, chapter01ComplexPlaceCount, chapter01Degree] using
    (NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K)

omit [NumberField K] in
theorem chapter01_infinite_place_is_real_or_complex
    (v : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace.IsReal v ∨ NumberField.InfinitePlace.IsComplex v :=
  v.isReal_or_isComplex

theorem chapter01_minkowski_space_model :
    Nonempty (chapter01MinkowskiSpace K ≃ₗ[ℝ]
      (Fin (chapter01RealPlaceCount K) → ℝ) ×
        (Fin (chapter01ComplexPlaceCount K) → ℂ)) := by
  sorry

theorem chapter01_minkowski_embedding_injective :
    Function.Injective (chapter01MinkowskiEmbedding K) := by
  exact NumberField.mixedEmbedding_injective K

theorem chapter01_integer_lattice_mem_iff {x : chapter01MinkowskiSpace K} :
    x ∈ NumberField.mixedEmbedding.integerLattice K ↔
      ∃ a : 𝓞 K, NumberField.mixedEmbedding K a = x := by
  sorry

theorem chapter01_integer_lattice_is_discrete :
    DiscreteTopology (NumberField.mixedEmbedding.integerLattice K) := by infer_instance

theorem chapter01_integer_lattice_is_full :
    IsZLattice ℝ (NumberField.mixedEmbedding.integerLattice K) := by infer_instance

theorem chapter01_lattice_basis_apply
    (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    NumberField.mixedEmbedding.latticeBasis K i =
      NumberField.mixedEmbedding K (NumberField.integralBasis K i) := by
  exact NumberField.mixedEmbedding.latticeBasis_apply K i

theorem chapter01_lattice_basis_span :
    Submodule.span ℤ (Set.range (NumberField.mixedEmbedding.latticeBasis K)) =
      NumberField.mixedEmbedding.integerLattice K := by
  exact NumberField.mixedEmbedding.span_latticeBasis K

theorem chapter01_integer_lattice_fundamental_domain :
    MeasureTheory.IsAddFundamentalDomain (NumberField.mixedEmbedding.integerLattice K)
      (ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis K)) := by
  exact NumberField.mixedEmbedding.fundamentalDomain_integerLattice K

theorem chapter01_bounded_integer_points_finite (r : ℝ) :
    ((NumberField.mixedEmbedding.integerLattice K : Set (chapter01MinkowskiSpace K)) ∩
      Metric.closedBall 0 r).Finite := by
  sorry

theorem chapter01_minkowski_quotient_compact :
    CompactSpace
      (chapter01MinkowskiSpace K ⧸
        (NumberField.mixedEmbedding.integerLattice K).toAddSubgroup) := by
  sorry

theorem chapter01_complex_coordinate_area_scale (z : ℂ) :
    chapter01ComplexAreaScale z = ‖z‖ ^ 2 := rfl

end

end LastLib.Book04AdelesAndIdeles.Chapter01
