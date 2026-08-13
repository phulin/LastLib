import LastLib.Book04AdelesAndIdeles.Chapter01.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter01

open NumberField NumberField.InfinitePlace
open Module
open Finset
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
  classical
  refine ⟨LinearEquiv.ofFinrankEq _ _ ?_⟩
  rw [NumberField.mixedEmbedding.finrank, Module.finrank_prod]
  simp only [Module.finrank_pi, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Fintype.card_fin, Finset.card_univ]
  simpa [chapter01Degree, chapter01RealPlaceCount, chapter01ComplexPlaceCount,
    Finset.sum_const, Nat.mul_comm] using (chapter01_signature_formula K).symm

theorem chapter01_minkowski_embedding_injective :
    Function.Injective (chapter01MinkowskiEmbedding K) := by
  exact NumberField.mixedEmbedding_injective K

theorem chapter01_integer_lattice_mem_iff {x : chapter01MinkowskiSpace K} :
    x ∈ NumberField.mixedEmbedding.integerLattice K ↔
      ∃ a : 𝓞 K, NumberField.mixedEmbedding K a = x := by
  simp [NumberField.mixedEmbedding.integerLattice]

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
  simpa [Set.inter_comm] using
    (let _ : DiscreteTopology (NumberField.mixedEmbedding.integerLattice K).toAddSubgroup :=
      (inferInstance : DiscreteTopology (NumberField.mixedEmbedding.integerLattice K))
     Metric.finite_isBounded_inter_isClosed
      (α := chapter01MinkowskiSpace K)
      (s := (↑(NumberField.mixedEmbedding.integerLattice K).toAddSubgroup :
        Set (chapter01MinkowskiSpace K)))
      DiscreteTopology.isDiscrete Metric.isBounded_closedBall inferInstance)

theorem chapter01_minkowski_quotient_compact :
    CompactSpace
      (chapter01MinkowskiSpace K ⧸
        (NumberField.mixedEmbedding.integerLattice K).toAddSubgroup) := by
  let b := NumberField.mixedEmbedding.latticeBasis K
  let C : Set (chapter01MinkowskiSpace K) := Module.Basis.parallelepiped b
  have hC : IsCompact C := by
    exact (Module.Basis.parallelepiped b).isCompact
  have hcover : ∀ x : chapter01MinkowskiSpace K,
      ∃ l : NumberField.mixedEmbedding.integerLattice K,
        (l : chapter01MinkowskiSpace K) + x ∈ C := by
    intro x
    obtain ⟨z, hz, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
    have hz' : (z : chapter01MinkowskiSpace K) ∈
        NumberField.mixedEmbedding.integerLattice K := by
      rw [← chapter01_lattice_basis_span K]
      exact z.property
    refine ⟨⟨(z : chapter01MinkowskiSpace K), hz'⟩, ?_⟩
    simpa [C, Submodule.vadd_def, vadd_eq_add, add_comm] using
      (ZSpan.fundamentalDomain_subset_parallelepiped b hz)
  let q : chapter01MinkowskiSpace K →
      chapter01MinkowskiSpace K ⧸
        (NumberField.mixedEmbedding.integerLattice K).toAddSubgroup :=
    QuotientAddGroup.mk' (NumberField.mixedEmbedding.integerLattice K).toAddSubgroup
  have hqcont : Continuous q := QuotientAddGroup.continuous_mk
  have hsurj : Function.Surjective q :=
    QuotientAddGroup.mk'_surjective (NumberField.mixedEmbedding.integerLattice K).toAddSubgroup
  have himage : q '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    rcases hsurj y with ⟨x, rfl⟩
    rcases hcover x with ⟨l, hl⟩
    refine ⟨(l : chapter01MinkowskiSpace K) + x, hl, ?_⟩
    change QuotientAddGroup.mk'
        (NumberField.mixedEmbedding.integerLattice K).toAddSubgroup
        ((l : chapter01MinkowskiSpace K) + x) =
      QuotientAddGroup.mk'
        (NumberField.mixedEmbedding.integerLattice K).toAddSubgroup x
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    change (l : chapter01MinkowskiSpace K) + x - x ∈
      (NumberField.mixedEmbedding.integerLattice K).toAddSubgroup
    rw [add_sub_cancel_right]
    change (l : chapter01MinkowskiSpace K) ∈ NumberField.mixedEmbedding.integerLattice K
    exact l.property
  refine ⟨?_⟩
  rw [← himage]
  exact hC.image hqcont

theorem chapter01_complex_coordinate_area_scale (z : ℂ) :
    chapter01ComplexAreaScale z = ‖z‖ ^ 2 := rfl

end

end LastLib.Book04AdelesAndIdeles.Chapter01
