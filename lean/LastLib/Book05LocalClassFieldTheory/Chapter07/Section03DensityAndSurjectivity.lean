import LastLib.Book05LocalClassFieldTheory.Chapter07.Section02Continuity

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory Opposite

/-- Every finite quotient of local reciprocity is onto. -/
theorem chapter07_local_reciprocity_surjective_on_finite_level
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (L : Chapter07FiniteAbelianIndex K KAb) :
    Function.Surjective
      (fun x : Kˣ =>
        InfiniteGalois.proj L
          ((chapter07AbelianGaloisLimitEquiv K KAb)
            (chapter07LocalReciprocity S x))) := by
  sorry

/-- For the canonical finite-level Galois system, surjectivity on every finite
projection is equivalent to density in the inverse limit. -/
theorem chapter07_local_reciprocity_dense_iff_finite_projections_surjective
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    DenseRange (chapter07LocalReciprocity S) ↔
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        Function.Surjective
          (fun x : Kˣ =>
            InfiniteGalois.proj L
              ((chapter07AbelianGaloisLimitEquiv K KAb)
                (chapter07LocalReciprocity S x))) := by
  sorry

/-- The image of local reciprocity is dense in the profinite abelian Galois
group. -/
theorem chapter07_local_reciprocity_dense
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    DenseRange (chapter07LocalReciprocity S) := by
  apply
    (chapter07_local_reciprocity_dense_iff_finite_projections_surjective S).2
  intro L
  exact chapter07_local_reciprocity_surjective_on_finite_level S L

/-- Data for the maximal unramified quotient in arithmetic normalization. -/
/- LOCAL_DEPENDENCY_GUESS: earlier local-field chapters provide the maximal
unramified quotient and identify its arithmetic coordinate. -/
structure Chapter07ArithmeticUnramifiedQuotient
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) where
  G : Type*
  [groupG : Group G]
  [topologyG : TopologicalSpace G]
  [topologicalGroupG : IsTopologicalGroup G]
  quotient : Gal(KAb / K) →* G
  quotient_continuous : Continuous quotient
  quotient_surjective : Function.Surjective quotient
  completionEquiv : G ≃ₜ* Chapter07ProfiniteIntegers
  valuation : Kˣ →* Multiplicative ℤ
  uniformizer : Kˣ
  valuation_uniformizer :
    valuation uniformizer = Multiplicative.ofAdd 1
  reciprocity_valuation :
    ∀ x : Kˣ,
      completionEquiv (quotient (chapter07LocalReciprocity S x)) =
      chapter07IntegerToProfiniteCompletion (Multiplicative.toAdd
          (valuation x))

/-- The arithmetic unramified coordinate of reciprocity has exactly the
integer image inside the profinite integers. -/
theorem chapter07_unramified_reciprocity_image_is_integer
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (U : Chapter07ArithmeticUnramifiedQuotient K KAb S) :
    Set.range (fun x : Kˣ =>
      U.completionEquiv (U.quotient (chapter07LocalReciprocity S x))) =
      Set.range chapter07IntegerToProfiniteCompletion := by
  sorry

/-- The integral powers form a dense proper subgroup of the profinite
integers. -/
theorem chapter07_integer_image_dense_and_proper :
    Dense (Set.range chapter07IntegerToProfiniteCompletion) ∧
      Set.range chapter07IntegerToProfiniteCompletion ≠
        (Set.univ : Set Chapter07ProfiniteIntegers) := by
  sorry

/-- No genuinely nonintegral profinite Frobenius exponent is represented by a
field element under the arithmetic-normalized unramified quotient. -/
theorem chapter07_local_reciprocity_not_surjective
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (U : Chapter07ArithmeticUnramifiedQuotient K KAb S) :
    ¬ Function.Surjective (chapter07LocalReciprocity S) := by
  sorry

/-- A topological group equivalence preserves compactness. -/
theorem chapter07_no_topological_equiv_from_noncompact_to_compact
    {X Y : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [NoncompactSpace X] [Group Y] [TopologicalSpace Y] [CompactSpace Y] :
    ¬ Nonempty (X ≃ₜ* Y) := by
  sorry

/-- The multiplicative group of a complete discretely valued local field with
finite residue field is noncompact. -/
/- LOCAL_DEPENDENCY_GUESS: the preceding local-field topology chapters supply
the valuation topology and its noncompact valuation coordinate. -/
theorem chapter07_local_field_units_noncompact
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ] (D : Chapter07LocalFieldData K) :
    NoncompactSpace Kˣ := by
  exact
    @LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01_local_field_units_noncompact
      K _ D.valuation D.local_field D.valuation_coordinate _ _
      D.unit_group_topology D.unit_group_topological D.coordinate_equiv

/-- The profinite abelian Galois target is compact. -/
theorem chapter07_reciprocity_target_is_compact
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :
    IsCompact (Set.univ : Set (Gal(KAb / K))) := by
  sorry

/-- The compactness obstruction for identifying K-units literally with the
whole profinite Galois group. -/
theorem chapter07_reciprocity_is_not_a_topological_equivalence
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ] [NoncompactSpace Kˣ]
    [IsAbelianGalois K KAb]
    (hcompact : IsCompact (Set.univ : Set (Gal(KAb / K)))) :
    ¬ Nonempty (Kˣ ≃ₜ* Gal(KAb / K)) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
