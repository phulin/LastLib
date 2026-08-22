import LastLib.Book05LocalClassFieldTheory.Chapter07.Section04Injectivity

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- The finite-quotient diagram underlying the profinite completion. -/
abbrev Chapter07FiniteQuotientDiagram (G : Type*) [Group G] :
    FiniteIndexNormalSubgroup (GrpCat.of G) ⥤ ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of G)

/-- Mathlib's profinite completion is the inverse limit of its finite
quotients.  For the commutative group K-units, finite-index normal subgroups
are the same as finite-index subgroups. -/
theorem chapter07_profinite_completion_is_the_finite_quotient_limit
    {G : Type*} [Group G] :
    Nonempty
      (Chapter07ProfiniteCompletion G ≃*
        (ProfiniteGrp.limit (Chapter07FiniteQuotientDiagram G) : Type _)) :=
  ⟨MulEquiv.refl _⟩

/-- The canonical copy of a group is dense in its profinite completion. -/
theorem chapter07_profinite_completion_eta_dense
    {G : Type*} [Group G] :
    DenseRange
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G)) :=
  ProfiniteGrp.ProfiniteCompletion.denseRange _

/-- The canonical map into the topology-sensitive completion is dense. -/
theorem chapter07_open_profinite_completion_eta_dense
    {G : Type*} [CommGroup G] [TopologicalSpace G] :
    DenseRange (chapter07OpenProfiniteCompletionEta G) := by
  sorry

/-- The canonical map into the open-indexed completion is continuous for the
original topological group. -/
theorem chapter07_open_profinite_completion_eta_continuous
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Continuous (chapter07OpenProfiniteCompletionEta G) := by
  sorry

/-- The universal continuous extension of local reciprocity to the profinite
completion. -/
theorem chapter07_open_completion_artin_extension_exists
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ)) →
    ∃ F : Chapter07OpenProfiniteCompletion Kˣ →* Gal(KAb / K),
      Continuous F ∧
        ∀ x,
          F (chapter07OpenProfiniteCompletionEta Kˣ x) =
            chapter07LocalReciprocity S x := by
  sorry

noncomputable def chapter07CompletedReciprocity
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ)) :
    Chapter07OpenProfiniteCompletion Kˣ →* Gal(KAb / K) :=
  (chapter07_open_completion_artin_extension_exists S hopen).choose

/-- The completion map extends the original reciprocity map on the canonical
dense copy of K-units. -/
theorem chapter07_completed_reciprocity_extends_local
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (x : Kˣ) :
    chapter07CompletedReciprocity S
        hopen
        (chapter07OpenProfiniteCompletionEta Kˣ x) =
      chapter07LocalReciprocity S x := by
  exact (chapter07_open_completion_artin_extension_exists S hopen).choose_spec.2 x

/-- The universal completion extension is continuous. -/
theorem chapter07_completed_reciprocity_continuous
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ)) →
    Continuous (chapter07CompletedReciprocity S hopen) := by
  intro hopen
  exact (chapter07_open_completion_artin_extension_exists S hopen).choose_spec.1

/- LOCAL_DEPENDENCY_GUESS: the local existence theorem identifies the
finite-index norm quotients with all finite quotients in the completion, so
the universal map above is a topological equivalence. -/
theorem chapter07_completed_reciprocity_is_topological_equivalence
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (hopen :
      ∀ L : Chapter07FiniteAbelianIndex K KAb,
        IsOpen (chapter07NormSubgroup (K := K) (L := L) : Set Kˣ))
    (hExist : chapter07ExistenceProperty K KAb) :
    ∃ e : Chapter07OpenProfiniteCompletion Kˣ ≃ₜ* Gal(KAb / K),
      ∀ x, e x = chapter07CompletedReciprocity S hopen x := by
  sorry

/-- A chosen uniformizer/unit decomposition, with the normalization that the
uniformizer has unramified coordinate one. -/
structure Chapter07UniformizerUnitDecomposition
    (K : Type*) [Field K] [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (U : Type*) [CommGroup U]
    [TopologicalSpace U] [IsTopologicalGroup U] where
  uniformizer : Kˣ
  decomposition : Kˣ ≃* Multiplicative ℤ × U
  decomposition_continuous : Continuous decomposition
  decomposition_symm_continuous : Continuous decomposition.symm
  uniformizer_coordinate :
    decomposition uniformizer = (Multiplicative.ofAdd 1, 1)
  unitsAlreadyProfinite :
    Nonempty (Chapter07OpenProfiniteCompletion U ≃ₜ* U)

/-- After choosing a uniformizer, the completion splits as the profinite
integer coordinate times the already profinite unit group. -/
theorem chapter07_profinite_completion_uniformizer_split
    {K : Type*} [Field K] {U : Type*} [CommGroup U]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [TopologicalSpace U] [IsTopologicalGroup U]
    (D : Chapter07UniformizerUnitDecomposition K U) :
    Nonempty
      (Chapter07OpenProfiniteCompletion Kˣ ≃ₜ*
        Chapter07ProfiniteIntegers × U) := by
  sorry

/-- Distinct normalized uniformizers give distinct splittings, recording the
noncanonical nature of the product decomposition. -/
theorem chapter07_uniformizer_split_depends_on_choice
    {K : Type*} [Field K] [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    {U : Type*} [CommGroup U]
    [TopologicalSpace U] [IsTopologicalGroup U]
    (D₁ D₂ : Chapter07UniformizerUnitDecomposition K U)
    (huniformizer : D₁.uniformizer ≠ D₂.uniformizer) :
    D₁.decomposition ≠ D₂.decomposition := by
  sorry

/-- The inertia subgroup presented as the kernel of an unramified quotient. -/
def chapter07InertiaSubgroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (U : Chapter07ArithmeticUnramifiedQuotient K KAb S) :
    Subgroup (Gal(KAb / K)) :=
  letI : Group U.G := U.groupG
  U.quotient.ker

theorem chapter07_inertia_subgroup_is_canonical
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (U₁ U₂ : Chapter07ArithmeticUnramifiedQuotient K KAb S) :
    (letI : Group U₁.G := U₁.groupG
     letI : Group U₂.G := U₂.groupG
     U₁.quotient.ker = U₂.quotient.ker) →
    chapter07InertiaSubgroup S U₁ = chapter07InertiaSubgroup S U₂ := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
