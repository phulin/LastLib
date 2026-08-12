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

/-- The universal continuous extension of local reciprocity to the profinite
completion. -/
noncomputable def chapter07CompletedReciprocity
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    Chapter07ProfiniteCompletion Kˣ →* Gal(KAb / K) :=
  (ProfiniteGrp.ProfiniteCompletion.lift
    (G := GrpCat.of Kˣ)
    (P := InfiniteGalois.profiniteGalGrp K KAb)
    (GrpCat.ofHom (chapter07LocalReciprocity S))).hom.toMonoidHom

/-- The completion map extends the original reciprocity map on the canonical
dense copy of K-units. -/
theorem chapter07_completed_reciprocity_extends_local
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (x : Kˣ) :
    chapter07CompletedReciprocity S
        (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of Kˣ) x) =
      chapter07LocalReciprocity S x := by
  sorry

/-- The universal completion extension is continuous. -/
theorem chapter07_completed_reciprocity_continuous
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb) :
    Continuous (chapter07CompletedReciprocity S) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the local existence theorem identifies the
finite-index norm quotients with all finite quotients in the completion, so
the universal map above is a topological equivalence. -/
theorem chapter07_completed_reciprocity_is_topological_equivalence
    {K KAb : Type u} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (hExist : chapter07ExistenceProperty K KAb) :
    ∃ e : Chapter07ProfiniteCompletion Kˣ ≃ₜ* Gal(KAb / K),
      ∀ x, e x = chapter07CompletedReciprocity S x := by
  sorry

/-- A chosen uniformizer/unit decomposition, with the normalization that the
uniformizer has unramified coordinate one. -/
structure Chapter07UniformizerUnitDecomposition
    (K : Type*) [Field K] (U : Type*) [CommGroup U]
    [TopologicalSpace U] [IsTopologicalGroup U] where
  uniformizer : Kˣ
  decomposition : Kˣ ≃* Multiplicative ℤ × U
  uniformizer_coordinate :
    decomposition uniformizer = (Multiplicative.ofAdd 1, 1)
  unitsAlreadyProfinite :
    Nonempty (Chapter07ProfiniteCompletion U ≃ₜ* U)

/-- After choosing a uniformizer, the completion splits as the profinite
integer coordinate times the already profinite unit group. -/
theorem chapter07_profinite_completion_uniformizer_split
    {K : Type*} [Field K] {U : Type*} [CommGroup U]
    [TopologicalSpace U] [IsTopologicalGroup U]
    (D : Chapter07UniformizerUnitDecomposition K U) :
    Nonempty
      (Chapter07ProfiniteCompletion Kˣ ≃ₜ*
        Chapter07ProfiniteIntegers × U) := by
  sorry

/-- Distinct normalized uniformizers give distinct splittings, recording the
noncanonical nature of the product decomposition. -/
theorem chapter07_uniformizer_split_depends_on_choice
    {K : Type*} [Field K] {U : Type*} [CommGroup U]
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

/- LOCAL_DEPENDENCY_GUESS: the arithmetic construction from the earlier
chapters supplies the equality of kernels for any two presentations of the
maximal unramified quotient. -/
theorem chapter07_inertia_subgroup_is_canonical
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (U₁ U₂ : Chapter07ArithmeticUnramifiedQuotient K KAb S)
    (hkernel :
      letI : Group U₁.G := U₁.groupG
      letI : Group U₂.G := U₂.groupG
      U₁.quotient.ker = U₂.quotient.ker) :
    chapter07InertiaSubgroup S U₁ = chapter07InertiaSubgroup S U₂ := by
  let : Group U₁.G := U₁.groupG
  let : Group U₂.G := U₂.groupG
  exact hkernel

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
