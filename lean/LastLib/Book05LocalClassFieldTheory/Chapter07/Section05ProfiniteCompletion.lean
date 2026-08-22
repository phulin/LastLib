import LastLib.Book05LocalClassFieldTheory.Chapter07.Section04Injectivity

namespace LastLib.Book05LocalClassFieldTheory.Chapter07

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- The finite-quotient diagram underlying the profinite completion. -/
abbrev Chapter07FiniteQuotientDiagram (G : Type*) [Group G] :
    FiniteIndexNormalSubgroup (GrpCat.of G) ⥤ ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of G)

/-- Mathlib's abstract profinite completion is the inverse limit of its
finite-index normal quotients.  The source's topology-sensitive completion is
recorded separately below. -/
theorem chapter07_profinite_completion_is_the_finite_quotient_limit
    {G : Type*} [Group G] :
    Nonempty
      (Chapter07ProfiniteCompletion G ≃*
        (ProfiniteGrp.limit (Chapter07FiniteQuotientDiagram G) : Type _)) :=
  ⟨MulEquiv.refl _⟩

/-- The completion used in the source is the inverse limit over open
finite-index quotients.  For the commutative multiplicative group, these are
the same subgroup quotients used in the source statement. -/
theorem chapter07_open_profinite_completion_is_the_open_finite_quotient_limit
    {G : Type*} [CommGroup G] [TopologicalSpace G] :
    Nonempty
      (Chapter07OpenProfiniteCompletion G ≃*
        (ProfiniteGrp.limit (chapter07OpenFiniteIndexProfiniteDiagram G) : Type _)) :=
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
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  have hpre : ⟨spc, hspc⟩ ∈ Subtype.val ⁻¹' s := hsv.symm ▸ uDefaultSpec
  have hspc_s : spc ∈ s := hpre
  rcases (isOpen_pi_iff.mp hsO) _ hspc_s with ⟨J, fJ, hJ1, hJ2⟩
  let M : Subgroup G := iInf fun (j : J) => j.1.toSubgroup
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hMFinite : M.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  have hMOpen : IsOpen (M : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => i.1.isOpen
  let m : Chapter07OpenFiniteIndexNormalSubgroup G :=
    { toSubgroup := M
      isNormal' := hM
      isFiniteIndex' := hMFinite
      isOpen := hMOpen }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use chapter07OpenProfiniteCompletionEtaFn G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a :=
    (iInf_le (fun (j : J) => (j.1.toSubgroup)) ⟨a, a_in_J⟩).hom
  change (ProfiniteGrp.Hom.hom
      ((LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenFiniteIndexProfiniteDiagram G).map
        M_to_Na))
      ((LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenProfiniteCompletionEtaFn G
        origin).val m) ∈ fJ a
  have horigin_map :
      (ProfiniteGrp.Hom.hom
          ((LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenFiniteIndexProfiniteDiagram G).map
            M_to_Na))
          ((LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenProfiniteCompletionEtaFn G
            origin).val m) =
        (ProfiniteGrp.Hom.hom
          ((LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01OpenFiniteIndexProfiniteDiagram G).map
            M_to_Na)) (spc m) := by
    congr 1
  rw [horigin_map]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).right

/-- The canonical map into the open-indexed completion is continuous for the
original topological group. -/
theorem chapter07_open_profinite_completion_eta_continuous
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Continuous (chapter07OpenProfiniteCompletionEta G) := by
  apply Continuous.subtype_mk
  refine continuous_pi
    (T := fun H => ((chapter07OpenFiniteIndexProfiniteDiagram G).obj H).toProfinite.toTop.str)
    (fun H ↦ ?_)
  let hdisc : DiscreteTopology (G ⧸ H.toSubgroup) :=
    QuotientGroup.discreteTopology_iff.mpr H.isOpen
  have htop :
      ((chapter07OpenFiniteIndexProfiniteDiagram G).obj H).toProfinite.toTop.str =
        (inferInstance : TopologicalSpace (G ⧸ H.toSubgroup)) := by
    change (⊥ : TopologicalSpace (G ⧸ H.toSubgroup)) =
      QuotientGroup.instTopologicalSpace H.toSubgroup
    exact hdisc.eq_bot.symm
  rw [htop]
  exact QuotientGroup.continuous_mk

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
  intro hopen
  exact
    LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01_open_completion_artin_extension_exists
      S hopen

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
  exact
    LastLib.Book05LocalClassFieldTheory.Chapter01.chapter01_completed_reciprocity_is_topological_equivalence
      S hopen hExist

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
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (I : Subgroup (Gal(KAb / K)))
    (U : Chapter07ArithmeticUnramifiedQuotient K KAb S I) :
    Subgroup (Gal(KAb / K)) :=
  letI : Group U.G := U.groupG
  U.quotient.ker

theorem chapter07_inertia_subgroup_is_quotient_kernel
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (I : Subgroup (Gal(KAb / K)))
    (U : Chapter07ArithmeticUnramifiedQuotient K KAb S I) :
    (letI : Group U.G := U.groupG; U.quotient.ker) =
      chapter07InertiaSubgroup S I U := by
  rfl

theorem chapter07_inertia_subgroup_eq_I
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (I : Subgroup (Gal(KAb / K)))
    (U : Chapter07ArithmeticUnramifiedQuotient K KAb S I) :
    chapter07InertiaSubgroup S I U = I := by
  change (letI : Group U.G := U.groupG; U.quotient.ker) = I
  exact U.quotient_kernel

theorem chapter07_inertia_subgroup_is_canonical
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb] (S : Chapter07FiniteArtinSystem K KAb)
    (I : Subgroup (Gal(KAb / K)))
    (U₁ U₂ : Chapter07ArithmeticUnramifiedQuotient K KAb S I) :
    chapter07InertiaSubgroup S I U₁ = chapter07InertiaSubgroup S I U₂ := by
  rw [chapter07_inertia_subgroup_eq_I S I U₁,
    chapter07_inertia_subgroup_eq_I S I U₂]

end

end LastLib.Book05LocalClassFieldTheory.Chapter07
