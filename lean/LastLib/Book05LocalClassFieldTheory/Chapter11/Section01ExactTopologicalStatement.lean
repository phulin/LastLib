import LastLib.Book05LocalClassFieldTheory.Chapter11.Dependencies
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.UniformSpace.OfCompactT2

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open scoped Topology

/-! ## 11.1. The exact topological statement -/

def chapter11IsProfiniteAbelianTarget
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] : Prop :=
  CompactSpace A ∧ TotallyDisconnectedSpace A

def chapter11FactorsThroughAbelianization
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalGroup G]
    (ρ : G →ₜ* A) : Prop :=
  ∃ ρab : TopologicalAbelianization G →ₜ* A,
    ρ = ρab.comp (chapter11AbelianizationMap G)

theorem chapter11_galois_character_factors_through_abelianization
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalGroup G]
    [T2Space A] (ρ : G →ₜ* A) :
    chapter11FactorsThroughAbelianization ρ := by
  have hcomm : commutator G ≤ ρ.toMonoidHom.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    change ρ.toMonoidHom (g * h * g⁻¹ * h⁻¹) = 1
    simp
  have hker : IsClosed (ρ.toMonoidHom.ker : Set G) := by
    have hpre : IsClosed (ρ ⁻¹' ({1} : Set A)) :=
      isClosed_singleton.preimage ρ.continuous
    convert hpre using 1
    ext x
    simp
  have hN : Subgroup.topologicalClosure (commutator G) ≤ ρ.toMonoidHom.ker := by
    exact closure_minimal hcomm hker
  let f : TopologicalAbelianization G →* A :=
    QuotientGroup.lift (Subgroup.topologicalClosure (commutator G)) ρ.toMonoidHom hN
  have hf : Continuous (f : TopologicalAbelianization G → A) := by
    change Continuous
      (QuotientGroup.lift (Subgroup.topologicalClosure (commutator G))
        ρ.toMonoidHom hN : TopologicalAbelianization G → A)
    apply Continuous.quotient_lift ρ.continuous
  refine ⟨{ toMonoidHom := f, continuous_toFun := hf }, ?_⟩
  rfl

noncomputable def chapter11CharacterAbelianization
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalGroup G]
    [T2Space A] (ρ : G →ₜ* A) : TopologicalAbelianization G →ₜ* A :=
  Classical.choose (chapter11_galois_character_factors_through_abelianization ρ)

theorem chapter11CharacterAbelianization_spec
    {G A : Type*} [Group G] [CommGroup A]
    [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalGroup G]
    [T2Space A] (ρ : G →ₜ* A) :
    ρ = (chapter11CharacterAbelianization ρ).comp
      (chapter11AbelianizationMap G) := by
  exact Classical.choose_spec
    (chapter11_galois_character_factors_through_abelianization ρ)

def chapter11ProfiniteExtensionOf
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    [IsTopologicalGroup A]
    (χ : Kˣ →ₜ* A) : Prop :=
  ∃ F : Chapter11ProfiniteCompletion Kˣ →ₜ* A,
    ∀ x : Kˣ,
      F (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
        Kˣ x) = χ x

theorem chapter11_profinite_extension_unique
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A]
    (χ : Kˣ →ₜ* A)
    {F₁ F₂ : Chapter11ProfiniteCompletion Kˣ →ₜ* A}
    (h₁ : ∀ x : Kˣ,
      F₁ (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
        Kˣ x) = χ x)
    (h₂ : ∀ x : Kˣ,
      F₂ (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
        Kˣ x) = χ x) :
    F₁ = F₂ := by
  apply DFunLike.ext _ _
  intro y
  have hη :
      F₁ ∘ LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
          Kˣ =
        F₂ ∘ LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
          Kˣ := by
    funext x
    change F₁
        (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
          Kˣ x) = F₂
        (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
          Kˣ x)
    rw [h₁ x, h₂ x]
  have hF :=
    (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07_open_profinite_completion_eta_dense
      (G := Kˣ)).equalizer F₁.continuous F₂.continuous hη
  exact congrFun hF y

def chapter11FiniteIndexNeighborhoodCondition
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (χ : Kˣ →ₜ* A) : Prop :=
  ∀ V : Set A, V ∈ 𝓝[closure (Set.range χ)] (1 : A) →
    ∃ H : Subgroup Kˣ,
      IsOpen (H : Set Kˣ) ∧ H.FiniteIndex ∧
        ∀ x ∈ H, χ x ∈ V

theorem chapter11_profinite_extension_iff_finite_index_neighborhood_condition
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ]
    [UniformSpace A] [IsUniformGroup A]
    [IsTopologicalGroup A]
    [T2Space A]
    (χ : Kˣ →ₜ* A)
    (hcofinal : chapter11OpenFiniteIndexCofinality (K := K)) :
    chapter11ProfiniteExtensionOf χ ↔
      IsComplete (closure (Set.range χ)) ∧
        chapter11FiniteIndexNeighborhoodCondition χ := by
  let η :=
    LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEta Kˣ
  constructor
  · rintro ⟨F, hF⟩
    have hcompact : IsCompact (Set.range F) := by
      rw [← Set.image_univ]
      exact isCompact_univ.image F.continuous
    have hclosed : IsClosed (Set.range F) := hcompact.isClosed
    have hFsubset : Set.range F ⊆ closure (Set.range χ) := by
      intro y hy
      rcases hy with ⟨z, rfl⟩
      exact (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07_open_profinite_completion_eta_dense
        (G := Kˣ)).induction_on z
        (isClosed_closure.preimage F.continuous) (fun x => by
          change F (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
            Kˣ x) ∈ closure (Set.range χ)
          rw [hF x]
          exact subset_closure ⟨x, rfl⟩)
    have hrange : closure (Set.range χ) = Set.range F := by
      apply le_antisymm
      · apply closure_minimal
        · rintro y ⟨x, rfl⟩
          exact ⟨η x, hF x⟩
        · exact hclosed
      · exact hFsubset
    refine ⟨?_, ?_⟩
    · rw [hrange]
      exact hcompact.isComplete
    · intro V hV
      rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hV with
        ⟨W, hW, hWV⟩
      have hpre : χ ⁻¹' W ∈ 𝓝 (1 : Kˣ) :=
        χ.continuous.continuousAt (by simpa using hW)
      rcases hcofinal (χ ⁻¹' W) hpre with ⟨H, hHo, hHf, hHsub⟩
      refine ⟨H, hHo, hHf, ?_⟩
      intro x hx
      apply hWV
      exact ⟨hHsub hx, subset_closure ⟨x, rfl⟩⟩
  · rintro ⟨hcomplete, hcondition⟩
    let S : Subgroup A := Subgroup.topologicalClosure χ.toMonoidHom.range
    let _ : CommGroup S :=
      Subgroup.commGroupTopologicalClosure χ.toMonoidHom.range (by
        intro x y
        exact mul_comm x y)
    have hScomplete : IsComplete (S : Set A) := by
      rw [Subgroup.topologicalClosure_coe]
      change IsComplete (closure (Set.range χ))
      exact hcomplete
    let _ : CompleteSpace S := hScomplete.completeSpace_coe
    let χS : Kˣ →* S :=
      χ.toMonoidHom.codRestrict S (fun x => by
        change χ x ∈ closure (Set.range χ)
        exact subset_closure ⟨x, rfl⟩)
    let _ : UniformSpace (Chapter11ProfiniteCompletion Kˣ) :=
      IsTopologicalGroup.rightUniformSpace (Chapter11ProfiniteCompletion Kˣ)
    let _ : CompleteSpace (Chapter11ProfiniteCompletion Kˣ) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    let _ : UniformSpace Kˣ := UniformSpace.comap
      (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn Kˣ)
      inferInstance
    let _ : IsUniformGroup (Chapter11ProfiniteCompletion Kˣ) := inferInstance
    let _ : IsUniformGroup Kˣ := IsUniformGroup.comap
      (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEta Kˣ)
    let pkg : AbstractCompletion Kˣ :=
      { space := Chapter11ProfiniteCompletion Kˣ
        coe := LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn Kˣ
        uniformStruct := inferInstance
        complete := inferInstance
        separation := inferInstance
        isUniformInducing := ⟨rfl⟩
        dense := LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07_open_profinite_completion_eta_dense
          (G := Kˣ) }
    let uK : UniformSpace Kˣ := inferInstance
    have hχS : @ContinuousAt Kˣ S
        uK.toTopologicalSpace
        (inferInstance : UniformSpace S).toTopologicalSpace χS 1 := by
      intro V hV
      change χS ⁻¹' V ∈ @nhds Kˣ uK.toTopologicalSpace 1
      have hV' : V ∈ 𝓝 (⟨1, by simp⟩ : S) := by simpa [χS] using hV
      rcases (mem_nhds_subtype (S : Set A) (⟨1, by simp⟩ : S) V).mp hV' with
        ⟨W, hW, hWV⟩
      have hWS : W ∈ 𝓝[(S : Set A)] (1 : A) := mem_nhdsWithin_of_mem_nhds hW
      rcases hcondition W hWS with ⟨H, hHo, hHf, hHχ⟩
      let m : LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenFiniteIndexNormalSubgroup
          Kˣ :=
        { toSubgroup := H
          isNormal' := inferInstance
          isFiniteIndex' := hHf
          isOpen := hHo }
      let _ : TopologicalSpace (Kˣ ⧸ H) := ⊥
      let _ : DiscreteTopology (Kˣ ⧸ H) := ⟨rfl⟩
      let p : LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion Kˣ
          →ₜ* (Kˣ ⧸ H) :=
        { toMonoidHom := LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
            Kˣ m
          continuous_toFun := by
            change Continuous
              (((ProfiniteGrp.limitCone
                (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenFiniteIndexProfiniteDiagram
                  Kˣ)).π.app m).hom :
                Chapter11ProfiniteCompletion Kˣ → (Kˣ ⧸ H))
            exact ((ProfiniteGrp.limitCone
              (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenFiniteIndexProfiniteDiagram
                Kˣ)).π.app m).hom.continuous_toFun }
      have hp' : p ⁻¹' ({1} : Set (Kˣ ⧸ H)) ∈
          𝓝 (1 : LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion Kˣ) := by
        have hp : IsOpen (p ⁻¹' ({1} : Set (Kˣ ⧸ H))) :=
          (isOpen_discrete _).preimage p.continuous
        have hp1 : (1 : Chapter11ProfiniteCompletion Kˣ) ∈
            p ⁻¹' ({1} : Set (Kˣ ⧸ H)) := by
          simp [p, m]
        exact hp.mem_nhds hp1
      have hHnhds : (H : Set Kˣ) ∈
          @nhds Kˣ uK.toTopologicalSpace 1 := by
        have hpre : (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEta
            Kˣ) ⁻¹'
              (p ⁻¹' ({1} : Set (Kˣ ⧸ H))) ∈
            @nhds Kˣ uK.toTopologicalSpace 1 := by
          change (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEta Kˣ) ⁻¹'
              (p ⁻¹' ({1} : Set (Kˣ ⧸ H))) ∈
            @nhds Kˣ
              (TopologicalSpace.induced
                (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
                  Kˣ)
                (inferInstance : UniformSpace (Chapter11ProfiniteCompletion Kˣ)).toTopologicalSpace) 1
          rw [nhds_induced]
          have heta_one :
              LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
                  Kˣ 1 = 1 := by
            exact (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEta
              Kˣ).map_one
          rw [heta_one]
          exact Filter.preimage_mem_comap hp'
        convert hpre using 1
        ext x
        simp only [Set.mem_preimage]
        change x ∈ H ↔ QuotientGroup.mk' H x = 1
        simp
      exact Filter.mem_of_superset hHnhds (fun (x : Kˣ) hx => by
        change χS x ∈ V
        apply hWV
        exact hHχ x hx)
    have hχS_uniform : @UniformContinuous Kˣ S
        uK (inferInstance : UniformSpace S) χS :=
      MonoidHom.uniformContinuous_of_continuousAt_one χS hχS
    let _ : TopologicalSpace (Chapter11ProfiniteCompletion Kˣ) :=
      (inferInstance : UniformSpace (Chapter11ProfiniteCompletion Kˣ)).toTopologicalSpace
    let _ : TopologicalSpace S := (inferInstance : UniformSpace S).toTopologicalSpace
    let f : Chapter11ProfiniteCompletion Kˣ → S := pkg.extend χS
    have hfcont : Continuous f := pkg.continuous_extend
    have hfη : ∀ x : Kˣ, f (η x) = χS x := fun x =>
      pkg.extend_coe hχS_uniform x
    have hf_one : f 1 = 1 := by
      rw [← η.map_one]
      rw [hfη]
      exact χS.map_one
    have hf_mul : ∀ x y : Chapter11ProfiniteCompletion Kˣ,
        f (x * y) = f x * f y := by
      let pkgProd := pkg.prod pkg
      let _ : TopologicalSpace pkgProd.space := pkgProd.uniformStruct.toTopologicalSpace
      have hmulfun :
          (fun p : Chapter11ProfiniteCompletion Kˣ × Chapter11ProfiniteCompletion Kˣ =>
            f (p.1 * p.2)) =
            (fun p => f p.1 * f p.2) := by
        apply pkgProd.funext
        · exact hfcont.comp (continuous_fst.mul continuous_snd)
        · exact (hfcont.comp continuous_fst).mul (hfcont.comp continuous_snd)
        · rintro ⟨a, b⟩
          change f (η (a * b)) = f (η a) * f (η b)
          rw [hfη, hfη, hfη]
          exact χS.map_mul a b
      intro x y
      exact congrFun hmulfun (x, y)
    let F₀ : Chapter11ProfiniteCompletion Kˣ →ₜ* S :=
      { toMonoidHom :=
          { toFun := f
            map_one' := hf_one
            map_mul' := hf_mul }
        continuous_toFun := hfcont }
    let inc : S →ₜ* A :=
      { toMonoidHom := S.subtype
        continuous_toFun := continuous_subtype_val }
    refine ⟨inc.comp F₀, ?_⟩
    intro x
    change (f (η x) : A) = χ x
    rw [hfη]
    rfl

theorem chapter11_profinite_extension_iff_finite_index_neighborhood_condition_of_complete_target
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ]
    [UniformSpace A] [IsUniformGroup A]
    [IsTopologicalGroup A]
    [T2Space A] [CompleteSpace A]
    (χ : Kˣ →ₜ* A)
    (hcofinal : chapter11OpenFiniteIndexCofinality (K := K)) :
    chapter11ProfiniteExtensionOf χ ↔
      chapter11FiniteIndexNeighborhoodCondition χ := by
  rw [chapter11_profinite_extension_iff_finite_index_neighborhood_condition χ hcofinal]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨isClosed_closure.isComplete, h⟩

/-!
The main classification is stated as an equivalence.  The proof uses the
completion comparison in `Chapter11ReciprocityData` and the universal
-/

noncomputable def chapter11AbelianContinuousCharacterEquiv
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) :
    (TopologicalAbelianization G →ₜ* A) ≃ (Kˣ →ₜ* A) := by
  letI : UniformSpace A := IsTopologicalGroup.rightUniformSpace A
  letI : IsUniformGroup A := inferInstance
  letI : CompleteSpace A :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  have hcondition : ∀ χ : Kˣ →ₜ* A,
      chapter11FiniteIndexNeighborhoodCondition χ := by
    intro χ V hV
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hV with
      ⟨W, hW, hWV⟩
    have hpre : χ ⁻¹' W ∈ 𝓝 (1 : Kˣ) :=
      χ.continuous.continuousAt (by simpa using hW)
    rcases R.openFiniteIndexCofinality (χ ⁻¹' W) hpre with
      ⟨H, hHo, hHf, hHsub⟩
    refine ⟨H, hHo, hHf, ?_⟩
    intro x hx
    apply hWV
    exact ⟨hHsub hx, subset_closure ⟨x, rfl⟩⟩
  have hExt : ∀ χ : Kˣ →ₜ* A, chapter11ProfiniteExtensionOf χ := by
    intro χ
    apply (chapter11_profinite_extension_iff_finite_index_neighborhood_condition_of_complete_target
      χ R.openFiniteIndexCofinality).mpr
    exact hcondition χ
  let extend : (Kˣ →ₜ* A) → (Chapter11ProfiniteCompletion Kˣ →ₜ* A) :=
    fun χ => Classical.choose (hExt χ)
  have extend_spec : ∀ (χ : Kˣ →ₜ* A) (x : Kˣ),
      extend χ
          (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
            Kˣ x) = χ x := by
    intro χ x
    exact Classical.choose_spec (hExt χ) x
  let e_inv : TopologicalAbelianization G →ₜ* Chapter11ProfiniteCompletion Kˣ :=
    { toMonoidHom := R.completionEquiv.symm.toMonoidHom
      continuous_toFun := R.completionEquiv.symm.continuous }
  refine
    { toFun := fun ρ => ρ.comp R.reciprocity
      invFun := fun χ => (extend χ).comp e_inv
      left_inv := ?_
      right_inv := ?_ }
  · intro ρ
    apply DFunLike.ext _ _
    intro y
    have hext : extend (ρ.comp R.reciprocity) =
        ρ.comp R.completionEquiv := by
      apply chapter11_profinite_extension_unique (ρ.comp R.reciprocity)
        (extend_spec (ρ.comp R.reciprocity))
      intro x
      change ρ (R.completionEquiv
        (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
          Kˣ x)) = ρ (R.reciprocity x)
      rw [R.reciprocity_eq_completion x]
    change (extend (ρ.comp R.reciprocity)).comp e_inv y = ρ y
    rw [hext]
    change ρ (R.completionEquiv (R.completionEquiv.symm y)) = ρ y
    rw [R.completionEquiv.apply_symm_apply]
  · intro χ
    apply DFunLike.ext _ _
    intro x
    change (extend χ) (e_inv (R.reciprocity x)) = χ x
    change (extend χ) (R.completionEquiv.symm (R.reciprocity x)) = χ x
    rw [R.reciprocity_eq_completion x]
    rw [R.completionEquiv.symm_apply_apply]
    exact extend_spec χ x

noncomputable def chapter11ContinuousCharacterEquiv
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) :
    (G →ₜ* A) ≃ (Kˣ →ₜ* A) := by
  let e : (TopologicalAbelianization G →ₜ* A) ≃ (Kˣ →ₜ* A) :=
    chapter11AbelianContinuousCharacterEquiv R
  refine
    { toFun := fun ρ => e (chapter11CharacterAbelianization ρ)
      invFun := fun χ => (e.symm χ).comp (chapter11AbelianizationMap G)
      left_inv := by
        intro ρ
        apply DFunLike.ext
        intro x
        have hρ : ρ = (chapter11CharacterAbelianization ρ).comp
            (chapter11AbelianizationMap G) :=
          chapter11CharacterAbelianization_spec ρ
        change (e.symm (e (chapter11CharacterAbelianization ρ))).toMonoidHom
            (chapter11AbelianizationMap G x) = ρ x
        rw [e.symm_apply_apply]
        exact congrArg (fun ψ => ψ x) hρ.symm
      right_inv := by
        intro χ
        apply DFunLike.ext
        intro x
        have hχ : chapter11CharacterAbelianization
            ((e.symm χ).comp (chapter11AbelianizationMap G)) = e.symm χ := by
          apply DFunLike.ext
          intro y
          obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
          have hspec := chapter11CharacterAbelianization_spec
            ((e.symm χ).comp (chapter11AbelianizationMap G))
          change chapter11CharacterAbelianization
              ((e.symm χ).comp (chapter11AbelianizationMap G))
              (chapter11AbelianizationMap G g) =
            (e.symm χ) (chapter11AbelianizationMap G g)
          exact congrArg (fun ψ : G →ₜ* A => ψ g) hspec.symm
        change e (chapter11CharacterAbelianization
          ((e.symm χ).comp (chapter11AbelianizationMap G))) x = χ x
        rw [hχ, e.apply_symm_apply] }

theorem chapter11_abelian_continuous_character_equiv_apply
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G)
    (ρ : TopologicalAbelianization G →ₜ* A) :
    chapter11AbelianContinuousCharacterEquiv R ρ =
      ρ.comp R.reciprocity := by
  rfl

theorem chapter11_continuous_character_equiv_apply
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) (ρ : G →ₜ* A) :
    chapter11ContinuousCharacterEquiv R ρ =
      ((chapter11AbelianContinuousCharacterEquiv R)
        (chapter11CharacterAbelianization ρ)) := by
  rfl

theorem chapter11_theorem_11_1
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) :
    Nonempty ((G →ₜ* A) ≃ (Kˣ →ₜ* A)) := by
  exact ⟨chapter11ContinuousCharacterEquiv R⟩

theorem chapter11_continuous_character_equiv_bijective
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) :
    Function.Bijective (chapter11ContinuousCharacterEquiv (A := A) R) := by
  exact (chapter11ContinuousCharacterEquiv (A := A) R).bijective

theorem chapter11_continuous_character_equiv_natural
    {K G A B : Type*} [Field K] [Group G] [CommGroup A] [CommGroup B]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalGroup G] [IsTopologicalGroup A]
    [IsTopologicalGroup B] [T2Space A] [T2Space B]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    [CompactSpace B] [TotallyDisconnectedSpace B]
    (R : Chapter11ReciprocityData K G) (f : A →ₜ* B) (ρ : G →ₜ* A) :
    (chapter11ContinuousCharacterEquiv R) (f.comp ρ) =
      f.comp ((chapter11ContinuousCharacterEquiv R) ρ) := by
  have hchar : chapter11CharacterAbelianization (f.comp ρ) =
      f.comp (chapter11CharacterAbelianization ρ) := by
    apply DFunLike.ext
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have h₁ : f.comp ρ =
        (chapter11CharacterAbelianization (f.comp ρ)).comp
          (chapter11AbelianizationMap G) :=
      chapter11CharacterAbelianization_spec (f.comp ρ)
    have h₂ : ρ = (chapter11CharacterAbelianization ρ).comp
        (chapter11AbelianizationMap G) :=
      chapter11CharacterAbelianization_spec ρ
    change chapter11CharacterAbelianization (f.comp ρ)
        (chapter11AbelianizationMap G g) =
      f (chapter11CharacterAbelianization ρ (chapter11AbelianizationMap G g))
    calc
      chapter11CharacterAbelianization (f.comp ρ)
          (chapter11AbelianizationMap G g) = f (ρ g) := by
            change ((chapter11CharacterAbelianization (f.comp ρ)).comp
              (chapter11AbelianizationMap G)) g = (f.comp ρ) g
            simpa [MonoidHom.comp_apply] using DFunLike.congr_fun h₁.symm g
      f (ρ g) = f (chapter11CharacterAbelianization ρ (chapter11AbelianizationMap G g)) := by
        exact congrArg (fun z : A => f z) (DFunLike.congr_fun h₂ g)
  rw [chapter11_continuous_character_equiv_apply,
    chapter11_continuous_character_equiv_apply, hchar]
  apply DFunLike.ext
  intro x
  rfl

def chapter11CharacterOfPair
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (α : A)
    (η : D.unitGroup →ₜ* A) : Kˣ →ₜ* A :=
  { toFun := fun x =>
      let p := D.decomposition.symm x
      α ^ p.1.toAdd * η p.2
    map_one' := by
      simp
    map_mul' := by
      intro x y
      simp [D.decomposition.symm.map_mul, zpow_add, mul_assoc] ; ac_rfl
    continuous_toFun := by
      exact
        (((@continuous_of_discreteTopology (Multiplicative ℤ) _ _ A _
          (fun z => α ^ z.toAdd)).comp continuous_fst).mul
          (η.continuous_toFun.comp continuous_snd)).comp
          D.decomposition_symm_continuous }

theorem chapter11_character_of_pair_apply_decomposition
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (α : A)
    (η : D.unitGroup →ₜ* A) (r : ℤ) (u : D.unitGroup) :
    chapter11CharacterOfPair D α η
        (D.uniformizer ^ r * (u : Kˣ)) = α ^ r * η u := by
  have hpair :
      D.decomposition.symm (D.uniformizer ^ r * (u : Kˣ)) =
        (Multiplicative.ofAdd r, u) := by
    apply D.decomposition.injective
    rw [D.decomposition.apply_symm_apply, D.decomposition_apply]
    rfl
  change (let p := D.decomposition.symm (D.uniformizer ^ r * (u : Kˣ));
    α ^ p.1.toAdd * η p.2) = _
  rw [hpair]
  rfl

def chapter11CharacterPairEquiv
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) :
    (Kˣ →ₜ* A) ≃ (A × (D.unitGroup →ₜ* A)) where
  toFun χ := (χ D.uniformizer, χ.comp (chapter11UnitInclusion D))
  invFun p := chapter11CharacterOfPair D p.1 p.2
  left_inv := by
    intro χ
    ext x
    sorry
  right_inv := by
    rintro ⟨α, η⟩
    apply Prod.ext
    · sorry
    · ext u
      sorry

def chapter11ChangedUniformizer
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) (a : D.unitGroup) : Kˣ :=
  (a : Kˣ) * D.uniformizer

def chapter11PairAfterUniformizerChange
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (α : A)
    (η : D.unitGroup →ₜ* A) (a : D.unitGroup) : A × (D.unitGroup →ₜ* A) :=
  (α * η a, η)

theorem chapter11_uniformizer_change_value
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) (a : D.unitGroup) :
    χ (chapter11ChangedUniformizer D a) = χ D.uniformizer * χ (a : Kˣ) := by
  sorry

theorem chapter11_character_pair_finite_image_iff
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (α : A)
    (η : D.unitGroup →ₜ* A) :
    chapter11FiniteImage (chapter11CharacterOfPair D α η) ↔
      IsOfFinOrder α ∧ chapter11FiniteImage η := by
  sorry

def chapter11ComplexCounterexample
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) : Kˣ →ₜ* ℂˣ :=
  chapter11CharacterOfPair D
    (Units.mk0 (2 : ℂ) (by norm_num))
    (1 : D.unitGroup →ₜ* ℂˣ)

theorem chapter11_complex_counterexample_not_galois
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter11LocalFieldData K) :
    ¬ chapter11ProfiniteExtensionOf (chapter11ComplexCounterexample D) ∧
      ¬ IsCompact (closure (Set.range (chapter11ComplexCounterexample D))) := by
  sorry

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
