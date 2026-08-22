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

private noncomputable def chapter07_open_completion_lift
    {G H : Type*} [CommGroup G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (f : G →ₜ* H) :
    Chapter07OpenProfiniteCompletion G →ₜ*
      Chapter07OpenProfiniteCompletion H := by
  let preimage (V : Chapter07OpenFiniteIndexNormalSubgroup H) :
      Chapter07OpenFiniteIndexNormalSubgroup G := by
    let Psub : Subgroup G := V.toFiniteIndexNormalSubgroup.toSubgroup.comap (↑f : G →* H)
    let Pfin : FiniteIndexNormalSubgroup G :=
      { toSubgroup := Psub
        isNormal' := by
          dsimp [Psub]
          infer_instance
        isFiniteIndex' := by
          dsimp [Psub]
          rw [← FiniteIndexNormalSubgroup.toSubgroup_comap
            (↑f : G →* H) V.toFiniteIndexNormalSubgroup]
          infer_instance }
    refine { toFiniteIndexNormalSubgroup := Pfin, isOpen := ?_ }
    dsimp [Pfin, Psub]
    change IsOpen
      ((V.toFiniteIndexNormalSubgroup.toSubgroup.comap (↑f : G →* H) : Subgroup G) : Set G)
    have hset :
        (V.toFiniteIndexNormalSubgroup.toSubgroup.comap (↑f : G →* H) : Set G) =
          ((↑f : G →* H) : G → H) ⁻¹'
            (V.toFiniteIndexNormalSubgroup.toSubgroup : Set H) := by
      ext g
      calc
        g ∈ V.toFiniteIndexNormalSubgroup.toSubgroup.comap (↑f : G →* H) ↔
            (↑f : G →* H) g ∈ V.toFiniteIndexNormalSubgroup.toSubgroup :=
          Subgroup.mem_comap
        _ ↔ g ∈ ((↑f : G →* H) : G → H) ⁻¹'
            (V.toFiniteIndexNormalSubgroup.toSubgroup : Set H) := Iff.rfl
    have hhom : (↑f : G →* H) = f.toMonoidHom :=
      (ContinuousMonoidHom.coe_toMonoidHom f).symm
    have hcont : Continuous ((↑f : G →* H) : G → H) := by
      rw [hhom]
      exact f.continuous_toFun
    convert V.isOpen.preimage hcont using 1
  let component (V : Chapter07OpenFiniteIndexNormalSubgroup H) :
      Chapter07OpenProfiniteCompletion G →*
        (H ⧸ V.toFiniteIndexNormalSubgroup.toSubgroup) :=
    let P := preimage V
    let q : (G ⧸ P.toFiniteIndexNormalSubgroup.toSubgroup) →*
        (H ⧸ V.toFiniteIndexNormalSubgroup.toSubgroup) :=
      QuotientGroup.map _ _ (↑f) (by
        intro g hg
        dsimp [P, preimage] at hg
        exact hg)
    q.comp (chapter07OpenProfiniteCompletionProjection G P)
  let phi : Chapter07OpenProfiniteCompletion G →
      Chapter07OpenProfiniteCompletion H := fun x =>
    ⟨fun V => component V x, by
      intro V W hVW
      have hVWsub : V.toSubgroup ≤ W.toSubgroup := hVW.down.down
      dsimp [component]
      change
        (QuotientGroup.map V.toSubgroup W.toSubgroup (MonoidHom.id H) (by
          intro g hg
          exact Subgroup.mem_comap.mpr (by simpa using hVWsub hg)))
            ((QuotientGroup.map (preimage V).toSubgroup V.toSubgroup (↑f) _)
              ((chapter07OpenProfiniteCompletionProjection G (preimage V)) x)) =
          (QuotientGroup.map (preimage W).toSubgroup W.toSubgroup (↑f) _)
            ((chapter07OpenProfiniteCompletionProjection G (preimage W)) x)
      have hPQsub : (preimage V).toSubgroup ≤ (preimage W).toSubgroup := by
        dsimp [preimage]
        exact Subgroup.comap_mono hVWsub
      let k : preimage V ⟶ preimage W := ⟨⟨hPQsub⟩⟩
      have hnat :=
        (ProfiniteGrp.limitCone
          (chapter07OpenFiniteIndexProfiniteDiagram G)).π.naturality k
      have hnat' := congrArg (fun m => (ProfiniteGrp.Hom.hom m) x) hnat.symm
      have hproj :
          (QuotientGroup.map (preimage V).toSubgroup (preimage W).toSubgroup
              (MonoidHom.id G) (by
                intro g hg
                exact Subgroup.mem_comap.mpr (by simpa using hPQsub hg)))
              ((chapter07OpenProfiniteCompletionProjection G (preimage V)) x) =
            (chapter07OpenProfiniteCompletionProjection G (preimage W)) x := by
        change
          (QuotientGroup.map (preimage V).toSubgroup (preimage W).toSubgroup
              (MonoidHom.id G) (by
                intro g hg
                exact Subgroup.mem_comap.mpr (by simpa using hPQsub hg)))
              ((chapter07OpenProfiniteCompletionProjection G (preimage V)) x) =
            (chapter07OpenProfiniteCompletionProjection G (preimage W)) x at hnat'
        exact hnat'
      have hqV :
          (preimage V).toSubgroup ≤
            Subgroup.comap (↑f : G →* H) V.toSubgroup := by
        intro g hg
        dsimp [preimage] at hg
        exact hg
      have hqW :
          (preimage W).toSubgroup ≤
            Subgroup.comap (↑f : G →* H) W.toSubgroup := by
        intro g hg
        dsimp [preimage] at hg
        exact hg
      have hVWid : V.toSubgroup ≤ Subgroup.comap (MonoidHom.id H) W.toSubgroup := by
        intro g hg
        exact Subgroup.mem_comap.mpr (by simpa using hVWsub hg)
      have hPQid :
          (preimage V).toSubgroup ≤
            Subgroup.comap (MonoidHom.id G) (preimage W).toSubgroup := by
        intro g hg
        exact Subgroup.mem_comap.mpr (by simpa using hPQsub hg)
      have hcomp :
          (preimage V).toSubgroup ≤
            Subgroup.comap ((↑f : G →* H).comp (MonoidHom.id G)) W.toSubgroup := by
        intro g hg
        have hgQ : g ∈ (preimage W).toSubgroup := hPQsub hg
        dsimp [preimage] at hgQ
        exact Subgroup.mem_comap.mpr (by
          simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using
            (Subgroup.mem_comap.mp hgQ))
      have hcomp1 :
          (preimage V).toSubgroup ≤
            Subgroup.comap ((MonoidHom.id H).comp (↑f : G →* H)) W.toSubgroup := by
        simpa only [MonoidHom.id_comp, MonoidHom.comp_id] using hcomp
      have hqVW :
          (preimage V).toSubgroup ≤ Subgroup.comap (↑f : G →* H) W.toSubgroup := by
        simpa only [MonoidHom.comp_id] using hcomp
      calc
        _ = (QuotientGroup.map (preimage V).toSubgroup W.toSubgroup (↑f) hqVW)
              ((chapter07OpenProfiniteCompletionProjection G (preimage V)) x) := by
          simpa only [MonoidHom.id_comp] using
            (QuotientGroup.map_map (preimage V).toSubgroup V.toSubgroup W.toSubgroup
              (↑f) (MonoidHom.id H) hqV hVWid hcomp1
              ((chapter07OpenProfiniteCompletionProjection G (preimage V)) x))
        _ = (QuotientGroup.map (preimage W).toSubgroup W.toSubgroup (↑f) hqW)
              ((QuotientGroup.map (preimage V).toSubgroup (preimage W).toSubgroup
                (MonoidHom.id G) hPQid)
                ((chapter07OpenProfiniteCompletionProjection G (preimage V)) x)) := by
          simpa only [MonoidHom.comp_id] using
            (QuotientGroup.map_map (preimage V).toSubgroup (preimage W).toSubgroup
              W.toSubgroup (MonoidHom.id G) (↑f) hPQid hqW hcomp
              ((chapter07OpenProfiniteCompletionProjection G (preimage V)) x)).symm
        _ = _ := by rw [hproj]
      ⟩
  refine
    { toFun := phi
      map_one' := by
        apply ProfiniteGrp.limit_ext _
        intro V
        dsimp [phi]
        change (component V) 1 = 1
        exact map_one (component V)
      map_mul' := by
        intro x y
        apply ProfiniteGrp.limit_ext _
        intro V
        dsimp [phi]
        change (component V) (x * y) = (component V) x * (component V) y
        exact map_mul (component V) x y
      continuous_toFun := by
        apply Continuous.subtype_mk
        refine continuous_pi
          (T := fun V =>
            ((chapter07OpenFiniteIndexProfiniteDiagram H).obj V).toProfinite.toTop.str)
          (fun V ↦ ?_)
        let P := preimage V
        let hdisc : DiscreteTopology
            (G ⧸ P.toFiniteIndexNormalSubgroup.toSubgroup) :=
          QuotientGroup.discreteTopology_iff.mpr P.isOpen
        let hdiscH : DiscreteTopology
            (H ⧸ V.toFiniteIndexNormalSubgroup.toSubgroup) :=
          QuotientGroup.discreteTopology_iff.mpr V.isOpen
        have htopH :
            ((chapter07OpenFiniteIndexProfiniteDiagram H).obj V).toProfinite.toTop.str =
              (inferInstance : TopologicalSpace
                (H ⧸ V.toFiniteIndexNormalSubgroup.toSubgroup)) := by
          change (⊥ : TopologicalSpace
              (H ⧸ V.toFiniteIndexNormalSubgroup.toSubgroup)) =
            QuotientGroup.instTopologicalSpace
              V.toFiniteIndexNormalSubgroup.toSubgroup
          exact hdiscH.eq_bot.symm
        rw [htopH]
        have htop :
            ((chapter07OpenFiniteIndexProfiniteDiagram G).obj P).toProfinite.toTop.str =
              (inferInstance : TopologicalSpace
                (G ⧸ P.toFiniteIndexNormalSubgroup.toSubgroup)) := by
          change (⊥ : TopologicalSpace
              (G ⧸ P.toFiniteIndexNormalSubgroup.toSubgroup)) =
            QuotientGroup.instTopologicalSpace
              P.toFiniteIndexNormalSubgroup.toSubgroup
          exact hdisc.eq_bot.symm
        let hdiscObj :
            DiscreteTopology
              (↑((chapter07OpenFiniteIndexProfiniteDiagram G).obj P).toProfinite.toTop) := by
          constructor
          rw [htop]
          exact hdisc.eq_bot
        dsimp [component, preimage]
        let q : (↑((chapter07OpenFiniteIndexProfiniteDiagram G).obj P).toProfinite.toTop) →
            (H ⧸ V.toFiniteIndexNormalSubgroup.toSubgroup) :=
          QuotientGroup.map _ _ (↑f) (by
            intro g hg
            dsimp [P, preimage] at hg
            exact hg)
        have hq : Continuous q :=
          @continuous_of_discreteTopology
            (↑((chapter07OpenFiniteIndexProfiniteDiagram G).obj P).toProfinite.toTop) _ hdiscObj
            (H ⧸ V.toFiniteIndexNormalSubgroup.toSubgroup) _ q
        exact
          hq.comp
            ((ProfiniteGrp.limitCone
              (chapter07OpenFiniteIndexProfiniteDiagram G)).π.app P).hom.continuous_toFun }

private theorem chapter07_open_completion_lift_eta
    {G H : Type*} [CommGroup G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (f : G →ₜ* H) (g : G) :
    chapter07_open_completion_lift f
        (chapter07OpenProfiniteCompletionEta G g) =
      chapter07OpenProfiniteCompletionEta H (f g) := by
  apply ProfiniteGrp.limit_ext _
  intro V
  dsimp [chapter07_open_completion_lift]
  rfl

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
  classical
  let d : Kˣ →ₜ* (Multiplicative ℤ × U) :=
    { toMonoidHom := D.decomposition.toMonoidHom
      continuous_toFun := D.decomposition_continuous }
  let dinv : (Multiplicative ℤ × U) →ₜ* Kˣ :=
    { toMonoidHom := D.decomposition.symm.toMonoidHom
      continuous_toFun := D.decomposition_symm_continuous }
  let fz : Kˣ →ₜ* Multiplicative ℤ :=
    (ContinuousMonoidHom.fst (Multiplicative ℤ) U).comp d
  let fu : Kˣ →ₜ* U :=
    (ContinuousMonoidHom.snd (Multiplicative ℤ) U).comp d
  let bz : Multiplicative ℤ →ₜ* Kˣ :=
    dinv.comp (ContinuousMonoidHom.inl (Multiplicative ℤ) U)
  let bu : U →ₜ* Kˣ :=
    dinv.comp (ContinuousMonoidHom.inr (Multiplicative ℤ) U)
  let Fz : Chapter07OpenProfiniteCompletion Kˣ →ₜ*
      Chapter07OpenProfiniteCompletion (Multiplicative ℤ) :=
    chapter07_open_completion_lift fz
  let Fu : Chapter07OpenProfiniteCompletion Kˣ →ₜ*
      Chapter07OpenProfiniteCompletion U :=
    chapter07_open_completion_lift fu
  let Bz : Chapter07OpenProfiniteCompletion (Multiplicative ℤ) →ₜ*
      Chapter07OpenProfiniteCompletion Kˣ :=
    chapter07_open_completion_lift bz
  let Bu : Chapter07OpenProfiniteCompletion U →ₜ*
      Chapter07OpenProfiniteCompletion Kˣ :=
    chapter07_open_completion_lift bu
  let A : Chapter07OpenProfiniteCompletion Kˣ →ₜ*
      Chapter07ProfiniteIntegers × Chapter07OpenProfiniteCompletion U :=
    Fz.prod Fu
  have hcomm :
      (fun p : Chapter07ProfiniteIntegers ×
          Chapter07OpenProfiniteCompletion U => Bz p.1 * Bu p.2) =
        (fun p => Bu p.2 * Bz p.1) := by
    apply DenseRange.equalizer
      ((chapter07_open_profinite_completion_eta_dense
          (G := Multiplicative ℤ)).prodMap
        (chapter07_open_profinite_completion_eta_dense (G := U)))
    · exact (Bz.continuous_toFun.comp continuous_fst).mul
        (Bu.continuous_toFun.comp continuous_snd)
    · exact (Bu.continuous_toFun.comp continuous_snd).mul
        (Bz.continuous_toFun.comp continuous_fst)
    · funext p
      rcases p with ⟨z, u⟩
      change Bz (chapter07OpenProfiniteCompletionEta
          (Multiplicative ℤ) z) * Bu (chapter07OpenProfiniteCompletionEta U u) =
        Bu (chapter07OpenProfiniteCompletionEta U u) * Bz
          (chapter07OpenProfiniteCompletionEta (Multiplicative ℤ) z)
      rw [chapter07_open_completion_lift_eta bz z,
        chapter07_open_completion_lift_eta bu u]
      rw [← map_mul, ← map_mul]
      congr 1
      dsimp [bz, bu, dinv]
      change D.decomposition.symm (z, 1) * D.decomposition.symm (1, u) =
        D.decomposition.symm (1, u) * D.decomposition.symm (z, 1)
      rw [← D.decomposition.symm.map_mul, ← D.decomposition.symm.map_mul]
      simp [mul_comm]
  let B : Chapter07ProfiniteIntegers × Chapter07OpenProfiniteCompletion U →ₜ*
      Chapter07OpenProfiniteCompletion Kˣ :=
    { toFun := fun p => Bz p.1 * Bu p.2
      map_one' := by simp
      map_mul' := by
        intro p q
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        have hpq : Bz q.1 * Bu p.2 = Bu p.2 * Bz q.1 := by
          exact congrFun hcomm (q.1, p.2)
        calc
          (Bz p.1 * Bz q.1) * (Bu p.2 * Bu q.2) =
              Bz p.1 * (Bz q.1 * (Bu p.2 * Bu q.2)) := by rw [mul_assoc]
          _ = Bz p.1 * (Bu p.2 * (Bz q.1 * Bu q.2)) := by
            congr 1
            rw [← mul_assoc, hpq, mul_assoc]
          _ = (Bz p.1 * Bu p.2) * (Bz q.1 * Bu q.2) := by rw [mul_assoc]
      continuous_toFun :=
        (Bz.continuous_toFun.comp continuous_fst).mul
          (Bu.continuous_toFun.comp continuous_snd) }
  have hcoord (x : Kˣ) : bz (fz x) * bu (fu x) = x := by
    dsimp [bz, bu, fz, fu, d, dinv]
    change D.decomposition.symm ((D.decomposition x).1, 1) *
      D.decomposition.symm (1, (D.decomposition x).2) = x
    rw [← D.decomposition.symm.map_mul]
    have hprod :
        ((D.decomposition x).1, 1) * (1, (D.decomposition x).2) =
          D.decomposition x := by
      apply Prod.ext <;> simp
    rw [hprod]
    exact D.decomposition.symm_apply_apply x
  have hBA : B.comp A = ContinuousMonoidHom.id _ := by
    apply ContinuousMonoidHom.ext
    intro x
    have hfun :
        (fun y => B (A y)) =
          (fun y : Chapter07OpenProfiniteCompletion Kˣ => y) := by
      apply DenseRange.equalizer
        (chapter07_open_profinite_completion_eta_dense (G := Kˣ))
      · exact B.continuous_toFun.comp A.continuous_toFun
      · exact continuous_id
      · funext y
        change Bz (Fz (chapter07OpenProfiniteCompletionEta Kˣ y)) *
          Bu (Fu (chapter07OpenProfiniteCompletionEta Kˣ y)) =
            chapter07OpenProfiniteCompletionEta Kˣ y
        rw [chapter07_open_completion_lift_eta fz y,
          chapter07_open_completion_lift_eta fu y,
          chapter07_open_completion_lift_eta bz,
          chapter07_open_completion_lift_eta bu]
        rw [← map_mul]
        exact congrArg (chapter07OpenProfiniteCompletionEta Kˣ) (hcoord y)
    exact congrFun hfun x
  have hfst (z : Chapter07OpenProfiniteCompletion (Multiplicative ℤ)) :
      Fz (Bz z) = z := by
    have hmap : Fz.comp Bz = ContinuousMonoidHom.id _ := by
      apply ContinuousMonoidHom.ext
      intro z
      have hfun :
          (fun x => Fz (Bz x)) =
            (fun x : Chapter07OpenProfiniteCompletion (Multiplicative ℤ) => x) := by
        apply DenseRange.equalizer
          (chapter07_open_profinite_completion_eta_dense
            (G := Multiplicative ℤ))
        · exact Fz.continuous_toFun.comp Bz.continuous_toFun
        · exact continuous_id
        · funext x
          change Fz (Bz (chapter07OpenProfiniteCompletionEta
            (Multiplicative ℤ) x)) =
            chapter07OpenProfiniteCompletionEta (Multiplicative ℤ) x
          rw [chapter07_open_completion_lift_eta bz x,
            chapter07_open_completion_lift_eta fz]
          congr 1
          dsimp [fz, bz, d, dinv]
          change (D.decomposition (D.decomposition.symm (x, 1))).1 = x
          rw [D.decomposition.apply_symm_apply]
      exact congrFun hfun z
    have h := congrArg (fun f :
        Chapter07OpenProfiniteCompletion (Multiplicative ℤ) →ₜ*
          Chapter07OpenProfiniteCompletion (Multiplicative ℤ) => f z) hmap
    exact h
  have hFzBu (u : Chapter07OpenProfiniteCompletion U) :
      Fz (Bu u) = 1 := by
    have hmap : Fz.comp Bu = (1 :
        Chapter07OpenProfiniteCompletion U →ₜ*
          Chapter07OpenProfiniteCompletion (Multiplicative ℤ)) := by
      apply ContinuousMonoidHom.ext
      intro u
      have hfun :
          (fun x => Fz (Bu x)) =
            (fun _ : Chapter07OpenProfiniteCompletion U =>
              (1 : Chapter07OpenProfiniteCompletion (Multiplicative ℤ))) := by
        apply DenseRange.equalizer
          (chapter07_open_profinite_completion_eta_dense (G := U))
        · exact Fz.continuous_toFun.comp Bu.continuous_toFun
        · exact continuous_const
        · funext x
          change Fz (Bu (chapter07OpenProfiniteCompletionEta U x)) = 1
          rw [chapter07_open_completion_lift_eta bu x,
            chapter07_open_completion_lift_eta fz]
          change chapter07OpenProfiniteCompletionEta (Multiplicative ℤ)
            (fz (bu x)) = 1
          rw [show fz (bu x) = 1 by
            dsimp [fz, bu, d, dinv]
            change (D.decomposition (D.decomposition.symm (1, x))).1 = 1
            rw [D.decomposition.apply_symm_apply]]
          rfl
      exact congrFun hfun u
    have h := congrArg (fun f :
        Chapter07OpenProfiniteCompletion U →ₜ*
          Chapter07OpenProfiniteCompletion (Multiplicative ℤ) => f u) hmap
    exact h
  have hFuBz (z : Chapter07OpenProfiniteCompletion (Multiplicative ℤ)) :
      Fu (Bz z) = 1 := by
    have hmap : Fu.comp Bz = (1 :
        Chapter07OpenProfiniteCompletion (Multiplicative ℤ) →ₜ*
          Chapter07OpenProfiniteCompletion U) := by
      apply ContinuousMonoidHom.ext
      intro z
      have hfun :
          (fun x => Fu (Bz x)) =
            (fun _ : Chapter07OpenProfiniteCompletion (Multiplicative ℤ) =>
              (1 : Chapter07OpenProfiniteCompletion U)) := by
        apply DenseRange.equalizer
          (chapter07_open_profinite_completion_eta_dense
            (G := Multiplicative ℤ))
        · exact Fu.continuous_toFun.comp Bz.continuous_toFun
        · exact continuous_const
        · funext x
          change Fu (Bz (chapter07OpenProfiniteCompletionEta
            (Multiplicative ℤ) x)) = 1
          rw [chapter07_open_completion_lift_eta bz x,
            chapter07_open_completion_lift_eta fu]
          change chapter07OpenProfiniteCompletionEta U (fu (bz x)) = 1
          rw [show fu (bz x) = 1 by
            dsimp [fu, bz, d, dinv]
            change (D.decomposition (D.decomposition.symm (x, 1))).2 = 1
            rw [D.decomposition.apply_symm_apply]]
          rfl
      exact congrFun hfun z
    have h := congrArg (fun f :
        Chapter07OpenProfiniteCompletion (Multiplicative ℤ) →ₜ*
          Chapter07OpenProfiniteCompletion U => f z) hmap
    exact h
  have hFuBu (u : Chapter07OpenProfiniteCompletion U) :
      Fu (Bu u) = u := by
    have hmap : Fu.comp Bu = ContinuousMonoidHom.id _ := by
      apply ContinuousMonoidHom.ext
      intro u
      have hfun :
          (fun x => Fu (Bu x)) =
            (fun x : Chapter07OpenProfiniteCompletion U => x) := by
        apply DenseRange.equalizer
          (chapter07_open_profinite_completion_eta_dense (G := U))
        · exact Fu.continuous_toFun.comp Bu.continuous_toFun
        · exact continuous_id
        · funext x
          change Fu (Bu (chapter07OpenProfiniteCompletionEta U x)) =
            chapter07OpenProfiniteCompletionEta U x
          rw [chapter07_open_completion_lift_eta bu x,
            chapter07_open_completion_lift_eta fu]
          change chapter07OpenProfiniteCompletionEta U (fu (bu x)) =
            chapter07OpenProfiniteCompletionEta U x
          congr 1
          dsimp [fu, bu, d, dinv]
          change (D.decomposition (D.decomposition.symm (1, x))).2 = x
          rw [D.decomposition.apply_symm_apply]
      exact congrFun hfun u
    have h := congrArg (fun f :
        Chapter07OpenProfiniteCompletion U →ₜ*
          Chapter07OpenProfiniteCompletion U => f u) hmap
    exact h
  have hAB : A.comp B = ContinuousMonoidHom.id _ := by
    apply ContinuousMonoidHom.ext
    intro p
    change (Fz (Bz p.1 * Bu p.2), Fu (Bz p.1 * Bu p.2)) = p
    apply Prod.ext
    · rw [map_mul, hfst, hFzBu]
      simp
    · change Fu (Bz p.1 * Bu p.2) = p.2
      rw [map_mul, hFuBz, hFuBu]
      simp
  let e0 : Chapter07OpenProfiniteCompletion Kˣ ≃*
      Chapter07ProfiniteIntegers × Chapter07OpenProfiniteCompletion U :=
    { toFun := A
      invFun := B
      left_inv := by
        intro x
        have h := congrArg (fun f :
            Chapter07OpenProfiniteCompletion Kˣ →ₜ*
              Chapter07OpenProfiniteCompletion Kˣ => f x) hBA
        exact h
      right_inv := by
        intro p
        have h := congrArg (fun f :
            (Chapter07ProfiniteIntegers × Chapter07OpenProfiniteCompletion U) →ₜ*
              (Chapter07ProfiniteIntegers × Chapter07OpenProfiniteCompletion U) => f p) hAB
        exact h
      map_mul' := by
        intro x y
        exact A.map_mul x y }
  let e0Top : Chapter07OpenProfiniteCompletion Kˣ ≃ₜ*
      Chapter07ProfiniteIntegers × Chapter07OpenProfiniteCompletion U :=
    ContinuousMulEquiv.mk e0 A.continuous_toFun B.continuous_toFun
  let uEquiv : Chapter07OpenProfiniteCompletion U ≃ₜ* U :=
    Classical.choice D.unitsAlreadyProfinite
  let eprod :
      (Chapter07ProfiniteIntegers × Chapter07OpenProfiniteCompletion U) ≃ₜ*
        (Chapter07ProfiniteIntegers × U) :=
    ContinuousMulEquiv.mk
      (MulEquiv.prodCongr (MulEquiv.refl _) uEquiv.toMulEquiv)
      (continuous_fst.prodMk (uEquiv.continuous_toFun.comp continuous_snd))
      (continuous_fst.prodMk (uEquiv.continuous_invFun.comp continuous_snd))
  exact ⟨e0Top.trans eprod⟩

/-- Distinct normalized uniformizers give distinct splittings, recording the
noncanonical nature of the product decomposition. -/
theorem chapter07_uniformizer_split_depends_on_choice
    {K : Type*} [Field K] [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    {U : Type*} [CommGroup U]
    [TopologicalSpace U] [IsTopologicalGroup U]
    (D₁ D₂ : Chapter07UniformizerUnitDecomposition K U)
    (huniformizer : D₁.uniformizer ≠ D₂.uniformizer) :
    D₁.decomposition ≠ D₂.decomposition := by
  intro hdecomposition
  apply huniformizer
  apply D₂.decomposition.injective
  calc
    D₂.decomposition D₁.uniformizer = D₁.decomposition D₁.uniformizer := by
      rw [hdecomposition]
    _ = (Multiplicative.ofAdd 1, 1) := D₁.uniformizer_coordinate
    _ = D₂.decomposition D₂.uniformizer := D₂.uniformizer_coordinate.symm

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
