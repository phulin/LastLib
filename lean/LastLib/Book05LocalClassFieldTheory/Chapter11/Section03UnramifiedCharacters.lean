import LastLib.Book05LocalClassFieldTheory.Chapter11.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter11.Section01ExactTopologicalStatement

namespace LastLib.Book05LocalClassFieldTheory.Chapter11

noncomputable section

open scoped Topology

/-! ## 11.3. Unramified characters -/

def chapter11IsUnramified
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) : Prop :=
  ∀ u : D.unitGroup, χ (u : Kˣ) = 1

def chapter11IsRamified
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) : Prop :=
  ¬ chapter11IsUnramified D χ

def chapter11IsTamelyRamified
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) : Prop :=
  (∀ x ∈ D.unitFiltration 1, χ x = 1) ∧
    chapter11IsRamified D χ

def chapter11IsWildlyRamified
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) : Prop :=
  ¬ ∀ x ∈ D.unitFiltration 1, χ x = 1

def chapter11UnramifiedCharacterOfValue
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (α : A) : Kˣ →ₜ* A :=
  chapter11CharacterOfPair D α (1 : D.unitGroup →ₜ* A)

theorem chapter11_unramified_character_iff_pair
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A) :
    chapter11IsUnramified D χ ↔
      χ = chapter11UnramifiedCharacterOfValue D (χ D.uniformizer) := by
  constructor
  · intro hχ
    have hunit :
        χ.comp (chapter11UnitInclusion D) = (1 : D.unitGroup →ₜ* A) := by
      ext u
      exact hχ u
    have hpair := (chapter11CharacterPairEquiv D).left_inv χ
    change χ = chapter11CharacterOfPair D (χ D.uniformizer)
      (1 : D.unitGroup →ₜ* A)
    calc
      χ = chapter11CharacterOfPair D (χ D.uniformizer)
          (χ.comp (chapter11UnitInclusion D)) := hpair.symm
      _ = chapter11CharacterOfPair D (χ D.uniformizer)
          (1 : D.unitGroup →ₜ* A) := by rw [hunit]
  · intro hχ u
    rw [hχ]
    change chapter11CharacterOfPair D (χ D.uniformizer)
      (1 : D.unitGroup →ₜ* A) (u : Kˣ) = 1
    have h :=
      chapter11_character_of_pair_apply_decomposition D (χ D.uniformizer)
        (1 : D.unitGroup →ₜ* A) 0 u
    simpa using h

theorem chapter11_unramified_character_determined_by_uniformizer
    {K A : Type*} [Field K] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace A] [IsTopologicalGroup A]
    (D : Chapter11LocalFieldData K) (χ : Kˣ →ₜ* A)
    (hχ : chapter11IsUnramified D χ) :
    ∀ x : Kˣ, χ x = (χ D.uniformizer) ^ Multiplicative.toAdd (D.valuation x) := by
  intro x
  let p := D.decomposition.symm x
  have hx : x = D.uniformizer ^ p.1.toAdd * (p.2 : Kˣ) := by
    rw [← D.decomposition_apply p.1 p.2]
    exact (D.decomposition.apply_symm_apply x).symm
  have hv : D.valuation x = Multiplicative.ofAdd p.1.toAdd := by
    have hpow2 : Multiplicative.ofAdd (1 : ℤ) ^ p.1.toAdd =
        Multiplicative.ofAdd p.1.toAdd := by
      rw [← ofAdd_zsmul, zsmul_one]
      rfl
    rw [hx, map_mul, map_zpow, D.valuation_uniformizer, D.valuation_unit]
    calc
      Multiplicative.ofAdd (1 : ℤ) ^ p.1.toAdd * Multiplicative.ofAdd (0 : ℤ) =
          Multiplicative.ofAdd p.1.toAdd * Multiplicative.ofAdd (0 : ℤ) := by
        rw [hpow2]
      _ = Multiplicative.ofAdd p.1.toAdd := by simp
  calc
    χ x = χ (D.uniformizer ^ p.1.toAdd * (p.2 : Kˣ)) := by rw [hx]
    _ = χ D.uniformizer ^ p.1.toAdd := by
      rw [map_mul, map_zpow, hχ p.2]
      simp
    _ = χ D.uniformizer ^ Multiplicative.toAdd (D.valuation x) := by
      rw [hv]
      rfl

def chapter11CorrespondingAbelianGaloisCharacter
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (R : Chapter11ReciprocityData K G) (χ : Kˣ →ₜ* A) :
    TopologicalAbelianization G →ₜ* A :=
  (chapter11AbelianContinuousCharacterEquiv R).symm χ

theorem chapter11_unramified_character_trivial_on_inertia
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11FrobeniusData K G D R) (χ : Kˣ →ₜ* A)
    (hχ : chapter11IsUnramified D χ) :
    ∀ g : F.inertia,
      chapter11CorrespondingAbelianGaloisCharacter R χ
        ((chapter11AbelianizationMap G) (g : G)) = 1 := by
  intro g
  have hgimage :
      (chapter11AbelianizationMap G) (g : G) ∈
        D.unitGroup.map R.reciprocity.toMonoidHom := by
    rw [← F.inertia_ab_eq_reciprocity_unit_image]
    exact ⟨g, g.property, rfl⟩
  rcases hgimage with ⟨u, hu, hgu⟩
  have hrec :
      chapter11CorrespondingAbelianGaloisCharacter R χ (R.reciprocity u) = χ u := by
    have hcomp := chapter11_abelian_continuous_character_equiv_apply R
      (chapter11CorrespondingAbelianGaloisCharacter R χ)
    have heq :
        (chapter11CorrespondingAbelianGaloisCharacter R χ).comp R.reciprocity = χ := by
      calc
        _ = (chapter11AbelianContinuousCharacterEquiv R)
            (chapter11CorrespondingAbelianGaloisCharacter R χ) := hcomp.symm
        _ = χ := (chapter11AbelianContinuousCharacterEquiv R).apply_symm_apply χ
    exact congrArg (fun ψ : Kˣ →ₜ* A => ψ u) heq
  calc
    (chapter11CorrespondingAbelianGaloisCharacter R χ)
        ((chapter11AbelianizationMap G) (g : G)) =
        (chapter11CorrespondingAbelianGaloisCharacter R χ)
          (R.reciprocity.toMonoidHom u) := by rw [hgu]
    _ = (chapter11CorrespondingAbelianGaloisCharacter R χ) (R.reciprocity u) := rfl
    _ = χ u := hrec
    _ = 1 := hχ ⟨u, hu⟩

theorem chapter11_unramified_character_sends_arithmetic_frobenius_to_parameter
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11FrobeniusData K G D R) (χ : Kˣ →ₜ* A)
    (hχ : chapter11IsUnramified D χ) :
    chapter11CorrespondingAbelianGaloisCharacter R χ F.arithmeticFrobenius =
      χ D.uniformizer := by
  have _hχ : chapter11IsUnramified D χ := hχ
  have heq :
      (chapter11CorrespondingAbelianGaloisCharacter R χ).comp R.reciprocity = χ := by
    have hcomp := chapter11_abelian_continuous_character_equiv_apply R
      (chapter11CorrespondingAbelianGaloisCharacter R χ)
    calc
      _ = (chapter11AbelianContinuousCharacterEquiv R)
          (chapter11CorrespondingAbelianGaloisCharacter R χ) := hcomp.symm
      _ = χ := (chapter11AbelianContinuousCharacterEquiv R).apply_symm_apply χ
  calc
    (chapter11CorrespondingAbelianGaloisCharacter R χ) F.arithmeticFrobenius =
        (chapter11CorrespondingAbelianGaloisCharacter R χ)
          (R.reciprocity D.uniformizer) := by rw [F.reciprocity_uniformizer]
    _ = χ D.uniformizer := congrArg (fun ψ : Kˣ →ₜ* A => ψ D.uniformizer) heq

def chapter11GeometricFrobenius
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (F : TopologicalAbelianization G) :
    TopologicalAbelianization G := F⁻¹

theorem chapter11_geometric_frobenius_normalization
    {K G A : Type*} [Field K] [Group G] [CommGroup A]
    [TopologicalSpace Kˣ] [TopologicalSpace G] [TopologicalSpace A]
    [IsTopologicalGroup G] [IsTopologicalGroup A] [T2Space A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (D : Chapter11LocalFieldData K) (R : Chapter11ReciprocityData K G)
    (F : Chapter11FrobeniusData K G D R) (χ : Kˣ →ₜ* A)
    (hχ : chapter11IsUnramified D χ) :
    chapter11CorrespondingAbelianGaloisCharacter R χ
        (chapter11GeometricFrobenius F.arithmeticFrobenius) =
      (χ D.uniformizer)⁻¹ := by
  rw [chapter11GeometricFrobenius, map_inv,
    chapter11_unramified_character_sends_arithmetic_frobenius_to_parameter D R F χ hχ]

/- The closure, rather than the raw subgroup of integer powers, is the compact
  procyclic object used for profinite extension. -/
def chapter11CompactProcyclicClosure
    {A : Type*} [CommGroup A] [TopologicalSpace A] (α : A) : Set A :=
  closure (Subgroup.zpowers α : Set A)

theorem chapter11_profinite_parameter_has_compact_procyclic_closure
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    [CompactSpace A]
    (α : A) :
    IsCompact (chapter11CompactProcyclicClosure α) := by
  exact IsCompact.of_isClosed_subset (isCompact_univ : IsCompact (Set.univ : Set A))
    isClosed_closure (Set.subset_univ _)

/- The closure is not merely a compact set: in a topological group it is the
   canonical closed subgroup generated by the parameter. -/
def chapter11CompactProcyclicSubgroup
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] (α : A) : Subgroup A :=
  Subgroup.topologicalClosure (Subgroup.zpowers α)

theorem chapter11_compact_procyclic_subgroup_coe
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] (α : A) :
    (chapter11CompactProcyclicSubgroup α : Set A) =
      chapter11CompactProcyclicClosure α := by
  rfl

theorem chapter11_unramified_parameter_extends_to_profinite_integer_power
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [CompactSpace A]
    [TotallyDisconnectedSpace A]
    (α : A) :
    ∃ F : Chapter11ProfiniteCompletion (Multiplicative ℤ) →ₜ* A,
      ∀ n : ℤ,
        F (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
          (Multiplicative ℤ) (Multiplicative.ofAdd n)) = α ^ n := by
  let f : Multiplicative ℤ →ₜ* A :=
    { toFun := fun n => α ^ n.toAdd
      map_one' := by simp
      map_mul' := by
        intro m n
        simp [zpow_add]
      continuous_toFun := continuous_of_discreteTopology }
  let preimage (V : OpenNormalSubgroup A) :
      LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenFiniteIndexNormalSubgroup
        (Multiplicative ℤ) := by
    let Psub : Subgroup (Multiplicative ℤ) :=
      V.toFiniteIndexNormalSubgroup.toSubgroup.comap
        (↑f : Multiplicative ℤ →* A)
    let Pfin : FiniteIndexNormalSubgroup (Multiplicative ℤ) :=
      { toSubgroup := Psub
        isNormal' := by
          dsimp [Psub]
          infer_instance
        isFiniteIndex' := by
          dsimp [Psub]
          rw [← FiniteIndexNormalSubgroup.toSubgroup_comap
            (↑f : Multiplicative ℤ →* A) V.toFiniteIndexNormalSubgroup]
          infer_instance }
    refine { toFiniteIndexNormalSubgroup := Pfin, isOpen := ?_ }
    dsimp [Pfin, Psub]
    exact V.isOpen.preimage f.continuous_toFun
  let componentO (V : OpenNormalSubgroup A) :
      LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion
          (Multiplicative ℤ) →* (A ⧸ V.toSubgroup) :=
    let P := preimage V
    let q : ((Multiplicative ℤ) ⧸ P.toSubgroup) →* (A ⧸ V.toSubgroup) :=
      QuotientGroup.map _ _ (↑f) (by
        intro g hg
        dsimp [P, preimage] at hg
        exact hg)
    q.comp
      (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
        (Multiplicative ℤ) P)
  have hcomponentO (V : OpenNormalSubgroup A) :
      Continuous (componentO V) := by
    let P := preimage V
    let hdisc : DiscreteTopology
        (Multiplicative ℤ ⧸ P.toSubgroup) :=
      QuotientGroup.discreteTopology_iff.mpr P.isOpen
    have htop :
        ((LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenFiniteIndexProfiniteDiagram
          (Multiplicative ℤ)).obj P).toProfinite.toTop.str =
          (inferInstance : TopologicalSpace
            (Multiplicative ℤ ⧸ P.toSubgroup)) := by
      change (⊥ : TopologicalSpace (Multiplicative ℤ ⧸ P.toSubgroup)) =
        QuotientGroup.instTopologicalSpace P.toSubgroup
      exact hdisc.eq_bot.symm
    let hdiscObj :
        DiscreteTopology
          (↑((LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenFiniteIndexProfiniteDiagram
            (Multiplicative ℤ)).obj P).toProfinite.toTop) := by
      constructor
      rw [htop]
      exact hdisc.eq_bot
    dsimp [componentO, preimage]
    let q :
        (↑((LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenFiniteIndexProfiniteDiagram
          (Multiplicative ℤ)).obj P).toProfinite.toTop) →
          (A ⧸ V.toSubgroup) :=
      QuotientGroup.map _ _ (↑f) (by
        intro g hg
        dsimp [P, preimage] at hg
        exact hg)
    have hq : Continuous q :=
      @continuous_of_discreteTopology
        (↑((LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenFiniteIndexProfiniteDiagram
          (Multiplicative ℤ)).obj P).toProfinite.toTop) _ hdiscObj
        (A ⧸ V.toSubgroup) _ q
    exact
      hq.comp
        ((ProfiniteGrp.limitCone
          (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenFiniteIndexProfiniteDiagram
            (Multiplicative ℤ))).π.app P).hom.continuous_toFun
  let htdSource : TotallyDisconnectedSpace
      (LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion
        (Multiplicative ℤ)) :=
    (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletion
      (Multiplicative ℤ)).toProfinite.prop
  let htdUp : TotallyDisconnectedSpace
      (ULift
        (LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion
          (Multiplicative ℤ))) :=
    @Homeomorph.totallyDisconnectedSpace
      (LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion
        (Multiplicative ℤ))
      (ULift
        (LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion
          (Multiplicative ℤ))) _ _
      Homeomorph.ulift.symm htdSource
  let _ := htdUp
  have htopV (V : OpenNormalSubgroup A) :
      ((ProfiniteGrp.diagram (ProfiniteGrp.of A)).obj V).toProfinite.toTop.str =
        (inferInstance : TopologicalSpace (A ⧸ V.toSubgroup)) := by
    let hdiscV : DiscreteTopology (A ⧸ V.toSubgroup) :=
      QuotientGroup.discreteTopology_iff.mpr V.isOpen
    change (⊥ : TopologicalSpace (A ⧸ V.toSubgroup)) =
      QuotientGroup.instTopologicalSpace V.toSubgroup
    exact hdiscV.eq_bot.symm
  let cone : CategoryTheory.Limits.Cone (ProfiniteGrp.diagram (ProfiniteGrp.of A)) :=
    { pt := ProfiniteGrp.of
        (ULift
          (LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion
            (Multiplicative ℤ)))
      π :=
        { app := fun V => ProfiniteGrp.ofHom
            (Y := (ProfiniteGrp.diagram (ProfiniteGrp.of A)).obj V)
            { toFun := fun x => componentO V x.down
              map_one' := by exact map_one (componentO V)
              map_mul' := by
                intro x y
                exact map_mul (componentO V) x.down y.down
              continuous_toFun := by
                rw [htopV V]
                exact (hcomponentO V).comp continuous_uliftDown }
          naturality := by
            intro V W g
            ext x
            dsimp
            have hVWsub : V.toSubgroup ≤ W.toSubgroup := g.le
            change
              componentO W x.down =
                QuotientGroup.map V.toSubgroup W.toSubgroup (MonoidHom.id A) (by
                  intro z hz
                  exact Subgroup.mem_comap.mpr (hVWsub hz))
                  (componentO V x.down)
            symm
            have hPQsub : (preimage V).toSubgroup ≤ (preimage W).toSubgroup := by
              dsimp [preimage]
              exact Subgroup.comap_mono hVWsub
            let k : preimage V ⟶ preimage W := ⟨⟨hPQsub⟩⟩
            have hnat :=
              (ProfiniteGrp.limitCone
                (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenFiniteIndexProfiniteDiagram
                  (Multiplicative ℤ))).π.naturality k
            have hnat' := congrArg (fun m => (ProfiniteGrp.Hom.hom m) x.down) hnat.symm
            have hproj :
                (QuotientGroup.map (preimage V).toSubgroup (preimage W).toSubgroup
                    (MonoidHom.id (Multiplicative ℤ)) (by
                      intro z hz
                      exact Subgroup.mem_comap.mpr (by simpa using hPQsub hz)))
                    ((LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
                      (Multiplicative ℤ) (preimage V)) x.down) =
                  (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
                    (Multiplicative ℤ) (preimage W)) x.down := by
              change
                (QuotientGroup.map (preimage V).toSubgroup (preimage W).toSubgroup
                    (MonoidHom.id (Multiplicative ℤ)) (by
                      intro z hz
                      exact Subgroup.mem_comap.mpr (by simpa using hPQsub hz)))
                    ((LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
                      (Multiplicative ℤ) (preimage V)) x.down) =
                  (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
                    (Multiplicative ℤ) (preimage W)) x.down at hnat'
              exact hnat'
            have hqV :
                (preimage V).toSubgroup ≤
                  Subgroup.comap (↑f : Multiplicative ℤ →* A) V.toSubgroup := by
              intro z hz
              dsimp [preimage] at hz
              exact hz
            have hqW :
                (preimage W).toSubgroup ≤
                  Subgroup.comap (↑f : Multiplicative ℤ →* A) W.toSubgroup := by
              intro z hz
              dsimp [preimage] at hz
              exact hz
            have hVWid :
                V.toSubgroup ≤ Subgroup.comap (MonoidHom.id A) W.toSubgroup := by
              intro z hz
              exact Subgroup.mem_comap.mpr (by simpa using hVWsub hz)
            have hPQid :
                (preimage V).toSubgroup ≤
                  Subgroup.comap (MonoidHom.id (Multiplicative ℤ))
                    (preimage W).toSubgroup := by
              intro z hz
              exact Subgroup.mem_comap.mpr (by simpa using hPQsub hz)
            have hsubW :
                W.toFiniteIndexNormalSubgroup.toSubgroup = W.toSubgroup := by
              rfl
            have hcomp :
                (preimage V).toSubgroup ≤
                  Subgroup.comap ((↑f : Multiplicative ℤ →* A).comp
                    (MonoidHom.id (Multiplicative ℤ))) W.toSubgroup := by
              intro z hz
              have hzQ : z ∈ (preimage W).toSubgroup := hPQsub hz
              dsimp [preimage] at hzQ
              exact Subgroup.mem_comap.mpr (by
                simpa only [MonoidHom.comp_apply, MonoidHom.id_apply, hsubW] using
                  (Subgroup.mem_comap.mp hzQ))
            have hcomp1 :
                (preimage V).toSubgroup ≤
                  Subgroup.comap ((MonoidHom.id A).comp
                    (↑f : Multiplicative ℤ →* A)) W.toSubgroup := by
              simpa only [MonoidHom.id_comp, MonoidHom.comp_id] using hcomp
            have hqVW :
                (preimage V).toSubgroup ≤
                  Subgroup.comap (↑f : Multiplicative ℤ →* A) W.toSubgroup := by
              simpa only [MonoidHom.comp_id] using hcomp
            calc
              _ = (QuotientGroup.map (preimage V).toSubgroup W.toSubgroup
                    (↑f) hqVW)
                  ((LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
                    (Multiplicative ℤ) (preimage V)) x.down) := by
                dsimp [componentO, preimage]
                simpa only [MonoidHom.id_comp] using
                  (QuotientGroup.map_map (preimage V).toSubgroup V.toSubgroup
                    W.toSubgroup (↑f) (MonoidHom.id A) hqV hVWid hcomp1
                    ((LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
                      (Multiplicative ℤ) (preimage V)) x.down))
              _ = (QuotientGroup.map (preimage W).toSubgroup W.toSubgroup
                    (↑f) hqW)
                  ((QuotientGroup.map (preimage V).toSubgroup
                    (preimage W).toSubgroup (MonoidHom.id (Multiplicative ℤ))
                    hPQid)
                    ((LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
                      (Multiplicative ℤ) (preimage V)) x.down)) := by
                simpa only [MonoidHom.comp_id] using
                  (QuotientGroup.map_map (preimage V).toSubgroup
                    (preimage W).toSubgroup W.toSubgroup
                    (MonoidHom.id (Multiplicative ℤ)) (↑f) hPQid hqW hcomp
                    ((LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
                      (Multiplicative ℤ) (preimage V)) x.down)).symm
              _ = _ := by
                rw [hproj]
                dsimp [componentO, preimage] } }
  let direct :
      ULift
          (LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion
            (Multiplicative ℤ)) →ₜ* A :=
    (ProfiniteGrp.isLimitCone (ProfiniteGrp.of A)).lift cone |>.hom
  let up :
      LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion
          (Multiplicative ℤ) →ₜ*
        ULift
          (LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion
            (Multiplicative ℤ)) :=
    { toFun := ULift.up
      map_one' := rfl
      map_mul' := by
        intro x y
        rfl
      continuous_toFun := continuous_uliftUp }
  let F :
      LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07OpenProfiniteCompletion
          (Multiplicative ℤ) →ₜ* A :=
    direct.comp up
  have hfac (V : OpenNormalSubgroup A) :=
    (ProfiniteGrp.isLimitCone (ProfiniteGrp.of A)).fac cone V
  have hraw (V : OpenNormalSubgroup A) (n : ℤ) :=
    congrArg
      (fun m => (ProfiniteGrp.Hom.hom m)
        (ULift.up
          (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
            (Multiplicative ℤ) (Multiplicative.ofAdd n))))
      (hfac V)
  have hcoordRaw (V : OpenNormalSubgroup A) (n : ℤ) :
      QuotientGroup.mk
          (F
            (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
              (Multiplicative ℤ) (Multiplicative.ofAdd n))) =
        (componentO V)
          (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
            (Multiplicative ℤ) (Multiplicative.ofAdd n)) := by
    have hf := hraw V n
    change
      QuotientGroup.mk
          (F
            (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
              (Multiplicative ℤ) (Multiplicative.ofAdd n))) =
        (componentO V)
          (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
            (Multiplicative ℤ) (Multiplicative.ofAdd n)) at hf
    exact hf
  have hpower (V : OpenNormalSubgroup A) (n : ℤ) :
      (componentO V)
          (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
            (Multiplicative ℤ) (Multiplicative.ofAdd n)) =
        QuotientGroup.mk (α ^ n) := by
    let P := preimage V
    let q : ((Multiplicative ℤ) ⧸ P.toSubgroup) →* (A ⧸ V.toSubgroup) :=
      QuotientGroup.map _ _ (↑f) (by
        intro z hz
        dsimp [P, preimage] at hz
        exact hz)
    change
      q
          (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection
            (Multiplicative ℤ) P
            (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEta
              (Multiplicative ℤ) (Multiplicative.ofAdd n))) =
        QuotientGroup.mk (α ^ n)
    rw [LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionProjection_eta]
    rfl
  refine ⟨F, by
    intro n
    apply ProfiniteGrp.toLimit_injective (ProfiniteGrp.of A)
    apply Subtype.ext
    funext V
    change
      QuotientGroup.mk
          (F
            (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
              (Multiplicative ℤ) (Multiplicative.ofAdd n))) =
        QuotientGroup.mk (α ^ n)
    calc
      _ = (componentO V)
          (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07OpenProfiniteCompletionEtaFn
            (Multiplicative ℤ) (Multiplicative.ofAdd n)) :=
        hcoordRaw V n
      _ = QuotientGroup.mk (α ^ n) := hpower V n⟩

end
end LastLib.Book05LocalClassFieldTheory.Chapter11
