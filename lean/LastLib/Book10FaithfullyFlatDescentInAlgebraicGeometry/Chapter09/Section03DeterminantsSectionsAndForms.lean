import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u v

/-! ## 9.3 Determinants, sections, and forms -/

abbrev Chapter09Section
    {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r) :=
  E.carrier.val.sections

abbrev Chapter09PullbackSectionData
    {S T : Scheme.{u}} (p : T ⟶ S) (M : S.Modules) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02PullbackSectionData p M

noncomputable def chapter09PullbackSectionData
    {S T : Scheme.{u}} (p : T ⟶ S) (M : S.Modules) :
    Chapter09PullbackSectionData p M :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02PullbackSectionData p M

noncomputable def chapter09PullbackMapToUnit
    {S T : Scheme.{u}} (p : T ⟶ S) {M : S.Modules}
    (φ : M ⟶ SheafOfModules.unit S.ringCatSheaf) :
    Chapter09PullbackModule p M ⟶ SheafOfModules.unit T.ringCatSheaf :=
  (Scheme.Modules.pullback p).map φ ≫
    (chapter09PullbackSectionData p M).unitComparison.hom

noncomputable def chapter09TensorModule
    {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02Tensor M N

noncomputable def chapter09TensorPower
    {X : Scheme.{u}} (M : X.Modules) (n : ℕ) : X.Modules :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02TensorPower M n

noncomputable def chapter09LineBundleTensorPower
    {X : Scheme.{u}} (L : Chapter09LineBundle X) (n : ℕ) : Chapter09LineBundle X where
  carrier := chapter09TensorPower L.carrier n
  locallyFree := by
    let L₂ :
        LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02LineBundle X :=
      { carrier := L.carrier
        invertible := L.locallyFree.2.2 }
    let P :=
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02LineBundlePowerData L₂
    let e : P.power n ≅ chapter09TensorPower L.carrier n := by
      simpa [chapter09TensorPower, L₂] using P.power_is_tensorPower n
    rcases P.power_invertible n with ⟨q, hq, hrank⟩
    let q' : (chapter09TensorPower L.carrier n).LocalGeneratorsData :=
      { I := q.I
        X := q.X
        coversTop := q.coversTop
        generators i := by
          let eᵢ := (SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e
          letI : IsIso eᵢ.hom := eᵢ.isIso_hom
          letI : Epi eᵢ.hom := by infer_instance
          exact (q.generators i).ofEpi eᵢ.hom }
    have hq' : q'.IsLocallyFreeData := by
      constructor
      intro i
      let eᵢ := (SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e
      change IsIso ((q.generators i).ofEpi eᵢ.hom).π
      rw [SheafOfModules.GeneratingSections.ofEpi_π]
      exact IsIso.comp_isIso' (hq.isIso i) eᵢ.isIso_hom
    have hqfin : q'.IsFiniteType := by
      constructor
      intro i
      let ei : (q.generators (i : q.I)).I ≃ Fin 1 :=
        Classical.choice (hrank (i : q.I))
      exact ⟨Finite.of_injective ei.toFun ei.injective⟩
    have hfinite : (chapter09TensorPower L.carrier n).IsFiniteType := by
      refine { exists_localGeneratorsData := ?_ }
      refine ⟨q'.shrink, ?_⟩
      constructor
      intro i
      change (q'.generators i.2.choose).IsFiniteType
      exact hqfin.isFiniteType i.2.choose
    have hqc : (chapter09TensorPower L.carrier n).IsQuasicoherent :=
      q'.quasiCoherentData.isQuasicoherent
    refine ⟨hqc, hfinite, ?_⟩
    · exact ⟨q', hq', fun i => by simpa [q'] using hrank i⟩

/-! ### Closed subschemes and regular sections -/

abbrev Chapter09ClosedSubscheme (X : Scheme.{u}) := X.IdealSheafData

/- The pinned sheaf API exposes the tensor carrier, but not the finite locally free operations used
by this section as a single functorial package.  Keep those operations in one data interface.  In
particular, all comparison maps used below are fields of the same package as their carriers; this
prevents a later declaration from silently combining unrelated provisional choices. -/
structure Chapter09SheafOperationsData where
  dual : ∀ {X : Scheme.{u}}, X.Modules → X.Modules
  symmetricPower : ∀ {X : Scheme.{u}}, ℕ → X.Modules → X.Modules
  exteriorPower : ∀ {X : Scheme.{u}}, ℕ → X.Modules → X.Modules
  internalHom : ∀ {X : Scheme.{u}}, X.Modules → X.Modules → X.Modules
  tensorToExteriorSquare : ∀ {X : Scheme.{u}} (M : X.Modules),
    chapter09TensorModule M M ⟶ exteriorPower 2 M
  tensorToExteriorSquare_epi :
    ∀ {X : Scheme.{u}} (M : X.Modules),
      Epi (tensorToExteriorSquare M)
  tensorSwap : ∀ {X : Scheme.{u}} (M N : X.Modules),
    chapter09TensorModule M N ⟶ chapter09TensorModule N M
  dualEvaluation : ∀ {X : Scheme.{u}} (M : X.Modules),
    chapter09TensorModule (dual M) M ⟶ SheafOfModules.unit X.ringCatSheaf
  dualUnit : ∀ {X : Scheme.{u}} (M : X.Modules),
    dual M ⟶ chapter09TensorModule (dual M) (SheafOfModules.unit X.ringCatSheaf)
  exteriorPowerPullback :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (M : X.Modules),
      Chapter09PullbackModule f (exteriorPower n M) ≅
        exteriorPower n (Chapter09PullbackModule f M)
  tensorPullback :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules),
      Chapter09PullbackModule f (chapter09TensorModule M N) ≅
        chapter09TensorModule (Chapter09PullbackModule f M)
          (Chapter09PullbackModule f N)
  dualPullback :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) {r : ℕ} (M : X.Modules)
      (_hM : chapter09FiniteLocallyFreeOfRank M r),
      Chapter09PullbackModule f (dual M) ≅
        dual (Chapter09PullbackModule f M)
  symmetricPowerPullback :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (M : X.Modules),
      Chapter09PullbackModule f (symmetricPower n M) ≅
        symmetricPower n (Chapter09PullbackModule f M)
  tensorToExteriorSquare_pullback :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules),
      (tensorPullback f M M).hom ≫ tensorToExteriorSquare
          (Chapter09PullbackModule f M) =
        (Scheme.Modules.pullback f).map (tensorToExteriorSquare M) ≫
          (exteriorPowerPullback f 2 M).hom
  exteriorPower_preserves_finite_locally_free :
    ∀ {X : Scheme.{u}} {M : X.Modules} (r n : ℕ),
      chapter09FiniteLocallyFreeOfRank M r →
        chapter09FiniteLocallyFreeOfRank (exteriorPower n M) (Nat.choose r n)
  tensor_preserves_finite_locally_free :
    ∀ {X : Scheme.{u}} {M N : X.Modules} {r s : ℕ},
      chapter09FiniteLocallyFreeOfRank M r →
        chapter09FiniteLocallyFreeOfRank N s →
          chapter09FiniteLocallyFreeOfRank (chapter09TensorModule M N) (r * s)
  dual_preserves_finite_locally_free :
    ∀ {X : Scheme.{u}} {M : X.Modules} {r : ℕ},
      chapter09FiniteLocallyFreeOfRank M r →
        chapter09FiniteLocallyFreeOfRank (dual M) r
  symmetricPower_preserves_finite_locally_free :
    ∀ {X : Scheme.{u}} {M : X.Modules} (n r : ℕ),
      chapter09FiniteLocallyFreeOfRank M r →
        chapter09FiniteLocallyFreeOfRank (symmetricPower n M) (Nat.choose (r + n - 1) n)
  internalHom_preserves_finite_locally_free :
    ∀ {X : Scheme.{u}} {M N : X.Modules} {r s : ℕ},
      chapter09FiniteLocallyFreeOfRank M r →
        chapter09FiniteLocallyFreeOfRank N s →
          chapter09FiniteLocallyFreeOfRank (internalHom M N) (r * s)
  internalHomPullback :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) {r : ℕ} (M N : X.Modules)
      (_hM : chapter09FiniteLocallyFreeOfRank M r),
      Chapter09PullbackModule f (internalHom M N) ≅
        internalHom (Chapter09PullbackModule f M) (Chapter09PullbackModule f N)
  tensorMap :
    ∀ {X : Scheme.{u}} {M M' N N' : X.Modules} (_f : M ⟶ M') (_g : N ⟶ N'),
      chapter09TensorModule M N ⟶ chapter09TensorModule M' N'
  tensorMapIso :
    ∀ {X : Scheme.{u}} {M M' N N' : X.Modules} (f : M ≅ M') (g : N ≅ N'),
      {e : chapter09TensorModule M N ≅ chapter09TensorModule M' N' //
        e.hom = tensorMap f.hom g.hom}
  dualMap :
    ∀ {X : Scheme.{u}} {M M' : X.Modules} (_f : M ⟶ M'),
      dual M' ⟶ dual M
  dualMapIso :
    ∀ {X : Scheme.{u}} {M M' : X.Modules} (f : M ≅ M'),
      {e : dual M' ≅ dual M // e.hom = dualMap f.hom}
  symmetricPowerMap :
    ∀ {X : Scheme.{u}} (n : ℕ) {M M' : X.Modules} (_f : M ⟶ M'),
      symmetricPower n M ⟶ symmetricPower n M'
  symmetricPowerMapIso :
    ∀ {X : Scheme.{u}} (n : ℕ) {M M' : X.Modules} (f : M ≅ M'),
      {e : symmetricPower n M ≅ symmetricPower n M' //
        e.hom = symmetricPowerMap n f.hom}
  exteriorPowerMap :
    ∀ {X : Scheme.{u}} (n : ℕ) {M M' : X.Modules} (_f : M ⟶ M'),
      exteriorPower n M ⟶ exteriorPower n M'
  exteriorPowerMapIso :
    ∀ {X : Scheme.{u}} (n : ℕ) {M M' : X.Modules} (f : M ≅ M'),
      {e : exteriorPower n M ≅ exteriorPower n M' //
        e.hom = exteriorPowerMap n f.hom}
  determinant_detects_isomorphism :
    ∀ {X : Scheme.{u}} {r : ℕ}
      (E F : Chapter09VectorBundle X r) (f : E.carrier ⟶ F.carrier),
      IsIso f ↔ IsIso (exteriorPowerMap r f)
  internalHomMap :
    ∀ {X : Scheme.{u}} {M M' N N' : X.Modules} (_f : M' ⟶ M) (_g : N ⟶ N'),
      internalHom M N ⟶ internalHom M' N'
  internalHomMapIso :
    ∀ {X : Scheme.{u}} {M M' N N' : X.Modules} (f : M' ≅ M) (g : N ≅ N'),
      {e : internalHom M N ≅ internalHom M' N' //
        e.hom = internalHomMap f.hom g.hom}
  bilinearFormAdjointMap :
    ∀ {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r)
      (L : Chapter09LineBundle X)
      (_b : chapter09TensorModule E.carrier E.carrier ⟶ L.carrier),
      E.carrier ⟶ chapter09TensorModule (dual E.carrier) L.carrier
  sectionDualMap :
    ∀ {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r)
      (s : Chapter09Section E),
      {φ : dual E.carrier ⟶ SheafOfModules.unit X.ringCatSheaf //
        φ = dualUnit E.carrier ≫
          tensorMap (𝟙 _) (E.carrier.unitHomEquiv.symm s) ≫ dualEvaluation E.carrier}
  sectionDualMap_natural :
    ∀ {X : Scheme.{u}} {r : ℕ} (E F : Chapter09VectorBundle X r)
      (e : E.carrier ≅ F.carrier) (s : Chapter09Section E),
      dualMap e.hom ≫ (sectionDualMap E s).1 =
        (sectionDualMap F (SheafOfModules.sectionsMap e.hom s)).1
  bilinearFormAdjoint :
    ∀ {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r)
      (L : Chapter09LineBundle X)
      (b : chapter09TensorModule E.carrier E.carrier ⟶ L.carrier),
      {f : E.carrier ⟶ chapter09TensorModule (dual E.carrier) L.carrier //
        f = bilinearFormAdjointMap E L b}
  idealSheafOfMap :
    ∀ {X : Scheme.{u}} {M : X.Modules}
      (_φ : M ⟶ SheafOfModules.unit X.ringCatSheaf), Chapter09ClosedSubscheme X
  idealSheafOfMap_iso :
    ∀ {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
      (φ : N ⟶ SheafOfModules.unit X.ringCatSheaf),
      idealSheafOfMap (e.hom ≫ φ) = idealSheafOfMap φ

  /- The operation maps are a single functorial package, rather than unrelated choices on each
  object.  These laws are the API used by descent of tensor constructions and equalities of maps. -/
  tensorMap_id :
    ∀ {X : Scheme.{u}} {M N : X.Modules},
      tensorMap (𝟙 M) (𝟙 N) = 𝟙 (chapter09TensorModule M N)
  tensorMap_comp :
    ∀ {X : Scheme.{u}} {M M' M'' N N' N'' : X.Modules}
      (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N''),
      tensorMap (f ≫ f') (g ≫ g') = tensorMap f g ≫ tensorMap f' g'
  dualMap_id :
    ∀ {X : Scheme.{u}} {M : X.Modules}, dualMap (𝟙 M) = 𝟙 (dual M)
  dualMap_comp :
    ∀ {X : Scheme.{u}} {M M' M'' : X.Modules}
      (f : M ⟶ M') (f' : M' ⟶ M''),
      dualMap (f ≫ f') = dualMap f' ≫ dualMap f
  symmetricPowerMap_id :
    ∀ {X : Scheme.{u}} (n : ℕ) {M : X.Modules},
      symmetricPowerMap n (𝟙 M) = 𝟙 (symmetricPower n M)
  symmetricPowerMap_comp :
    ∀ {X : Scheme.{u}} (n : ℕ) {M M' M'' : X.Modules}
      (f : M ⟶ M') (f' : M' ⟶ M''),
      symmetricPowerMap n (f ≫ f') = symmetricPowerMap n f ≫ symmetricPowerMap n f'
  exteriorPowerMap_id :
    ∀ {X : Scheme.{u}} (n : ℕ) {M : X.Modules},
      exteriorPowerMap n (𝟙 M) = 𝟙 (exteriorPower n M)
  exteriorPowerMap_comp :
    ∀ {X : Scheme.{u}} (n : ℕ) {M M' M'' : X.Modules}
      (f : M ⟶ M') (f' : M' ⟶ M''),
      exteriorPowerMap n (f ≫ f') = exteriorPowerMap n f ≫ exteriorPowerMap n f'
  internalHomMap_id :
    ∀ {X : Scheme.{u}} {M N : X.Modules},
      internalHomMap (𝟙 M) (𝟙 N) = 𝟙 (internalHom M N)
  internalHomMap_comp :
    ∀ {X : Scheme.{u}} {M₀ M₁ M₂ N₀ N₁ N₂ : X.Modules}
      (f₁ : M₁ ⟶ M₀) (f₂ : M₂ ⟶ M₁)
      (g₁ : N₀ ⟶ N₁) (g₂ : N₁ ⟶ N₂),
      internalHomMap (f₂ ≫ f₁) (g₁ ≫ g₂) =
        internalHomMap f₁ g₁ ≫ internalHomMap f₂ g₂
  tensorSwap_natural :
    ∀ {X : Scheme.{u}} {M M' N N' : X.Modules}
      (f : M ⟶ M') (g : N ⟶ N'),
      tensorSwap M N ≫ tensorMap g f = tensorMap f g ≫ tensorSwap M' N'
  tensorToExteriorSquare_natural :
    ∀ {X : Scheme.{u}} {M M' : X.Modules} (f : M ⟶ M'),
      tensorToExteriorSquare M ≫ exteriorPowerMap 2 f =
        tensorMap f f ≫ tensorToExteriorSquare M'
  dualEvaluation_natural :
    ∀ {X : Scheme.{u}} {M M' : X.Modules} (f : M ⟶ M'),
      tensorMap (dualMap f) (𝟙 M) ≫ dualEvaluation M =
        tensorMap (𝟙 (dual M')) f ≫ dualEvaluation M'
  dualUnit_natural :
    ∀ {X : Scheme.{u}} {M M' : X.Modules} (f : M ⟶ M'),
      dualMap f ≫ dualUnit M = dualUnit M' ≫ tensorMap (dualMap f) (𝟙 _)

  /- Pullback naturality makes the comparison isomorphisms usable on maps. -/
  tensorPullback_natural :
    ∀ {X Y : Scheme.{u}} (p : Y ⟶ X)
      {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N'),
      (tensorPullback p M N).hom ≫ tensorMap
          ((Scheme.Modules.pullback p).map f) ((Scheme.Modules.pullback p).map g) =
        (Scheme.Modules.pullback p).map (tensorMap f g) ≫
          (tensorPullback p M' N').hom
  dualPullback_natural :
    ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) {r : ℕ}
      {M M' : X.Modules} (f : M ⟶ M')
      (hM : chapter09FiniteLocallyFreeOfRank M r)
      (hM' : chapter09FiniteLocallyFreeOfRank M' r),
      (dualPullback p M' hM').hom ≫ dualMap ((Scheme.Modules.pullback p).map f) =
        (Scheme.Modules.pullback p).map (dualMap f) ≫ (dualPullback p M hM).hom
  symmetricPowerPullback_natural :
    ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) (n : ℕ)
      {M M' : X.Modules} (f : M ⟶ M'),
      (symmetricPowerPullback p n M).hom ≫ symmetricPowerMap n
          ((Scheme.Modules.pullback p).map f) =
        (Scheme.Modules.pullback p).map (symmetricPowerMap n f) ≫
          (symmetricPowerPullback p n M').hom
  exteriorPowerPullback_natural :
    ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) (n : ℕ)
      {M M' : X.Modules} (f : M ⟶ M'),
      (exteriorPowerPullback p n M).hom ≫ exteriorPowerMap n
          ((Scheme.Modules.pullback p).map f) =
        (Scheme.Modules.pullback p).map (exteriorPowerMap n f) ≫
          (exteriorPowerPullback p n M').hom
  internalHomPullback_natural :
    ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) {r : ℕ}
      {M M' N N' : X.Modules} (f : M' ⟶ M) (g : N ⟶ N')
      (hM : chapter09FiniteLocallyFreeOfRank M r)
      (hM' : chapter09FiniteLocallyFreeOfRank M' r),
      (internalHomPullback p M N hM).hom ≫ internalHomMap
          ((Scheme.Modules.pullback p).map f) ((Scheme.Modules.pullback p).map g) =
        (Scheme.Modules.pullback p).map (internalHomMap f g) ≫
          (internalHomPullback p M' N' hM').hom

  /- The following are the pseudofunctorial Čech coherence laws.  They make the induced overlap
  maps independent of whether a triple overlap is formed in one or two pullback steps. -/
  tensorPullback_cech :
    ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (M N : X.Modules),
      chapter09PullbackCompositionIso g f (chapter09TensorModule M N) ≪≫
          (Scheme.Modules.pullback g).mapIso (tensorPullback f M N) ≪≫
          tensorPullback g (Chapter09PullbackModule f M) (Chapter09PullbackModule f N) ≪≫
          (tensorMapIso (chapter09PullbackCompositionIso g f M).symm
            (chapter09PullbackCompositionIso g f N).symm).1 =
        tensorPullback (g ≫ f) M N
  dualPullback_cech :
    ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) {r : ℕ} (M : X.Modules)
      (hM : chapter09FiniteLocallyFreeOfRank M r)
      (hM_f : chapter09FiniteLocallyFreeOfRank (Chapter09PullbackModule f M) r),
      chapter09PullbackCompositionIso g f (dual M) ≪≫
          (Scheme.Modules.pullback g).mapIso (dualPullback f M hM) ≪≫
          dualPullback g (Chapter09PullbackModule f M) hM_f ≪≫
          (dualMapIso (chapter09PullbackCompositionIso g f M)).1 =
        dualPullback (g ≫ f) M hM
  symmetricPowerPullback_cech :
    ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (n : ℕ) (M : X.Modules),
      chapter09PullbackCompositionIso g f (symmetricPower n M) ≪≫
          (Scheme.Modules.pullback g).mapIso (symmetricPowerPullback f n M) ≪≫
          symmetricPowerPullback g n (Chapter09PullbackModule f M) ≪≫
          (symmetricPowerMapIso n (chapter09PullbackCompositionIso g f M)).1.symm =
        symmetricPowerPullback (g ≫ f) n M
  exteriorPowerPullback_cech :
    ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (n : ℕ) (M : X.Modules),
      chapter09PullbackCompositionIso g f (exteriorPower n M) ≪≫
          (Scheme.Modules.pullback g).mapIso (exteriorPowerPullback f n M) ≪≫
          exteriorPowerPullback g n (Chapter09PullbackModule f M) ≪≫
          (exteriorPowerMapIso n (chapter09PullbackCompositionIso g f M)).1.symm =
        exteriorPowerPullback (g ≫ f) n M
  internalHomPullback_cech :
    ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) {r : ℕ}
      (M N : X.Modules) (hM : chapter09FiniteLocallyFreeOfRank M r)
      (hM_f : chapter09FiniteLocallyFreeOfRank (Chapter09PullbackModule f M) r),
      chapter09PullbackCompositionIso g f (internalHom M N) ≪≫
          (Scheme.Modules.pullback g).mapIso (internalHomPullback f M N hM) ≪≫
          internalHomPullback g (Chapter09PullbackModule f M)
            (Chapter09PullbackModule f N) hM_f ≪≫
          (internalHomMapIso (chapter09PullbackCompositionIso g f M)
            (chapter09PullbackCompositionIso g f N).symm).1 =
        internalHomPullback (g ≫ f) M N hM

  /- Sections and ideals use the same unit comparison as the selected pullback-section map. -/
  pullbackSectionMap_natural :
    ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) {M N : X.Modules}
      (h : M ⟶ N) (s : M.sections),
      (chapter09PullbackSectionData p N).map (SheafOfModules.sectionsMap h s) =
        SheafOfModules.sectionsMap ((Scheme.Modules.pullback p).map h)
          ((chapter09PullbackSectionData p M).map s)
  sectionDualMap_pullback :
    ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) {r : ℕ}
      (E : Chapter09VectorBundle X r) (s : Chapter09Section E),
      chapter09PullbackMapToUnit p (M := dual E.carrier)
          (sectionDualMap E s).1 =
        (dualPullback p E.carrier E.locallyFree).hom ≫
          (sectionDualMap (chapter09PullbackVectorBundle p E)
            ((chapter09PullbackSectionData p E.carrier).map s)).1
  idealSheafOfMap_pullback :
    ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) {M : X.Modules}
      (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf),
      idealSheafOfMap (chapter09PullbackMapToUnit p φ) =
        (idealSheafOfMap φ).comap p
  bilinearFormAdjoint_pullback :
    ∀ {X Y : Scheme.{u}} (p : Y ⟶ X) {r : ℕ}
      (E : Chapter09VectorBundle X r) (L : Chapter09LineBundle X)
      (b : chapter09TensorModule E.carrier E.carrier ⟶ L.carrier),
          (Scheme.Modules.pullback p).map (bilinearFormAdjointMap E L b) ≫
          (tensorPullback p (dual E.carrier) L.carrier).hom ≫
          tensorMap (dualPullback p E.carrier E.locallyFree).hom (𝟙 _) =
        bilinearFormAdjointMap (chapter09PullbackVectorBundle p E)
          (chapter09PullbackLineBundle p L)
          ((tensorPullback p E.carrier E.carrier).inv ≫
            (Scheme.Modules.pullback p).map b)

theorem chapter09_sheaf_operations_data_exists :
    Nonempty Chapter09SheafOperationsData := by
  sorry

noncomputable def chapter09SheafOperations : Chapter09SheafOperationsData :=
  Classical.choice chapter09_sheaf_operations_data_exists

noncomputable def chapter09ClosedSubschemeScheme
    {X : Scheme.{u}} (Z : Chapter09ClosedSubscheme X) : Scheme.{u} :=
  Z.subscheme

noncomputable def chapter09ClosedSubschemeInclusion
    {X : Scheme.{u}} (Z : Chapter09ClosedSubscheme X) :
    chapter09ClosedSubschemeScheme Z ⟶ X :=
  Z.subschemeι

theorem chapter09_closedSubscheme_inclusion_isClosedImmersion
    {X : Scheme.{u}} (Z : Chapter09ClosedSubscheme X) :
    IsClosedImmersion (chapter09ClosedSubschemeInclusion Z) := by
  exact (inferInstance : IsClosedImmersion Z.subschemeι)

noncomputable def chapter09SectionAsMap
    {X : Scheme.{u}} (L : Chapter09LineBundle X) (s : Chapter09Section L) :
    SheafOfModules.unit X.ringCatSheaf ⟶ L.carrier :=
  L.carrier.unitHomEquiv.symm s

def chapter09RegularSection
    {X : Scheme.{u}} (L : Chapter09LineBundle X) (s : Chapter09Section L) : Prop :=
  Mono (chapter09SectionAsMap L s)

/-! ### Operations on finite locally free sheaves -/
noncomputable def chapter09DualModule
    {X : Scheme.{u}} (M : X.Modules) : X.Modules :=
  Chapter09SheafOperationsData.dual chapter09SheafOperations M

noncomputable def chapter09SymmetricPowerModule
    {X : Scheme.{u}} (n : ℕ) (M : X.Modules) : X.Modules :=
  Chapter09SheafOperationsData.symmetricPower chapter09SheafOperations n M

noncomputable def chapter09ExteriorPowerModule
    {X : Scheme.{u}} (n : ℕ) (M : X.Modules) : X.Modules :=
  Chapter09SheafOperationsData.exteriorPower chapter09SheafOperations n M

noncomputable def chapter09TensorToExteriorSquare
    {X : Scheme.{u}} (M : X.Modules) :
    chapter09TensorModule M M ⟶ chapter09ExteriorPowerModule 2 M :=
  Chapter09SheafOperationsData.tensorToExteriorSquare chapter09SheafOperations M

noncomputable def chapter09InternalHomModule
    {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  Chapter09SheafOperationsData.internalHom chapter09SheafOperations M N

noncomputable def chapter09TensorSwap
    {X : Scheme.{u}} (M N : X.Modules) :
    chapter09TensorModule M N ⟶ chapter09TensorModule N M :=
  Chapter09SheafOperationsData.tensorSwap chapter09SheafOperations M N

noncomputable def chapter09BilinearFormAdjoint
    {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r)
    (L : Chapter09LineBundle X)
  (b : chapter09TensorModule E.carrier E.carrier ⟶ L.carrier) :
    E.carrier ⟶ chapter09TensorModule (chapter09DualModule E.carrier) L.carrier :=
  (Chapter09SheafOperationsData.bilinearFormAdjoint chapter09SheafOperations E L b).1

noncomputable def chapter09DeterminantModule
    {X : Scheme.{u}} (r : ℕ) (M : X.Modules) : X.Modules :=
  chapter09ExteriorPowerModule r M

noncomputable def chapter09_determinant_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) {r : ℕ} (M : X.Modules) :
    Chapter09PullbackModule f (chapter09DeterminantModule r M) ≅
      chapter09DeterminantModule r (Chapter09PullbackModule f M) :=
  Chapter09SheafOperationsData.exteriorPowerPullback chapter09SheafOperations f r M

noncomputable def chapter09_tensor_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) :
    Chapter09PullbackModule f (chapter09TensorModule M N) ≅
      chapter09TensorModule (Chapter09PullbackModule f M) (Chapter09PullbackModule f N) :=
  Chapter09SheafOperationsData.tensorPullback chapter09SheafOperations f M N

noncomputable def chapter09_dual_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) {r : ℕ} (M : X.Modules)
    (_hM : chapter09FiniteLocallyFreeOfRank M r) :
    Chapter09PullbackModule f (chapter09DualModule M) ≅
      chapter09DualModule (Chapter09PullbackModule f M) :=
  Chapter09SheafOperationsData.dualPullback chapter09SheafOperations f M _hM

noncomputable def chapter09_symmetric_power_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (M : X.Modules) :
    Chapter09PullbackModule f (chapter09SymmetricPowerModule n M) ≅
      chapter09SymmetricPowerModule n (Chapter09PullbackModule f M) :=
  Chapter09SheafOperationsData.symmetricPowerPullback chapter09SheafOperations f n M

noncomputable def chapter09_exterior_power_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (M : X.Modules) :
    Chapter09PullbackModule f (chapter09ExteriorPowerModule n M) ≅
      chapter09ExteriorPowerModule n (Chapter09PullbackModule f M) :=
  Chapter09SheafOperationsData.exteriorPowerPullback chapter09SheafOperations f n M

noncomputable def chapter09_internal_hom_commutes_with_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) {r : ℕ} (M N : X.Modules)
    (_hM : chapter09FiniteLocallyFreeOfRank M r) :
    Chapter09PullbackModule f (chapter09InternalHomModule M N) ≅
      chapter09InternalHomModule (Chapter09PullbackModule f M)
        (Chapter09PullbackModule f N) :=
  Chapter09SheafOperationsData.internalHomPullback chapter09SheafOperations f M N _hM

noncomputable def chapter09TensorMapIso
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ≅ M') (g : N ≅ N') :
  chapter09TensorModule M N ≅ chapter09TensorModule M' N' :=
  (Chapter09SheafOperationsData.tensorMapIso chapter09SheafOperations f g).1

noncomputable def chapter09DualMapIso
    {X : Scheme.{u}} {M M' : X.Modules} (f : M ≅ M') :
  chapter09DualModule M' ≅ chapter09DualModule M :=
  (Chapter09SheafOperationsData.dualMapIso chapter09SheafOperations f).1

noncomputable def chapter09SymmetricPowerMapIso
    {X : Scheme.{u}} (n : ℕ) {M M' : X.Modules} (f : M ≅ M') :
  chapter09SymmetricPowerModule n M ≅ chapter09SymmetricPowerModule n M' :=
  (Chapter09SheafOperationsData.symmetricPowerMapIso chapter09SheafOperations n f).1

noncomputable def chapter09ExteriorPowerMapIso
    {X : Scheme.{u}} (n : ℕ) {M M' : X.Modules} (f : M ≅ M') :
  chapter09ExteriorPowerModule n M ≅ chapter09ExteriorPowerModule n M' :=
  (Chapter09SheafOperationsData.exteriorPowerMapIso chapter09SheafOperations n f).1

noncomputable def chapter09DeterminantMap
    {X : Scheme.{u}} (r : ℕ) {M M' : X.Modules} (f : M ⟶ M') :
    chapter09DeterminantModule r M ⟶ chapter09DeterminantModule r M' :=
  Chapter09SheafOperationsData.exteriorPowerMap chapter09SheafOperations r f

theorem chapter09_determinant_map_pullback_natural
    {X Y : Scheme.{u}} (p : Y ⟶ X) (r : ℕ)
    {M M' : X.Modules} (f : M ⟶ M') :
    (chapter09_determinant_commutes_with_pullback p (r := r) M).hom ≫
        chapter09DeterminantMap r ((Scheme.Modules.pullback p).map f) =
      (Scheme.Modules.pullback p).map (chapter09DeterminantMap r f) ≫
        (chapter09_determinant_commutes_with_pullback p (r := r) M').hom := by
  exact Chapter09SheafOperationsData.exteriorPowerPullback_natural
    chapter09SheafOperations p r f

theorem chapter09_isIso_iff_determinant_map_isIso
    {X : Scheme.{u}} {r : ℕ}
    (E F : Chapter09VectorBundle X r) (f : E.carrier ⟶ F.carrier) :
    IsIso f ↔ IsIso (chapter09DeterminantMap r f) := by
  exact Chapter09SheafOperationsData.determinant_detects_isomorphism
    chapter09SheafOperations E F f

theorem chapter09_determinant_of_vector_bundle_is_line_bundle
    {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r) :
    chapter09FiniteLocallyFreeOfRank
      (chapter09DeterminantModule r E.carrier) 1 := by
  change chapter09FiniteLocallyFreeOfRank
    (Chapter09SheafOperationsData.exteriorPower chapter09SheafOperations r E.carrier) 1
  have h :=
    Chapter09SheafOperationsData.exteriorPower_preserves_finite_locally_free
      (self := chapter09SheafOperations) (M := E.carrier) r r E.locallyFree
  simpa using h

noncomputable def chapter09DeterminantLineBundle
    {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r) :
    Chapter09LineBundle X where
  carrier := chapter09DeterminantModule r E.carrier
  locallyFree := chapter09_determinant_of_vector_bundle_is_line_bundle E

noncomputable def chapter09InternalHomMapIso
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M' ≅ M) (g : N ≅ N') :
  chapter09InternalHomModule M N ≅ chapter09InternalHomModule M' N' :=
  (Chapter09SheafOperationsData.internalHomMapIso chapter09SheafOperations f g).1

noncomputable def chapter09TensorOverlapIso
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) :
    Chapter09PullbackModule (chapter09DoubleFirst p)
        (chapter09TensorModule D.upstairs.carrier E.upstairs.carrier) ≅
      Chapter09PullbackModule (chapter09DoubleSecond p)
        (chapter09TensorModule D.upstairs.carrier E.upstairs.carrier) :=
  chapter09_tensor_commutes_with_pullback (chapter09DoubleFirst p)
      D.upstairs.carrier E.upstairs.carrier ≪≫
    chapter09TensorMapIso D.overlapIso E.overlapIso ≪≫
    (chapter09_tensor_commutes_with_pullback (chapter09DoubleSecond p)
      D.upstairs.carrier E.upstairs.carrier).symm

noncomputable def chapter09DualOverlapIso
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) :
    Chapter09PullbackModule (chapter09DoubleFirst p)
        (chapter09DualModule D.upstairs.carrier) ≅
      Chapter09PullbackModule (chapter09DoubleSecond p)
        (chapter09DualModule D.upstairs.carrier) :=
  chapter09_dual_commutes_with_pullback (chapter09DoubleFirst p)
      D.upstairs.carrier D.upstairs.locallyFree ≪≫
    chapter09DualMapIso D.overlapIso.symm ≪≫
    (chapter09_dual_commutes_with_pullback (chapter09DoubleSecond p)
      D.upstairs.carrier D.upstairs.locallyFree).symm

noncomputable def chapter09SymmetricPowerOverlapIso
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (n : ℕ) (D : Chapter09ModuleDescentDatum p r) :
    Chapter09PullbackModule (chapter09DoubleFirst p)
        (chapter09SymmetricPowerModule n D.upstairs.carrier) ≅
      Chapter09PullbackModule (chapter09DoubleSecond p)
        (chapter09SymmetricPowerModule n D.upstairs.carrier) :=
  chapter09_symmetric_power_commutes_with_pullback (chapter09DoubleFirst p)
      n D.upstairs.carrier ≪≫
    chapter09SymmetricPowerMapIso n D.overlapIso ≪≫
    (chapter09_symmetric_power_commutes_with_pullback (chapter09DoubleSecond p)
      n D.upstairs.carrier).symm

noncomputable def chapter09ExteriorPowerOverlapIso
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (n : ℕ) (D : Chapter09ModuleDescentDatum p r) :
    Chapter09PullbackModule (chapter09DoubleFirst p)
        (chapter09ExteriorPowerModule n D.upstairs.carrier) ≅
      Chapter09PullbackModule (chapter09DoubleSecond p)
        (chapter09ExteriorPowerModule n D.upstairs.carrier) :=
  chapter09_exterior_power_commutes_with_pullback (chapter09DoubleFirst p)
      n D.upstairs.carrier ≪≫
    chapter09ExteriorPowerMapIso n D.overlapIso ≪≫
    (chapter09_exterior_power_commutes_with_pullback (chapter09DoubleSecond p)
      n D.upstairs.carrier).symm

noncomputable def chapter09InternalHomOverlapIso
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) :
    Chapter09PullbackModule (chapter09DoubleFirst p)
        (chapter09InternalHomModule D.upstairs.carrier E.upstairs.carrier) ≅
      Chapter09PullbackModule (chapter09DoubleSecond p)
        (chapter09InternalHomModule D.upstairs.carrier E.upstairs.carrier) :=
  chapter09_internal_hom_commutes_with_pullback (chapter09DoubleFirst p)
      D.upstairs.carrier E.upstairs.carrier D.upstairs.locallyFree ≪≫
    chapter09InternalHomMapIso D.overlapIso.symm E.overlapIso ≪≫
    (chapter09_internal_hom_commutes_with_pullback (chapter09DoubleSecond p)
      D.upstairs.carrier E.upstairs.carrier D.upstairs.locallyFree).symm

def chapter09TensorDescentCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) : Prop :=
  chapter09CechCocycleCondition p D.nerve (chapter09TensorOverlapIso D E)

def chapter09DualDescentCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) : Prop :=
  chapter09CechCocycleCondition p D.nerve (chapter09DualOverlapIso D)

def chapter09SymmetricPowerDescentCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (n : ℕ) (D : Chapter09ModuleDescentDatum p r) : Prop :=
  chapter09CechCocycleCondition p D.nerve (chapter09SymmetricPowerOverlapIso n D)

def chapter09ExteriorPowerDescentCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (n : ℕ) (D : Chapter09ModuleDescentDatum p r) : Prop :=
  chapter09CechCocycleCondition p D.nerve (chapter09ExteriorPowerOverlapIso n D)

def chapter09InternalHomDescentCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) : Prop :=
  chapter09CechCocycleCondition p D.nerve (chapter09InternalHomOverlapIso D E)

private theorem chapter09_tensor_overlap_transport
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) :
    ∀ {U : Scheme.{u}} (q : U ⟶ Chapter09DoubleOverlap p),
      (chapter09_tensor_commutes_with_pullback
          (q ≫ chapter09DoubleFirst p) D.upstairs.carrier E.upstairs.carrier).hom ≫
        chapter09SheafOperations.tensorMap
          ((chapter09CechPullbackIso p q D.overlapIso).hom)
          ((chapter09CechPullbackIso p q E.overlapIso).hom) =
      (chapter09CechPullbackIso p q (chapter09TensorOverlapIso D E)).hom ≫
        (chapter09_tensor_commutes_with_pullback
          (q ≫ chapter09DoubleSecond p) D.upstairs.carrier E.upstairs.carrier).hom := by
  intro U q
  have htpF :
      (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
          (chapter09TensorModule D.upstairs.carrier E.upstairs.carrier)).hom ≫
        (Scheme.Modules.pullback q).map
          (chapter09_tensor_commutes_with_pullback (chapter09DoubleFirst p)
            D.upstairs.carrier E.upstairs.carrier).hom ≫
        (chapter09_tensor_commutes_with_pullback q
          (Chapter09PullbackModule (chapter09DoubleFirst p) D.upstairs.carrier)
          (Chapter09PullbackModule (chapter09DoubleFirst p) E.upstairs.carrier)).hom ≫
        (chapter09TensorMapIso
          (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
            D.upstairs.carrier).symm
          (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
            E.upstairs.carrier).symm).hom =
      (chapter09_tensor_commutes_with_pullback
        (q ≫ chapter09DoubleFirst p) D.upstairs.carrier E.upstairs.carrier).hom := by
    exact congrArg (fun e => e.hom)
      (Chapter09SheafOperationsData.tensorPullback_cech
        chapter09SheafOperations (chapter09DoubleFirst p) q
          D.upstairs.carrier E.upstairs.carrier)
  have htpG :
      (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
          (chapter09TensorModule D.upstairs.carrier E.upstairs.carrier)).hom ≫
        (Scheme.Modules.pullback q).map
          (chapter09_tensor_commutes_with_pullback (chapter09DoubleSecond p)
            D.upstairs.carrier E.upstairs.carrier).hom ≫
        (chapter09_tensor_commutes_with_pullback q
          (Chapter09PullbackModule (chapter09DoubleSecond p) D.upstairs.carrier)
          (Chapter09PullbackModule (chapter09DoubleSecond p) E.upstairs.carrier)).hom ≫
        (chapter09TensorMapIso
          (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
            D.upstairs.carrier).symm
          (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
            E.upstairs.carrier).symm).hom =
      (chapter09_tensor_commutes_with_pullback
        (q ≫ chapter09DoubleSecond p) D.upstairs.carrier E.upstairs.carrier).hom := by
    exact congrArg (fun e => e.hom)
      (Chapter09SheafOperationsData.tensorPullback_cech
        chapter09SheafOperations (chapter09DoubleSecond p) q
          D.upstairs.carrier E.upstairs.carrier)
  have hnat :
      (chapter09_tensor_commutes_with_pullback q
          (Chapter09PullbackModule (chapter09DoubleFirst p) D.upstairs.carrier)
          (Chapter09PullbackModule (chapter09DoubleFirst p) E.upstairs.carrier)).hom ≫
        chapter09SheafOperations.tensorMap
          ((Scheme.Modules.pullback q).map D.overlapIso.hom)
          ((Scheme.Modules.pullback q).map E.overlapIso.hom) =
      (Scheme.Modules.pullback q).map
          (chapter09SheafOperations.tensorMap D.overlapIso.hom E.overlapIso.hom) ≫
        (chapter09_tensor_commutes_with_pullback q
          (Chapter09PullbackModule (chapter09DoubleSecond p) D.upstairs.carrier)
          (Chapter09PullbackModule (chapter09DoubleSecond p) E.upstairs.carrier)).hom := by
    exact Chapter09SheafOperationsData.tensorPullback_natural
      chapter09SheafOperations q D.overlapIso.hom E.overlapIso.hom
  have hIsoF :
      (chapter09TensorMapIso
          (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
            D.upstairs.carrier).symm
          (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
            E.upstairs.carrier).symm).hom =
        chapter09SheafOperations.tensorMap
          (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
            D.upstairs.carrier).inv
          (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
            E.upstairs.carrier).inv := by
    change ((Chapter09SheafOperationsData.tensorMapIso chapter09SheafOperations
      (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
        D.upstairs.carrier).symm
      (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
        E.upstairs.carrier).symm).1).hom = _
    exact (Chapter09SheafOperationsData.tensorMapIso chapter09SheafOperations
      (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
        D.upstairs.carrier).symm
      (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
        E.upstairs.carrier).symm).2
  have hIsoG :
      (chapter09TensorMapIso
          (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
            D.upstairs.carrier).symm
          (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
            E.upstairs.carrier).symm).hom =
        chapter09SheafOperations.tensorMap
          (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
            D.upstairs.carrier).inv
          (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
            E.upstairs.carrier).inv := by
    change ((Chapter09SheafOperationsData.tensorMapIso chapter09SheafOperations
      (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
        D.upstairs.carrier).symm
      (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
        E.upstairs.carrier).symm).1).hom = _
    exact (Chapter09SheafOperationsData.tensorMapIso chapter09SheafOperations
      (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
        D.upstairs.carrier).symm
      (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
        E.upstairs.carrier).symm).2
  simp only [chapter09CechPullbackIso, chapter09TensorOverlapIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← htpF, ← htpG, hIsoF, hIsoG]
  simp only [Functor.map_comp, Chapter09SheafOperationsData.tensorMap_comp,
    Category.assoc]
  have hcancelF :
      chapter09SheafOperations.tensorMap
          (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
            D.upstairs.carrier).inv
          (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
            E.upstairs.carrier).inv ≫
        chapter09SheafOperations.tensorMap
          (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
            D.upstairs.carrier).hom
          (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
            E.upstairs.carrier).hom =
      𝟙 _ := by
    rw [← Chapter09SheafOperationsData.tensorMap_comp chapter09SheafOperations
        (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
          D.upstairs.carrier).inv
        (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
          D.upstairs.carrier).hom
        (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
          E.upstairs.carrier).inv
        (chapter09PullbackCompositionIso q (chapter09DoubleFirst p)
          E.upstairs.carrier).hom]
    simp only [Iso.inv_hom_id, Chapter09SheafOperationsData.tensorMap_id]
  simp only [← Category.assoc, hcancelF, Category.id_comp]
  simp only [Category.assoc]
  rw [← Category.assoc
    (chapter09_tensor_commutes_with_pullback q
      (Chapter09PullbackModule (chapter09DoubleFirst p) D.upstairs.carrier)
      (Chapter09PullbackModule (chapter09DoubleFirst p) E.upstairs.carrier)).hom
    (chapter09SheafOperations.tensorMap
      ((Scheme.Modules.pullback q).map D.overlapIso.hom)
      ((Scheme.Modules.pullback q).map E.overlapIso.hom))
    (chapter09SheafOperations.tensorMap
      (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
        D.upstairs.carrier).inv
      (chapter09PullbackCompositionIso q (chapter09DoubleSecond p)
        E.upstairs.carrier).inv)]
  rw [hnat]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hIsoDE :
      (chapter09TensorMapIso D.overlapIso E.overlapIso).hom =
        chapter09SheafOperations.tensorMap D.overlapIso.hom E.overlapIso.hom := by
    change ((Chapter09SheafOperationsData.tensorMapIso chapter09SheafOperations
      D.overlapIso E.overlapIso).1).hom = _
    exact (Chapter09SheafOperationsData.tensorMapIso chapter09SheafOperations
      D.overlapIso E.overlapIso).2
  have hcancelG :
      (Scheme.Modules.pullback q).map
          (chapter09_tensor_commutes_with_pullback (chapter09DoubleSecond p)
            D.upstairs.carrier E.upstairs.carrier).inv ≫
        (Scheme.Modules.pullback q).map
          (chapter09_tensor_commutes_with_pullback (chapter09DoubleSecond p)
            D.upstairs.carrier E.upstairs.carrier).hom =
      𝟙 _ := by
    rw [← Functor.map_comp]
    simp
  rw [hIsoDE]
  simp only [← Category.assoc, hcancelG, Category.id_comp]

private theorem chapter09_tensor_cech_expansion
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s)
    {U : Scheme.{u}} (q : U ⟶ Chapter09DoubleOverlap p) :
    (chapter09CechPullbackIso p q (chapter09TensorOverlapIso D E)).hom =
      (chapter09_tensor_commutes_with_pullback
        (q ≫ chapter09DoubleFirst p) D.upstairs.carrier E.upstairs.carrier).hom ≫
        chapter09SheafOperations.tensorMap
          (chapter09CechPullbackIso p q D.overlapIso).hom
          (chapter09CechPullbackIso p q E.overlapIso).hom ≫
        (chapter09_tensor_commutes_with_pullback
          (q ≫ chapter09DoubleSecond p) D.upstairs.carrier E.upstairs.carrier).inv := by
  apply (cancel_mono
    (chapter09_tensor_commutes_with_pullback
      (q ≫ chapter09DoubleSecond p) D.upstairs.carrier E.upstairs.carrier).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (chapter09_tensor_overlap_transport D E (q := q)).symm

private theorem chapter09_tensor_pullback_eqToIso_naturality
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s)
    {q q' : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T}
    (e : q = q') :
    (chapter09_tensor_commutes_with_pullback q
      D.upstairs.carrier E.upstairs.carrier).hom ≫
        chapter09SheafOperations.tensorMap
          (eqToIso (congrArg
            (fun q :
                LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T =>
              Chapter09PullbackModule q D.upstairs.carrier) e)).hom
          (eqToIso (congrArg
            (fun q :
                LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T =>
              Chapter09PullbackModule q E.upstairs.carrier) e)).hom =
      (eqToIso (congrArg
          (fun q :
              LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T =>
            Chapter09PullbackModule q
              (chapter09TensorModule D.upstairs.carrier E.upstairs.carrier)) e)).hom ≫
        (chapter09_tensor_commutes_with_pullback q'
          D.upstairs.carrier E.upstairs.carrier).hom := by
  cases e
  simp only [eqToIso_refl, Iso.refl_hom,
    Chapter09SheafOperationsData.tensorMap_id, Category.comp_id, Category.id_comp]

private theorem chapter09_tensor_pullback_eqToIso_conjugation
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s)
    {q q' : LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T}
    (e : q = q') :
    (chapter09_tensor_commutes_with_pullback q
      D.upstairs.carrier E.upstairs.carrier).inv ≫
        (eqToIso (congrArg
          (fun q :
              LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T =>
            Chapter09PullbackModule q
              (chapter09TensorModule D.upstairs.carrier E.upstairs.carrier)) e)).hom ≫
      (chapter09_tensor_commutes_with_pullback q'
        D.upstairs.carrier E.upstairs.carrier).hom =
    chapter09SheafOperations.tensorMap
      (eqToIso (congrArg
        (fun q :
            LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T =>
          Chapter09PullbackModule q D.upstairs.carrier) e)).hom
      (eqToIso (congrArg
        (fun q :
            LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T =>
          Chapter09PullbackModule q E.upstairs.carrier) e)).hom := by
  rw [← chapter09_tensor_pullback_eqToIso_naturality D E e]
  simp only [Iso.inv_hom_id_assoc]

private theorem chapter09_tensor_cocycle_of
    {C : Type v} [Category C]
    (P : C → C → C)
    (tm : ∀ {A A' B B' : C}, (A ⟶ A') → (B ⟶ B') →
      Quiver.Hom (P A B) (P A' B'))
    (tm_comp : ∀ {A A' A'' B B' B'' : C}
      (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B') (g' : B' ⟶ B''),
      tm (f ≫ f') (g ≫ g') = tm f g ≫ tm f' g')
    {DF12 DS12 DF23 DS23 DF13 DS13 EF12 ES12 EF23 ES23 EF13 ES13 : C}
    {TF12 TS12 TF23 TS23 TF13 TS13 : C}
    (d12 : DF12 ⟶ DS12) (d23 : DF23 ⟶ DS23) (d13 : DF13 ⟶ DS13)
    (fd2 : DS12 ⟶ DF23) (fd3 : DS23 ⟶ DS13) (fd1 : DF12 ⟶ DF13)
    (e12 : EF12 ⟶ ES12) (e23 : EF23 ⟶ ES23) (e13 : EF13 ⟶ ES13)
    (fe2 : ES12 ⟶ EF23) (fe3 : ES23 ⟶ ES13) (fe1 : EF12 ⟶ EF13)
    (t12F : TF12 ≅ P DF12 EF12) (t12S : TS12 ≅ P DS12 ES12)
    (t23F : TF23 ≅ P DF23 EF23) (t23S : TS23 ≅ P DS23 ES23)
    (t13F : TF13 ≅ P DF13 EF13) (t13S : TS13 ≅ P DS13 ES13)
    (c12 : TF12 ⟶ TS12) (c23 : TF23 ⟶ TS23) (c13 : TF13 ⟶ TS13)
    (f2 : TS12 ⟶ TF23) (f3 : TS23 ⟶ TS13) (f1 : TF12 ⟶ TF13)
    (hc12 : c12 = t12F.hom ≫ tm d12 e12 ≫ t12S.inv)
    (hc23 : c23 = t23F.hom ≫ tm d23 e23 ≫ t23S.inv)
    (hc13 : c13 = t13F.hom ≫ tm d13 e13 ≫ t13S.inv)
    (h2 : t12S.inv ≫ f2 ≫ t23F.hom = tm fd2 fe2)
    (h3 : t23S.inv ≫ f3 ≫ t13S.hom = tm fd3 fe3)
    (h1 : f1 ≫ t13F.hom = t12F.hom ≫ tm fd1 fe1)
    (hD : d12 ≫ fd2 ≫ d23 ≫ fd3 = fd1 ≫ d13)
    (hE : e12 ≫ fe2 ≫ e23 ≫ fe3 = fe1 ≫ e13) :
    c12 ≫ f2 ≫ c23 ≫ f3 = f1 ≫ c13 := by
  rw [hc12, hc23, hc13]
  apply (cancel_mono t13S.hom).1
  have h2tail := congrArg
    (fun k => k ≫ tm d23 e23 ≫ t23S.inv ≫ f3 ≫ t13S.hom) h2
  have h1tail := congrArg (fun k => k ≫ tm d13 e13) h1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h2tail h1tail ⊢
  rw [h2tail, h3, h1tail]
  rw [← tm_comp, ← tm_comp, ← tm_comp, ← tm_comp]
  rw [hD, hE]

theorem chapter09_tensor_preserves_descent
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) :
    chapter09TensorDescentCompatible D E := by
  sorry

theorem chapter09_dual_preserves_descent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) :
    chapter09DualDescentCompatible D := by
  sorry

theorem chapter09_symmetric_power_preserves_descent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (n : ℕ) (D : Chapter09ModuleDescentDatum p r) :
    chapter09SymmetricPowerDescentCompatible n D := by
  sorry

theorem chapter09_exterior_power_preserves_descent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (n : ℕ) (D : Chapter09ModuleDescentDatum p r) :
    chapter09ExteriorPowerDescentCompatible n D := by
  sorry

theorem chapter09_internal_hom_preserves_descent
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) :
    chapter09InternalHomDescentCompatible D E := by
  sorry

/- The overlap cocycles above, together with rank preservation, package the resulting
   finite locally free descent data.  Keeping these constructors explicit makes the route from
   functorial tensor operations to the effective vector-bundle theorem usable by later sections. -/
noncomputable def chapter09TensorDescentDatum
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) :
    Chapter09ModuleDescentDatum p (r * s) := by
  refine {
    nerve := D.nerve
    upstairs := {
      carrier := chapter09TensorModule D.upstairs.carrier E.upstairs.carrier
      locallyFree :=
        Chapter09SheafOperationsData.tensor_preserves_finite_locally_free
          chapter09SheafOperations D.upstairs.locallyFree E.upstairs.locallyFree }
    overlapIso := chapter09TensorOverlapIso D E
    cocycle := chapter09_tensor_preserves_descent D E }

noncomputable def chapter09DualDescentDatum
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) :
    Chapter09ModuleDescentDatum p r := by
  refine {
    nerve := D.nerve
    upstairs := {
      carrier := chapter09DualModule D.upstairs.carrier
      locallyFree :=
        Chapter09SheafOperationsData.dual_preserves_finite_locally_free
          chapter09SheafOperations D.upstairs.locallyFree }
    overlapIso := chapter09DualOverlapIso D
    cocycle := chapter09_dual_preserves_descent D }

noncomputable def chapter09SymmetricPowerDescentDatum
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ} (n : ℕ)
    (D : Chapter09ModuleDescentDatum p r) :
    Chapter09ModuleDescentDatum p (Nat.choose (r + n - 1) n) := by
  refine {
    nerve := D.nerve
    upstairs := {
      carrier := chapter09SymmetricPowerModule n D.upstairs.carrier
      locallyFree :=
        Chapter09SheafOperationsData.symmetricPower_preserves_finite_locally_free
          chapter09SheafOperations n r D.upstairs.locallyFree }
    overlapIso := chapter09SymmetricPowerOverlapIso n D
    cocycle := chapter09_symmetric_power_preserves_descent n D }

noncomputable def chapter09ExteriorPowerDescentDatum
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ} (n : ℕ)
    (D : Chapter09ModuleDescentDatum p r) :
    Chapter09ModuleDescentDatum p (Nat.choose r n) := by
  refine {
    nerve := D.nerve
    upstairs := {
      carrier := chapter09ExteriorPowerModule n D.upstairs.carrier
      locallyFree :=
        Chapter09SheafOperationsData.exteriorPower_preserves_finite_locally_free
          chapter09SheafOperations r n D.upstairs.locallyFree }
    overlapIso := chapter09ExteriorPowerOverlapIso n D
    cocycle := chapter09_exterior_power_preserves_descent n D }

noncomputable def chapter09InternalHomDescentDatum
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) :
    Chapter09ModuleDescentDatum p (r * s) := by
  refine {
    nerve := D.nerve
    upstairs := {
      carrier := chapter09InternalHomModule D.upstairs.carrier E.upstairs.carrier
      locallyFree :=
        Chapter09SheafOperationsData.internalHom_preserves_finite_locally_free
          chapter09SheafOperations D.upstairs.locallyFree E.upstairs.locallyFree }
    overlapIso := chapter09InternalHomOverlapIso D E
    cocycle := chapter09_internal_hom_preserves_descent D E }

/-! ### Bilinear forms -/

structure Chapter09BilinearForm
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (L : Chapter09LineBundle X) where
  map : chapter09TensorModule E.carrier E.carrier ⟶ L.carrier

def chapter09BilinearFormIsSymmetric
    {X : Scheme.{u}} {r : ℕ}
    {E : Chapter09VectorBundle X r} {L : Chapter09LineBundle X}
    (b : Chapter09BilinearForm E L) : Prop :=
  b.map = chapter09TensorSwap E.carrier E.carrier ≫ b.map

def chapter09BilinearFormIsSkewSymmetric
    {X : Scheme.{u}} {r : ℕ}
    {E : Chapter09VectorBundle X r} {L : Chapter09LineBundle X}
    (b : Chapter09BilinearForm E L) : Prop :=
  b.map = -(chapter09TensorSwap E.carrier E.carrier ≫ b.map)

/- An alternating form factors through the exterior square.  This is stronger than the displayed
skew-symmetry equation in characteristic two, so the two predicates are kept distinct. -/
def chapter09BilinearFormIsAlternating
    {X : Scheme.{u}} {r : ℕ}
    {E : Chapter09VectorBundle X r} {L : Chapter09LineBundle X}
    (b : Chapter09BilinearForm E L) : Prop :=
  ∃ c : chapter09ExteriorPowerModule 2 E.carrier ⟶ L.carrier,
    chapter09TensorToExteriorSquare E.carrier ≫ c = b.map

def chapter09BilinearFormIsPerfect
    {X : Scheme.{u}} {r : ℕ}
    {E : Chapter09VectorBundle X r} {L : Chapter09LineBundle X}
    (b : Chapter09BilinearForm E L) : Prop :=
  IsIso (chapter09BilinearFormAdjoint E L b.map)

/- The two predicates below are the overlap square for a form and the
comparison square identifying a descended form with its upstairs form. -/
def chapter09BilinearFormCompatibleWithDescent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs) : Prop :=
  (chapter09_tensor_commutes_with_pullback (chapter09DoubleFirst p)
      D.upstairs.carrier D.upstairs.carrier).inv ≫
      (Scheme.Modules.pullback (chapter09DoubleFirst p)).map b.map ≫
      L.overlapIso.hom =
    (chapter09TensorMapIso D.overlapIso D.overlapIso).hom ≫
      (chapter09_tensor_commutes_with_pullback (chapter09DoubleSecond p)
        D.upstairs.carrier D.upstairs.carrier).inv ≫
      (Scheme.Modules.pullback (chapter09DoubleSecond p)).map b.map

def chapter09BilinearFormComparisonCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs)
    (E : Chapter09VectorBundle S r) (K : Chapter09LineBundle S)
    (b₀ : Chapter09BilinearForm E K)
    (eE : (chapter09PullbackVectorBundle p E).carrier ≅ D.upstairs.carrier)
    (eK : (chapter09PullbackLineBundle p K).carrier ≅ L.upstairs.carrier) : Prop :=
  (chapter09_tensor_commutes_with_pullback p E.carrier E.carrier).hom ≫
      (chapter09TensorMapIso eE eE).hom ≫ b.map =
    (Scheme.Modules.pullback p).map b₀.map ≫ eK.hom

structure Chapter09BilinearFormDescentResult
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs) where
  downstairsVectorBundle : Chapter09VectorBundle S r
  downstairsLineBundle : Chapter09LineBundle S
  downstairsForm :
    Chapter09BilinearForm downstairsVectorBundle downstairsLineBundle
  comparisonVector :
    (chapter09PullbackVectorBundle p downstairsVectorBundle).carrier ≅ D.upstairs.carrier
  comparisonVectorCompatible :
    chapter09DescentComparisonCompatible D downstairsVectorBundle comparisonVector
  comparisonLine :
    (chapter09PullbackLineBundle p downstairsLineBundle).carrier ≅ L.upstairs.carrier
  comparisonLineCompatible :
    chapter09DescentComparisonCompatible L downstairsLineBundle comparisonLine
  compatible : chapter09BilinearFormComparisonCompatible D L b
    downstairsVectorBundle downstairsLineBundle downstairsForm comparisonVector comparisonLine

theorem chapter09_bilinear_form_effective_descent
    {S T : Scheme.{u}} {p : T ⟶ S} (hp : Chapter09FpqcCover p) {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs)
    (hb : chapter09BilinearFormCompatibleWithDescent D L b) :
    Nonempty (Chapter09BilinearFormDescentResult D L b) := by
  sorry

theorem chapter09_symmetric_bilinear_form_descends
    {S T : Scheme.{u}} {p : T ⟶ S} (hp : Chapter09FpqcCover p) {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs)
    (R : Chapter09BilinearFormDescentResult D L b)
    (hb : chapter09BilinearFormIsSymmetric b) :
    chapter09BilinearFormIsSymmetric R.downstairsForm := by
  sorry

theorem chapter09_alternating_bilinear_form_descends
    {S T : Scheme.{u}} {p : T ⟶ S} (hp : Chapter09FpqcCover p) {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs)
    (R : Chapter09BilinearFormDescentResult D L b)
    (hb : chapter09BilinearFormIsAlternating b) :
    chapter09BilinearFormIsAlternating R.downstairsForm := by
  sorry

theorem chapter09_perfect_bilinear_form_descends
    {S T : Scheme.{u}} {p : T ⟶ S} (hp : Chapter09FpqcCover p) {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (L : Chapter09LineBundleDescentDatum p)
    (b : Chapter09BilinearForm D.upstairs L.upstairs)
    (R : Chapter09BilinearFormDescentResult D L b)
    (hb : chapter09BilinearFormIsPerfect b) :
    chapter09BilinearFormIsPerfect R.downstairsForm := by
  sorry

/-! ### Sections -/

noncomputable def chapter09PullbackSection
    {S T : Scheme.{u}} (p : T ⟶ S) {r : ℕ}
    (E : Chapter09VectorBundle S r) (s : Chapter09Section E) :
    Chapter09Section (chapter09PullbackVectorBundle p E) :=
  (chapter09PullbackSectionData p E.carrier).map s

def chapter09SectionCompatibleWithDescent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) (s : Chapter09Section D.upstairs) : Prop :=
  SheafOfModules.sectionsMap D.overlapIso.hom
      ((chapter09PullbackSectionData (chapter09DoubleFirst p) D.upstairs.carrier).map s) =
    (chapter09PullbackSectionData (chapter09DoubleSecond p) D.upstairs.carrier).map s

theorem chapter09_section_descends_iff_overlap_compatibility
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) (s : Chapter09Section D.upstairs) :
    chapter09SectionCompatibleWithDescent D s ↔
      SheafOfModules.sectionsMap D.overlapIso.hom
          ((chapter09PullbackSectionData (chapter09DoubleFirst p)
            D.upstairs.carrier).map s) =
        (chapter09PullbackSectionData (chapter09DoubleSecond p)
          D.upstairs.carrier).map s := by
  rfl

def chapter09SectionMatchesDescentComparison
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (R : Chapter09VectorBundleDescentResult D)
    (s : Chapter09Section D.upstairs)
    (s₀ : Chapter09Section R.downstairs) : Prop :=
  SheafOfModules.sectionsMap R.comparison.hom
      ((chapter09PullbackSectionData p R.downstairs.carrier).map s₀) = s

theorem chapter09_section_effective_descent
    {S T : Scheme.{u}} {p : T ⟶ S} (hp : Chapter09FpqcCover p) {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (R : Chapter09VectorBundleDescentResult D)
    (s : Chapter09Section D.upstairs)
    (hs : chapter09SectionCompatibleWithDescent D s) :
    ∃! s₀ : Chapter09Section R.downstairs,
      chapter09SectionMatchesDescentComparison D R s s₀ := by
  sorry

theorem chapter09_section_effective_descent_iff
    {S T : Scheme.{u}} {p : T ⟶ S} (hp : Chapter09FpqcCover p) {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (R : Chapter09VectorBundleDescentResult D)
    (s : Chapter09Section D.upstairs) :
    (∃! s₀ : Chapter09Section R.downstairs,
      chapter09SectionMatchesDescentComparison D R s s₀) ↔
      chapter09SectionCompatibleWithDescent D s := by
  sorry

/-! ### Zero schemes and regular sections -/

noncomputable def chapter09SectionDualMap
    {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r)
    (s : Chapter09Section E) :
  chapter09DualModule E.carrier ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Chapter09SheafOperationsData.sectionDualMap chapter09SheafOperations E s).1

noncomputable def chapter09IdealSheafOfDualMap
    {X : Scheme.{u}} {M : X.Modules}
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) : Chapter09ClosedSubscheme X :=
  Chapter09SheafOperationsData.idealSheafOfMap chapter09SheafOperations φ

structure Chapter09ZeroScheme
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) where
  idealSheaf : Chapter09ClosedSubscheme X
  dualMap : chapter09DualModule E.carrier ⟶ SheafOfModules.unit X.ringCatSheaf
  idealSheaf_isGeneratedByDualMap :
    idealSheaf = chapter09IdealSheafOfDualMap dualMap
  isDefinedByDualMap : dualMap = chapter09SectionDualMap E s

theorem chapter09_zero_scheme_exists
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) :
    Nonempty (Chapter09ZeroScheme E s) := by
  refine ⟨{
    idealSheaf := chapter09IdealSheafOfDualMap (chapter09SectionDualMap E s)
    dualMap := chapter09SectionDualMap E s
    idealSheaf_isGeneratedByDualMap := rfl
    isDefinedByDualMap := rfl
  }⟩

noncomputable def chapter09ZeroScheme
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) :
    Chapter09ZeroScheme E s :=
  Classical.choice (chapter09_zero_scheme_exists E s)

noncomputable def chapter09ZeroSubscheme
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) : Scheme.{u} :=
  (chapter09ZeroScheme E s).idealSheaf.subscheme

noncomputable def chapter09ZeroSubschemeInclusion
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) :
    chapter09ZeroSubscheme E s ⟶ X :=
  (chapter09ZeroScheme E s).idealSheaf.subschemeι

theorem chapter09_zero_subscheme_isClosed
    {X : Scheme.{u}} {r : ℕ}
    (E : Chapter09VectorBundle X r) (s : Chapter09Section E) :
    IsClosedImmersion (chapter09ZeroSubschemeInclusion E s) := by
  exact (inferInstance : IsClosedImmersion
    (chapter09ZeroScheme E s).idealSheaf.subschemeι)

def chapter09ZeroSchemeCompatibleWithDescent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (s : Chapter09Section D.upstairs)
    (Z : Chapter09ZeroScheme D.upstairs s) : Prop :=
  chapter09SectionCompatibleWithDescent D s ∧
    Z.idealSheaf.comap (chapter09DoubleFirst p) =
      Z.idealSheaf.comap (chapter09DoubleSecond p)

/- The ideal of a zero scheme is generated by the dual evaluation map, so compatibility of the
section already forces compatibility of its zero scheme. -/
theorem chapter09_zero_scheme_compatibility_of_section_compatibility
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (s : Chapter09Section D.upstairs)
    (Z : Chapter09ZeroScheme D.upstairs s)
    (hs : chapter09SectionCompatibleWithDescent D s) :
    chapter09ZeroSchemeCompatibleWithDescent D s Z := by
  refine ⟨hs, ?_⟩
  rw [Z.idealSheaf_isGeneratedByDualMap]
  simp only [chapter09IdealSheafOfDualMap]
  rw [← Chapter09SheafOperationsData.idealSheafOfMap_pullback
    chapter09SheafOperations (chapter09DoubleFirst p) Z.dualMap,
    ← Chapter09SheafOperationsData.idealSheafOfMap_pullback
    chapter09SheafOperations (chapter09DoubleSecond p) Z.dualMap]
  let q₁ := chapter09DoubleFirst p
  let q₂ := chapter09DoubleSecond p
  let e₁ := Chapter09SheafOperationsData.dualPullback chapter09SheafOperations q₁
    D.upstairs.carrier D.upstairs.locallyFree
  let e₂ := Chapter09SheafOperationsData.dualPullback chapter09SheafOperations q₂
    D.upstairs.carrier D.upstairs.locallyFree
  let s₁ : chapter09SheafOperations.dual
      (Chapter09PullbackModule q₁ D.upstairs.carrier) ⟶
      SheafOfModules.unit (Chapter09DoubleOverlap p).ringCatSheaf :=
    (Chapter09SheafOperationsData.sectionDualMap chapter09SheafOperations
      (chapter09PullbackVectorBundle q₁ D.upstairs)
      ((chapter09PullbackSectionData q₁ D.upstairs.carrier).map s)).1
  let s₂ : chapter09SheafOperations.dual
      (Chapter09PullbackModule q₂ D.upstairs.carrier) ⟶
      SheafOfModules.unit (Chapter09DoubleOverlap p).ringCatSheaf :=
    (Chapter09SheafOperationsData.sectionDualMap chapter09SheafOperations
      (chapter09PullbackVectorBundle q₂ D.upstairs)
      ((chapter09PullbackSectionData q₂ D.upstairs.carrier).map s)).1
  let d : chapter09SheafOperations.dual
      (Chapter09PullbackModule q₂ D.upstairs.carrier) ⟶
      chapter09SheafOperations.dual
        (Chapter09PullbackModule q₁ D.upstairs.carrier) :=
    Chapter09SheafOperationsData.dualMap chapter09SheafOperations D.overlapIso.hom
  let e : Chapter09PullbackModule q₂ (chapter09DualModule D.upstairs.carrier) ≅
      Chapter09PullbackModule q₁ (chapter09DualModule D.upstairs.carrier) :=
    e₂ ≪≫ chapter09DualMapIso D.overlapIso ≪≫ e₁.symm
  have hφ₁ :
      chapter09PullbackMapToUnit q₁
          (M := chapter09DualModule D.upstairs.carrier) Z.dualMap =
        e₁.hom ≫ s₁ := by
    rw [Z.isDefinedByDualMap]
    simpa [q₁, e₁, s₁, chapter09SectionDualMap, chapter09DualModule] using
      (Chapter09SheafOperationsData.sectionDualMap_pullback
        chapter09SheafOperations q₁ D.upstairs s)
  have hφ₂ :
      chapter09PullbackMapToUnit q₂
          (M := chapter09DualModule D.upstairs.carrier) Z.dualMap =
        e₂.hom ≫ s₂ := by
    rw [Z.isDefinedByDualMap]
    simpa [q₂, e₂, s₂, chapter09SectionDualMap, chapter09DualModule] using
      (Chapter09SheafOperationsData.sectionDualMap_pullback
        chapter09SheafOperations q₂ D.upstairs s)
  have hsec : s₂ = d ≫ s₁ := by
    dsimp [s₁, s₂]
    rw [← hs]
    exact (Chapter09SheafOperationsData.sectionDualMap_natural
      chapter09SheafOperations (chapter09PullbackVectorBundle q₁ D.upstairs)
        (chapter09PullbackVectorBundle q₂ D.upstairs) D.overlapIso
        ((chapter09PullbackSectionData q₁ D.upstairs.carrier).map s)).symm
  have hdual :
      (chapter09DualMapIso D.overlapIso).hom = d := by
    change
      ((Chapter09SheafOperationsData.dualMapIso chapter09SheafOperations D.overlapIso).1).hom =
        Chapter09SheafOperationsData.dualMap chapter09SheafOperations D.overlapIso.hom
    exact (Chapter09SheafOperationsData.dualMapIso chapter09SheafOperations D.overlapIso).2
  have hmap :
      e.hom ≫ chapter09PullbackMapToUnit q₁
          (M := chapter09DualModule D.upstairs.carrier) Z.dualMap =
        chapter09PullbackMapToUnit q₂
          (M := chapter09DualModule D.upstairs.carrier) Z.dualMap := by
    rw [hφ₁, hφ₂]
    change ((e₂.hom ≫ (chapter09DualMapIso D.overlapIso).hom ≫ e₁.inv) ≫
        e₁.hom ≫ s₁) = e₂.hom ≫ s₂
    rw [hsec, hdual]
    have h₁ :
        e₂.hom ≫ d ≫ e₁.inv = (e₂.hom ≫ d) ≫ e₁.inv :=
      (Category.assoc e₂.hom d e₁.inv).symm
    have h₂ :
        ((e₂.hom ≫ d) ≫ e₁.inv) ≫ e₁.hom ≫ s₁ =
          (e₂.hom ≫ d) ≫ (e₁.inv ≫ e₁.hom ≫ s₁) :=
      Category.assoc (e₂.hom ≫ d) e₁.inv (e₁.hom ≫ s₁)
    calc
      (e₂.hom ≫ d ≫ e₁.inv) ≫ e₁.hom ≫ s₁ =
          ((e₂.hom ≫ d) ≫ e₁.inv) ≫ e₁.hom ≫ s₁ := by
        exact congrArg (fun f => f ≫ e₁.hom ≫ s₁) h₁
      _ = (e₂.hom ≫ d) ≫ (e₁.inv ≫ e₁.hom ≫ s₁) := h₂
      _ = (e₂.hom ≫ d) ≫ s₁ := by
        exact congrArg (fun f => (e₂.hom ≫ d) ≫ f) (e₁.inv_hom_id_assoc s₁)
      _ = e₂.hom ≫ d ≫ s₁ := Category.assoc e₂.hom d s₁
  calc
    chapter09SheafOperations.idealSheafOfMap
        (chapter09PullbackMapToUnit q₁
          (M := chapter09DualModule D.upstairs.carrier) Z.dualMap) =
      chapter09SheafOperations.idealSheafOfMap
        (e.hom ≫ chapter09PullbackMapToUnit q₁
          (M := chapter09DualModule D.upstairs.carrier) Z.dualMap) :=
      (Chapter09SheafOperationsData.idealSheafOfMap_iso chapter09SheafOperations e
        (chapter09PullbackMapToUnit q₁
          (M := chapter09DualModule D.upstairs.carrier) Z.dualMap)).symm
    _ = chapter09SheafOperations.idealSheafOfMap
        (chapter09PullbackMapToUnit q₂
          (M := chapter09DualModule D.upstairs.carrier) Z.dualMap) := by
      rw [hmap]

def chapter09ZeroSchemeMatchesDescent
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (R : Chapter09VectorBundleDescentResult D)
    (s : Chapter09Section D.upstairs)
    (s₀ : Chapter09Section R.downstairs)
    (Z : Chapter09ZeroScheme D.upstairs s)
    (Z₀ : Chapter09ZeroScheme R.downstairs s₀) : Prop := by
  exact Z.idealSheaf = Z₀.idealSheaf.comap p

theorem chapter09_zero_scheme_effective_descent
    {S T : Scheme.{u}} {p : T ⟶ S} (hp : Chapter09FpqcCover p) {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (R : Chapter09VectorBundleDescentResult D)
    (s : Chapter09Section D.upstairs)
    (hs : chapter09SectionCompatibleWithDescent D s)
    (Z : Chapter09ZeroScheme D.upstairs s) :
    ∃ s₀ : Chapter09Section R.downstairs,
      ∃ Z₀ : Chapter09ZeroScheme R.downstairs s₀,
        chapter09SectionMatchesDescentComparison D R s s₀ ∧
          chapter09ZeroSchemeMatchesDescent D R s s₀ Z Z₀ := by
  rcases chapter09_section_effective_descent hp D R s hs with ⟨s₀, hs₀, _⟩
  let Z₀ := chapter09ZeroScheme R.downstairs s₀
  refine ⟨s₀, Z₀, hs₀, ?_⟩
  let φ := chapter09SectionDualMap
    (chapter09PullbackVectorBundle p R.downstairs)
    (chapter09PullbackSection p R.downstairs s₀)
  let dcomp : chapter09DualModule D.upstairs.carrier ⟶
      chapter09DualModule (Chapter09PullbackModule p R.downstairs.carrier) :=
    Chapter09SheafOperationsData.dualMap chapter09SheafOperations R.comparison.hom
  let a := Chapter09SheafOperationsData.dualPullback chapter09SheafOperations p
    R.downstairs.carrier R.downstairs.locallyFree
  have hdual : Z.dualMap = dcomp ≫ φ := by
    rw [Z.isDefinedByDualMap]
    dsimp [dcomp, φ, chapter09SectionDualMap, chapter09PullbackSection]
    dsimp [chapter09SectionMatchesDescentComparison] at hs₀
    rw [← hs₀]
    exact (Chapter09SheafOperationsData.sectionDualMap_natural
      chapter09SheafOperations (chapter09PullbackVectorBundle p R.downstairs)
        D.upstairs R.comparison
        ((chapter09PullbackSectionData p R.downstairs.carrier).map s₀)).symm
  have hcomp : (chapter09DualMapIso R.comparison).hom = dcomp := by
    change
      ((Chapter09SheafOperationsData.dualMapIso chapter09SheafOperations R.comparison).1).hom =
        Chapter09SheafOperationsData.dualMap chapter09SheafOperations R.comparison.hom
    exact (Chapter09SheafOperationsData.dualMapIso chapter09SheafOperations R.comparison).2
  have hφpull :
      chapter09PullbackMapToUnit p
          (M := chapter09DualModule R.downstairs.carrier)
          (chapter09SectionDualMap R.downstairs s₀) =
        a.hom ≫ φ := by
    simpa [a, φ, chapter09SectionDualMap, chapter09DualModule,
      chapter09PullbackSection] using
      (Chapter09SheafOperationsData.sectionDualMap_pullback
        chapter09SheafOperations p R.downstairs s₀)
  calc
    Z.idealSheaf = chapter09IdealSheafOfDualMap Z.dualMap :=
      Z.idealSheaf_isGeneratedByDualMap
    _ = chapter09IdealSheafOfDualMap (dcomp ≫ φ) := by rw [hdual]
    _ = chapter09SheafOperations.idealSheafOfMap φ := by
      change chapter09SheafOperations.idealSheafOfMap (dcomp ≫ φ) =
        chapter09SheafOperations.idealSheafOfMap φ
      rw [← hcomp]
      exact Chapter09SheafOperationsData.idealSheafOfMap_iso
        chapter09SheafOperations (chapter09DualMapIso R.comparison) φ
    _ = chapter09SheafOperations.idealSheafOfMap
        (chapter09PullbackMapToUnit p
          (M := chapter09DualModule R.downstairs.carrier)
          (chapter09SectionDualMap R.downstairs s₀)) := by
      rw [hφpull]
      exact (Chapter09SheafOperationsData.idealSheafOfMap_iso
        chapter09SheafOperations a φ).symm
    _ = Z₀.idealSheaf.comap p := by
      rw [Chapter09SheafOperationsData.idealSheafOfMap_pullback
        chapter09SheafOperations p (chapter09SectionDualMap R.downstairs s₀)]
      rw [Z₀.idealSheaf_isGeneratedByDualMap, Z₀.isDefinedByDualMap]
      simp only [chapter09IdealSheafOfDualMap]

theorem chapter09_regular_section_reflected_by_fpqc
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    (L : Chapter09LineBundle S) (s : Chapter09Section L) :
    chapter09RegularSection L s ↔
      chapter09RegularSection (chapter09PullbackLineBundle p L)
        (chapter09PullbackSection p L s) := by
  sorry

/-! ### Effective Cartier divisors -/

structure Chapter09EffectiveCartierDivisor (X : Scheme.{u}) where
  lineBundle : Chapter09LineBundle X
  sectionValue : Chapter09Section lineBundle
  regular : chapter09RegularSection lineBundle sectionValue
  zeroScheme : Chapter09ZeroScheme lineBundle sectionValue

noncomputable def chapter09CartierSectionTransport
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter09LineBundleDescentDatum p)
    (d : Chapter09EffectiveCartierDivisor T)
    (e : D.upstairs.carrier ≅ d.lineBundle.carrier) :
    Chapter09Section D.upstairs :=
  SheafOfModules.sectionsMap e.inv d.sectionValue

structure Chapter09EffectiveCartierDivisorDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) where
  lineBundleDatum : Chapter09LineBundleDescentDatum p
  upstairsDivisor : Chapter09EffectiveCartierDivisor T
  line_carrier_agrees : lineBundleDatum.upstairs.carrier ≅ upstairsDivisor.lineBundle.carrier
  section_compatible :
    chapter09SectionCompatibleWithDescent lineBundleDatum
      (chapter09CartierSectionTransport lineBundleDatum upstairsDivisor
        line_carrier_agrees)

noncomputable def chapter09CartierComparisonIso
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter09EffectiveCartierDivisorDescentDatum p)
    (R : Chapter09VectorBundleDescentResult D.lineBundleDatum)
    (d₀ : Chapter09EffectiveCartierDivisor S)
    (e₀ : d₀.lineBundle.carrier ≅ R.downstairs.carrier) :
    Chapter09PullbackModule p d₀.lineBundle.carrier ≅
      D.upstairsDivisor.lineBundle.carrier :=
  (Scheme.Modules.pullback p).mapIso e₀ ≪≫
    R.comparison ≪≫ D.line_carrier_agrees

def chapter09EffectiveCartierDivisorMatches
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter09EffectiveCartierDivisorDescentDatum p)
    (R : Chapter09VectorBundleDescentResult D.lineBundleDatum)
    (d₀ : Chapter09EffectiveCartierDivisor S) : Prop :=
  ∃ e₀ : d₀.lineBundle.carrier ≅ R.downstairs.carrier,
    SheafOfModules.sectionsMap
        (chapter09CartierComparisonIso D R d₀ e₀).hom
        ((chapter09PullbackSectionData p d₀.lineBundle.carrier).map
          d₀.sectionValue) = D.upstairsDivisor.sectionValue ∧
      D.upstairsDivisor.zeroScheme.idealSheaf =
        d₀.zeroScheme.idealSheaf.comap p

theorem chapter09_effective_cartier_divisor_effective_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    (D : Chapter09EffectiveCartierDivisorDescentDatum p)
    (R : Chapter09VectorBundleDescentResult D.lineBundleDatum) :
    ∃ d₀ : Chapter09EffectiveCartierDivisor S,
      chapter09EffectiveCartierDivisorMatches D R d₀ := by
  sorry

end
end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09
