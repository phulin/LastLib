import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02.Section02LocalizationAndGluing

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open scoped AlgebraicGeometry BigOperators

universe u v

noncomputable section

/-! ### 2.3 The universal property -/

/-- An embedding of a finite extension into a second field over the same base field. -/
structure Chapter02FunctionFieldEmbedding (F L K : Type u) [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] [FiniteDimensional F L] where
  toAlgHom : L →ₐ[F] K
  injective : Function.Injective toAlgHom

instance chapter02FunctionFieldEmbeddingCoe
    (F L K : Type u) [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] [FiniteDimensional F L] :
    Coe (Chapter02FunctionFieldEmbedding F L K) (L →ₐ[F] K) :=
  ⟨Chapter02FunctionFieldEmbedding.toAlgHom⟩

theorem chapter02_functionFieldEmbedding_injective
    (F L K : Type u) [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] [FiniteDimensional F L]
    (e : Chapter02FunctionFieldEmbedding F L K) :
    Function.Injective (e.toAlgHom : L → K) :=
  e.injective

/-- The local algebra fact used in the proof of the universal property. -/
theorem chapter02_normal_stalk_is_integrallyClosed (Y : Scheme.{u}) [IsIntegral Y]
    [IsLocallyNoetherian Y] [Chapter02Normal Y] (y : Y) :
    IsIntegrallyClosed (Y.presheaf.stalk y) :=
  Chapter02Normal.integrallyClosed_stalk y

/-- A ring-level form of the local step: integral elements of a fraction field land in a
normal local ring. -/
theorem chapter02_integral_element_lands_in_integrallyClosed_ring
    (R : Type u) [CommRing R] (z : FractionRing R)
    (hR : IsIntegrallyClosed R) (hz : IsIntegral R z) :
    ∃ r : R, algebraMap R (FractionRing R) r = z := by
  exact hR.algebraMap_eq_of_integral hz

/-- The canonical factorization map supplied by the relative-normalization universal property. -/
noncomputable def chapter02NormalizationDesc
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]
    (H : f = f₁ ≫ f₂) : f.normalization ⟶ T :=
  f.normalizationDesc f₁ f₂ H

theorem chapter02_normalizationDesc_factor
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]
    (H : f = f₁ ≫ f₂) :
    f.toNormalization ≫ chapter02NormalizationDesc f f₁ f₂ H = f₁ := by
  exact f.toNormalization_normalizationDesc f₁ f₂ H

theorem chapter02_normalizationDesc_over
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]
    (H : f = f₁ ≫ f₂) :
    chapter02NormalizationDesc f f₁ f₂ H ≫ f₂ = f.fromNormalization := by
  exact f.normalizationDesc_comp f₁ f₂ H

/-- The uniqueness clause for maps out of the normalization, among maps over a separated target. -/
theorem chapter02_normalizationDesc_unique
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (f₂ : T ⟶ Y) [IsSeparated f₂]
    (a b : f.normalization ⟶ T)
    (ha : a ≫ f₂ = f.fromNormalization)
    (hb : b ≫ f₂ = f.fromNormalization)
    (hab : f.toNormalization ≫ a = f.toNormalization ≫ b) : a = b := by
  let X' : Over Y := Over.mk f
  let N' : Over Y := Over.mk f.fromNormalization
  let T' : Over Y := Over.mk f₂
  have : IsSeparated T'.hom := by
    change IsSeparated f₂
    infer_instance
  let a' : N' ⟶ T' := Over.homMk a ha
  let b' : N' ⟶ T' := Over.homMk b hb
  let t' : X' ⟶ N' :=
    Over.homMk f.toNormalization f.toNormalization_fromNormalization
  have ht : t' ≫ a' = t' ≫ b' := by
    apply Over.OverMorphism.ext
    simpa [t', a', b', T', N', X', Over.comp_left] using hab
  let l' : X' ⟶ equalizer a' b' := equalizer.lift t' ht
  let hli : l' ≫ equalizer.ι a' b' = t' := equalizer.lift_ι t' ht
  let i : (equalizer a' b').left ⟶ f.normalization := (equalizer.ι a' b').left
  have hl : l'.left ≫ i = f.toNormalization := by
    have h := congrArg (fun q => q.left) hli
    change l'.left ≫ (equalizer.ι a' b').left = t'.left at h
    simpa [i, N', X', t'] using h
  have : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  have hkerle : i.ker ≤ (l'.left ≫ i).ker :=
    Scheme.Hom.le_ker_comp l'.left i
  have hkeri : i.ker = ⊥ := by
    apply le_antisymm
    · simpa [hl] using hkerle
    · exact bot_le
  let : IsIso i := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hkeri
  have hcond : i ≫ a = i ≫ b := by
    have h := congrArg (fun q => q.left) (equalizer.condition a' b')
    simpa [i, a', b', T', Over.comp_left] using h
  rw [← cancel_epi i]
  exact hcond

private theorem chapter02_affine_sections_integrallyClosed
    (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [Chapter02Normal Y]
    (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    IsIntegrallyClosed Γ(Y, V) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p hp hpm
  let y : PrimeSpectrum Γ(Y, V) := ⟨p, hpm.isPrime⟩
  let x : V := hV.isoSpec.inv y
  have hxy : hV.primeIdealOf x = y := by
    change hV.isoSpec.hom (hV.isoSpec.inv y) = y
    have h := congrArg (fun q => q y) hV.isoSpec.inv_hom_id
    change hV.isoSpec.hom (hV.isoSpec.inv y) = y at h
    simpa using h
  have hloc := hV.isLocalization_stalk x
  rw [hxy] at hloc
  exact (Chapter02Normal.integrallyClosed_stalk x.1).of_equiv
    (IsLocalization.algEquiv p.primeCompl
      (Y.presheaf.stalk x.1) (Localization.AtPrime p)).toRingEquiv

/-- Relative normalization is terminal among integral affine factorizations of a qcqs morphism. -/
theorem chapter02_normalization_universal_property
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]
    (H : f = f₁ ≫ f₂) :
    ∃! g : f.normalization ⟶ T,
      f.toNormalization ≫ g = f₁ ∧ g ≫ f₂ = f.fromNormalization := by
  refine ⟨chapter02NormalizationDesc f f₁ f₂ H, ?_, ?_⟩
  · exact ⟨chapter02_normalizationDesc_factor f f₁ f₂ H,
      chapter02_normalizationDesc_over f f₁ f₂ H⟩
  · intro g hg
    exact chapter02_normalizationDesc_unique f f₂ g
      (chapter02NormalizationDesc f f₁ f₂ H) hg.2
      (chapter02_normalizationDesc_over f f₁ f₂ H)
      (hg.1.trans (chapter02_normalizationDesc_factor f f₁ f₂ H).symm)

/-- Generic-point data for the normal-source specialization of the finite-field-extension
normalization theorem.  The displayed equality is the compatibility with the given dominant map.
It is the scheme-level form of fixing an `F`-embedding into the source function field. -/
structure Chapter02NormalSourceGenericFactorization
    (X Y : Scheme.{u}) (L : Type u) [IsIntegral X] [IsIntegral Y]
    [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X L)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X L)] where
  map : Y ⟶ X
  dominant : IsDominant map
  generic : Spec (CommRingCat.of Y.functionField) ⟶
    Chapter02FieldExtensionNormalization X L
  generic_over :
    generic ≫ chapter02FieldExtensionNormalizationMap X L =
      Y.fromSpecStalk (genericPoint Y) ≫ map

private theorem chapter02_normal_source_generic_preimage_affine
    (X Y : Scheme.{u}) (L : Type u) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Chapter02Normal Y]
    [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X L)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X L)]
    (D : Chapter02NormalSourceGenericFactorization X Y L)
    (U : X.affineOpens) (V : Y.affineOpens) [Nonempty V]
    (hVU : (V : Y.Opens) ≤ D.map ⁻¹ᵁ (U : X.Opens)) :
    D.generic ⁻¹ᵁ
        (chapter02FieldExtensionNormalizationMap X L ⁻¹ᵁ (U : X.Opens)) = ⊤ := by
  apply le_antisymm le_top
  intro z hz
  have hz' : z = genericPoint (Spec (CommRingCat.of Y.functionField)) :=
    Subsingleton.elim _ _
  subst z
  have hpoint :
      Y.fromSpecStalk (genericPoint Y)
          (⊥ : PrimeSpectrum Y.functionField) = genericPoint Y := by
    have hbot : (⊥ : PrimeSpectrum Y.functionField) =
        IsLocalRing.closedPoint Y.functionField := by
      apply PrimeSpectrum.ext
      change (⊥ : Ideal Y.functionField) = IsLocalRing.maximalIdeal Y.functionField
      rw [IsLocalRing.maximalIdeal_eq_bot]
    rw [hbot]
    exact Scheme.fromSpecStalk_closedPoint (X := Y) (x := genericPoint Y)
  have hgenericY : genericPoint Y ∈ (V : Y.Opens) := by
    exact ((genericPoint_spec Y).mem_open_set_iff V.1.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hmapU : D.map (genericPoint Y) ∈ (U : X.Opens) := by
    exact hVU hgenericY
  have hgeneric :
      chapter02FieldExtensionNormalizationMap X L
          (D.generic (genericPoint (Spec (CommRingCat.of Y.functionField)))) =
        D.map (genericPoint Y) := by
    have h := congrArg (fun q => q (genericPoint (Spec (CommRingCat.of Y.functionField))))
      D.generic_over
    change chapter02FieldExtensionNormalizationMap X L
        (D.generic (genericPoint (Spec (CommRingCat.of Y.functionField)))) =
      D.map (Y.fromSpecStalk (genericPoint Y)
        (genericPoint (Spec (CommRingCat.of Y.functionField)))) at h
    simpa [hpoint] using h
  change D.generic (genericPoint (Spec (CommRingCat.of Y.functionField))) ∈
    chapter02FieldExtensionNormalizationMap X L ⁻¹ᵁ (U : X.Opens)
  change chapter02FieldExtensionNormalizationMap X L
      (D.generic (genericPoint (Spec (CommRingCat.of Y.functionField)))) ∈ (U : X.Opens)
  rw [hgeneric]
  exact hmapU

private noncomputable def chapter02_normal_source_generic_ringMap
    (X Y : Scheme.{u}) (L : Type u) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Chapter02Normal Y]
    [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X L)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X L)]
    (D : Chapter02NormalSourceGenericFactorization X Y L)
    (U : X.affineOpens) (V : Y.affineOpens) [Nonempty V]
    (hVU : (V : Y.Opens) ≤ D.map ⁻¹ᵁ (U : X.Opens)) :
    chapter02AffineIntegralClosure (chapter02FunctionFieldExtensionMap X L) U.1 →+* Y.functionField := by
  letI := ((chapter02FunctionFieldExtensionMap X L).app U.1).hom.toAlgebra
  let hpre := chapter02_normal_source_generic_preimage_affine X Y L D U V hVU
  let φCat : CommRingCat.of (chapter02AffineIntegralClosure
      (chapter02FunctionFieldExtensionMap X L) U.1) ⟶ CommRingCat.of Y.functionField :=
    ((chapter02FunctionFieldExtensionMap X L).normalizationObjIso U.2).inv ≫
    D.generic.appLE
      (chapter02FieldExtensionNormalizationMap X L ⁻¹ᵁ (U : X.Opens)) ⊤
      (by simp [hpre]) ≫
    (Scheme.ΓSpecIso (CommRingCat.of Y.functionField)).hom
  exact φCat.hom

private theorem chapter02_normal_source_generic_ringMap_base
    (X Y : Scheme.{u}) (L : Type u) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Chapter02Normal Y]
    [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X L)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X L)]
    (D : Chapter02NormalSourceGenericFactorization X Y L)
    (U : X.affineOpens) (V : Y.affineOpens) [Nonempty V]
    (hVU : (V : Y.Opens) ≤ D.map ⁻¹ᵁ (U : X.Opens)) :
    (algebraMap Γ(Y, V) Y.functionField).comp (D.map.appLE U.1 V.1 hVU).hom =
      (chapter02_normal_source_generic_ringMap X Y L D U V hVU).comp
        (algebraMap Γ(X, U) (chapter02AffineIntegralClosure
          (chapter02FunctionFieldExtensionMap X L) U.1)) := by
  sorry

theorem chapter02_normalization_universal_property_normal_source
    (X Y : Scheme.{u}) (L : Type u) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Chapter02Normal Y]
    [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X L)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X L)]
    (D : Chapter02NormalSourceGenericFactorization X Y L) :
    ∃! g : Y ⟶ Chapter02FieldExtensionNormalization X L,
      g ≫ chapter02FieldExtensionNormalizationMap X L = D.map ∧
        Y.fromSpecStalk (genericPoint Y) ≫ g = D.generic := by
  sorry

/-!
The source's normal-source theorem is the field-extension specialization of the
factorization API above: on an affine chart, the fixed `F`-embedding sends each
integral element into every normal stalk, and the resulting affine maps glue.
The embedding type and the stalk landing lemma are exposed separately so this
specialization can be connected to a future scheme-level function-field map API.
-/

structure Chapter02NormalSourceFactorization
    (F L K R : Type u) [Field F] [Field L] [Field K] [CommRing R]
    [Algebra F L] [Algebra F K] [Algebra R K] [FiniteDimensional F L] where
  embedding : Chapter02FunctionFieldEmbedding F L K
  integral_elements_land :
    ∀ z : L, IsIntegral R (embedding.toAlgHom z) →
      ∃ r : R, algebraMap R K r = embedding.toAlgHom z

theorem chapter02_normalSourceFactorization_embedding_is_injective
    (F L K R : Type u) [Field F] [Field L] [Field K] [CommRing R]
    [Algebra F L] [Algebra F K] [Algebra R K] [FiniteDimensional F L]
    (D : Chapter02NormalSourceFactorization F L K R) :
    Function.Injective (D.embedding.toAlgHom : L → K) :=
  D.embedding.injective

theorem chapter02_normalSourceFactorization_integral_elements_land_unique
    (F L K R : Type u) [Field F] [Field L] [Field K] [CommRing R]
    [Algebra F L] [Algebra F K] [Algebra R K] [FiniteDimensional F L]
    (D : Chapter02NormalSourceFactorization F L K R)
    (hR : Function.Injective (algebraMap R K)) :
    ∀ z : L, IsIntegral R (D.embedding.toAlgHom z) →
      ∃! r : R, algebraMap R K r = D.embedding.toAlgHom z := by
  intro z hz
  rcases D.integral_elements_land z hz with ⟨r, hr⟩
  refine ⟨r, hr, ?_⟩
  intro r' hr'
  apply hR
  exact hr'.trans hr.symm

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
