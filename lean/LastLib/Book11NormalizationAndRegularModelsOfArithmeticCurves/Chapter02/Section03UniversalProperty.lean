import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02.Section02LocalizationAndGluing

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open scoped AlgebraicGeometry BigOperators

universe u v

noncomputable section

/-! ### 2.3 The universal property -/

/-- An embedding of a finite extension into a second field over the same base field. -/
structure Chapter02FunctionFieldEmbedding (F L K : Type u) [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] where
  toAlgHom : L →ₐ[F] K
  injective : Function.Injective toAlgHom

instance chapter02FunctionFieldEmbeddingCoe
    (F L K : Type u) [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K] : Coe (Chapter02FunctionFieldEmbedding F L K) (L →ₐ[F] K) :=
  ⟨Chapter02FunctionFieldEmbedding.toAlgHom⟩

theorem chapter02_functionFieldEmbedding_injective
    (F L K : Type u) [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra F K]
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
  sorry

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

/-- The uniqueness clause for maps from the normalization into an affine integral factor. -/
theorem chapter02_normalizationDesc_unique
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : T ⟶ Y) [IsAffineHom g]
    (a b : f.normalization ⟶ T)
    (ha : f.toNormalization ≫ a = f.toNormalization ≫ b)
    (ha_over : a ≫ g = f.fromNormalization)
    (hb_over : b ≫ g = f.fromNormalization) : a = b := by
  exact f.normalization.hom_ext a b g ha ha_over hb_over

/-- Relative normalization is terminal among integral affine factorizations of a qcqs morphism. -/
theorem chapter02_normalization_universal_property
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]
    [IsAffineHom f₂] (H : f = f₁ ≫ f₂) :
    ∃! g : f.normalization ⟶ T,
      f.toNormalization ≫ g = f₁ ∧ g ≫ f₂ = f.fromNormalization := by
  sorry

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
    [Algebra F L] [Algebra F K] [Algebra R K] where
  embedding : Chapter02FunctionFieldEmbedding F L K
  integral_elements_land :
    ∀ z : L, IsIntegral F z → ∃ r : R, algebraMap R K r = embedding.toAlgHom z

theorem chapter02_normalSourceFactorization_embedding_is_injective
    (F L K R : Type u) [Field F] [Field L] [Field K] [CommRing R]
    [Algebra F L] [Algebra F K] [Algebra R K]
    (D : Chapter02NormalSourceFactorization F L K R) :
    Function.Injective (D.embedding.toAlgHom : L → K) :=
  D.embedding.injective

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
