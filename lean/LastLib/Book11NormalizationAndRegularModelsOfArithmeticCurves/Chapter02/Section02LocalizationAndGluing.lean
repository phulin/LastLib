import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02.Section01AffineConstruction

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open scoped AlgebraicGeometry BigOperators

universe u v

noncomputable section

/-! ### 2.2 Localization and gluing -/

/-- The affine closure used on an open of the target of a morphism. -/
def chapter02AffineIntegralClosure {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    letI := (f.app U).hom.toAlgebra
    Subalgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  letI := (f.app U).hom.toAlgebra
  exact integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)

theorem chapter02_affineIntegralClosure_mem_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (x : Γ(X, f ⁻¹ᵁ U)) :
    letI := (f.app U).hom.toAlgebra
    x ∈ chapter02AffineIntegralClosure f U ↔ IsIntegral Γ(Y, U) x := by
  letI := (f.app U).hom.toAlgebra
  exact mem_integralClosure_iff

/-- Taking integral closure commutes with an arbitrary localization. -/
theorem chapter02_integralClosure_localization
    {R S Rf Sf : Type u} [CommRing R] [CommRing S] [CommRing Rf] [CommRing Sf]
    [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf] [Algebra R Sf]
    [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
    (M : Submonoid R) [IsLocalization M Rf]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf]
    [Algebra (integralClosure R S) (integralClosure Rf Sf)]
    [IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf]
    [IsScalarTower R (integralClosure R S) (integralClosure Rf Sf)] :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R S) M)
      (integralClosure Rf Sf) := by
  exact IsLocalization.integralClosure M

/-- The principal-open form of the localization bridge used on overlaps. -/
theorem chapter02_integralClosure_localization_away
    {R S Rf Sf : Type u} [CommRing R] [CommRing S] [CommRing Rf] [CommRing Sf]
    [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf] [Algebra R Sf]
    [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
    (r : R) [IsLocalization.Away r Rf]
    [IsLocalization.Away (algebraMap R S r) Sf]
    [Algebra (integralClosure R S) (integralClosure Rf Sf)]
    [IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf]
    [IsScalarTower R (integralClosure R S) (integralClosure Rf Sf)] :
    IsLocalization.Away (algebraMap R (integralClosure R S) r)
      (integralClosure Rf Sf) := by
  exact IsLocalization.Away.integralClosure r

/-- The relative normalization supplied by Mathlib's affine gluing construction. -/
abbrev Chapter02RelativeNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : Scheme :=
  f.normalization

/-- The integral map from the relative normalization to the target. -/
abbrev chapter02NormalizationMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : f.normalization ⟶ Y :=
  f.fromNormalization

/-- The dominant map from the source into the relative normalization. -/
abbrev chapter02NormalizationDominantMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : X ⟶ f.normalization :=
  f.toNormalization

noncomputable def chapter02NormalizationOpenCover {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : f.normalization.OpenCover :=
  f.normalizationOpenCover

noncomputable def chapter02NormalizationSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≅
      .of (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
  f.normalizationObjIso hU

theorem chapter02_normalization_is_integral_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    IsIntegralHom (chapter02NormalizationMap f) ∧
      IsAffineHom (chapter02NormalizationMap f) := by
  constructor <;> infer_instance

theorem chapter02_normalization_factorization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter02NormalizationDominantMap f ≫ chapter02NormalizationMap f = f := by
  exact f.toNormalization_fromNormalization

theorem chapter02_normalization_is_finite_iff_local_closures {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    IsFinite (chapter02NormalizationMap f) ↔
      ∀ (U : Y.Opens), IsAffineOpen U →
        letI := (f.app U).hom.toAlgebra
        Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
  sorry

/-- A finite extension of the function field is presented to the relative normalization API
through the generic point map `Spec L → Spec K(X) → X`. -/
def chapter02FunctionFieldExtensionMap (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L] :
    Spec (CommRingCat.of L) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
    X.fromSpecStalk (genericPoint X)

abbrev Chapter02FieldExtensionNormalization (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X L)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X L)] : Scheme :=
  (chapter02FunctionFieldExtensionMap X L).normalization

abbrev chapter02FieldExtensionNormalizationMap (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X L)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X L)] :
    Chapter02FieldExtensionNormalization X L ⟶ X :=
  (chapter02FunctionFieldExtensionMap X L).fromNormalization

/-- The absolute normalization is the relative normalization of the identity. -/
abbrev Chapter02AbsoluteNormalization (X : Scheme.{u})
    [QuasiCompact (𝟙 X)] [QuasiSeparated (𝟙 X)] : Scheme :=
  (𝟙 X).normalization

abbrev chapter02AbsoluteNormalizationMap (X : Scheme.{u})
    [QuasiCompact (𝟙 X)] [QuasiSeparated (𝟙 X)] :
    Chapter02AbsoluteNormalization X ⟶ X :=
  (𝟙 X).fromNormalization

theorem chapter02_fieldExtension_normalization_is_integral_affine
    (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L]
    [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [QuasiCompact (chapter02FunctionFieldExtensionMap X L)]
    [QuasiSeparated (chapter02FunctionFieldExtensionMap X L)] :
    IsIntegralHom (chapter02FieldExtensionNormalizationMap X L) ∧
      IsAffineHom (chapter02FieldExtensionNormalizationMap X L) := by
  constructor <;> infer_instance

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter02
