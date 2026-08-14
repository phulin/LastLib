import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.DedekindDomain.Basic
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section01TheAbsoluteAndRelativeSettings
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Section01FromACurveOverAFieldToASurface
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03.Core
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Section01TheResolutionTheoremInTheRequiredSetting

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter03
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
open scoped AlgebraicGeometry

universe u v

/-! ## Shared interfaces for regular proper models -/

structure Chapter09ExcellentDedekindBase
    (S : Scheme.{u}) (K : Type u) [Field K]
    extends Chapter01DedekindBase S K where
  excellent : Chapter01ExcellentScheme S

theorem chapter09_excellentDedekindBase_is_dedekind
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K) :
    Chapter01DedekindScheme S :=
  B.dedekind

theorem chapter09_excellentDedekindBase_is_noetherian
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K) :
    IsNoetherian S :=
  B.dedekind.1

theorem chapter09_excellentDedekindBase_is_normal
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K) :
    Chapter01NormalScheme S := by
  sorry

structure Chapter09SmoothProperCurveOverField
    (K : Type u) [Field K]
    extends Chapter01ProperCurveOverField K where
  smooth : Smooth structureMap
  geometricallyConnected : GeometricallyConnected structureMap

structure Chapter09SmoothProjectiveCurve
    (K : Type u) [Field K]
    extends Chapter09SmoothProperCurveOverField K where
  projective : Chapter01ProjectiveMorphism structureMap

theorem chapter09_smoothProjectiveCurve_is_proper
    {K : Type u} [Field K]
    (C : Chapter09SmoothProjectiveCurve K) :
    IsProper C.structureMap :=
  C.proper

instance {K : Type u} [Field K]
    (C : Chapter09SmoothProjectiveCurve K) : IsProper C.structureMap := C.proper

instance {K : Type u} [Field K]
    (C : Chapter09SmoothProjectiveCurve K) : LocallyOfFiniteType C.structureMap :=
  C.finiteType

instance {K : Type u} [Field K]
    (C : Chapter09SmoothProjectiveCurve K) : Smooth C.structureMap := C.smooth

instance {K : Type u} [Field K]
    (C : Chapter09SmoothProjectiveCurve K) : GeometricallyConnected C.structureMap :=
  C.geometricallyConnected

theorem chapter09_smoothProjectiveCurve_is_integral
    {K : Type u} [Field K]
    (C : Chapter09SmoothProjectiveCurve K) :
    IsIntegral C.carrier := by
  sorry

instance {K : Type u} [Field K]
    (C : Chapter09SmoothProjectiveCurve K) : IsIntegral C.carrier :=
  chapter09_smoothProjectiveCurve_is_integral C

structure Chapter09ProjectiveModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  flat : Flat structureMap
  finiteType : Chapter01FiniteType structureMap
  projective : Chapter01ProjectiveMorphism structureMap
  proper : IsProper structureMap
  integral : IsIntegral carrier
  genericFiberIso : pullback structureMap B.genericPointMap ≅ C.carrier
  genericFiberIso_over :
    genericFiberIso.hom ≫ C.structureMap = pullback.snd structureMap B.genericPointMap

instance {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K)
    (X : Chapter09ProjectiveModel B C) :
    IsProper X.structureMap :=
  X.proper

instance {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K)
    (X : Chapter09ProjectiveModel B C) :
    IsIntegral X.carrier :=
  X.integral

noncomputable def chapter09ProjectiveModelToChapter01Model
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09ProjectiveModel B C) :
    Chapter01Model B.toChapter01DedekindBase.toChapter01GenericPointData C.structureMap :=
  { carrier := X.carrier
    structureMap := X.structureMap
    flat := X.flat
    finiteType := X.finiteType
    genericFiberIso := X.genericFiberIso
    genericFiberIso_over := X.genericFiberIso_over }

theorem chapter09ProjectiveModel_toChapter01Model_projective
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09ProjectiveModel B C) :
    Chapter01ProjectiveModel (chapter09ProjectiveModelToChapter01Model X) :=
  X.projective

theorem chapter09ProjectiveModel_toChapter01Model_proper
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09ProjectiveModel B C) :
    Chapter01ProperModel (chapter09ProjectiveModelToChapter01Model X) :=
  X.proper

structure Chapter09RegularProjectiveModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K)
    extends Chapter09ProjectiveModel B C where
  regular : Chapter01RegularScheme carrier

instance {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K)
    (X : Chapter09RegularProjectiveModel B C) :
    IsIntegral X.carrier :=
  X.integral

instance {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K)
    (X : Chapter09RegularProjectiveModel B C) :
    IsProper X.structureMap :=
  X.proper

theorem chapter09RegularProjectiveModel_toChapter01Model_regular
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C) :
    Chapter01RegularModel
      (chapter09ProjectiveModelToChapter01Model X.toChapter09ProjectiveModel) :=
  X.regular

theorem chapter09_regularProjectiveModel_is_projective
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C) :
    Chapter01ProjectiveMorphism X.structureMap :=
  X.projective

structure Chapter09RegularProjectiveOpenModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K)
    (U : S.Opens) where
  open_nonempty : U ≠ ⊥
  carrier : Scheme.{u}
  structureMap : carrier ⟶ U.toScheme
  flat : Flat structureMap
  finiteType : Chapter01FiniteType structureMap
  projective : Chapter01ProjectiveMorphism structureMap
  proper : IsProper structureMap
  integral : IsIntegral carrier
  regular : Chapter01RegularScheme carrier
  genericMap : Spec (CommRingCat.of K) ⟶ U.toScheme
  genericMap_over : genericMap ≫ U.ι = B.genericPointMap
  genericFiberIso : pullback structureMap genericMap ≅ C.carrier
  genericFiberIso_over :
    genericFiberIso.hom ≫ C.structureMap = pullback.snd structureMap genericMap

def Chapter09RegularSurface (X : Scheme.{u}) : Prop :=
  Chapter04RegularScheme X ∧ Chapter04NoetherianSurface X

structure Chapter09ModelRestrictionIdentification
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C)
    (U : S.Opens)
    (M : Chapter09RegularProjectiveOpenModel B C U) where
  iso : (X.structureMap ⁻¹ᵁ U).toScheme ≅ M.carrier
  «over» : iso.hom ≫ M.structureMap = X.structureMap ∣_ U

abbrev chapter09ModelRestrictionMap
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C) (U : S.Opens) :
    (X.structureMap ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  X.structureMap ∣_ U

theorem chapter09_modelRestrictionIdentification_over
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {U : S.Opens}
    {M : Chapter09RegularProjectiveOpenModel B C U}
    (I : Chapter09ModelRestrictionIdentification X U M) :
    I.iso.hom ≫ M.structureMap = chapter09ModelRestrictionMap X U :=
  I.over

/-! A section is kept as a morphism with its splitting equation. -/

structure Chapter09Section {X S : Scheme.{u}} (f : X ⟶ S) where
  map : S ⟶ X
  «over» : map ≫ f = 𝟙 S

@[ext]
theorem chapter09_section_ext
    {X S : Scheme.{u}} {f : X ⟶ S}
    {σ τ : Chapter09Section f} (h : σ.map = τ.map) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

abbrev Chapter09KPoint
    {K : Type u} [Field K] (C : Chapter09SmoothProjectiveCurve K) :=
  Spec (CommRingCat.of K) ⟶ C.carrier

noncomputable def chapter09KPointToModel
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C)
    (P : Chapter09KPoint C) : Spec (CommRingCat.of K) ⟶ X.carrier :=
  P ≫ X.genericFiberIso.inv ≫ pullback.fst X.structureMap B.genericPointMap

structure Chapter09SectionExtension
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C)
    (P : Chapter09KPoint C) where
  «section» : Chapter09Section X.structureMap
  generic_agreement :
    B.genericPointMap ≫ section.map = chapter09KPointToModel X P

@[ext]
theorem chapter09_sectionExtension_ext
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {P : Chapter09KPoint C}
    {σ τ : Chapter09SectionExtension X P}
    (h : σ.section.map = τ.section.map) : σ = τ := by
  sorry

/-! Closed points are paired with an explicit residue-field presentation. -/

abbrev chapter09FieldExtensionMap
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap K L)).op

structure Chapter09ClosedPointOverK
    {K : Type u} [Field K]
    (C : Chapter09SmoothProjectiveCurve K)
    (L : Type u) [Field L] [Algebra K L] where
  point : C.carrier
  closed : IsClosed ({point} : Set C.carrier)
  finiteOverK : FiniteDimensional K L
  residueIso : CommRingCat.of L ≅ C.carrier.residueField point
  residueIso_over :
    chapter09FieldExtensionMap K L =
      Scheme.Spec.map residueIso.inv.op ≫ C.carrier.fromSpecResidueField point ≫
        C.structureMap

noncomputable def chapter09ClosedPointLPoint
    {K : Type u} [Field K]
    {C : Chapter09SmoothProjectiveCurve K}
    {L : Type u} [Field L] [Algebra K L]
    (P : Chapter09ClosedPointOverK C L) :
    Spec (CommRingCat.of L) ⟶ C.carrier :=
  Scheme.Spec.map P.residueIso.inv.op ≫ C.carrier.fromSpecResidueField P.point

theorem chapter09_closedPoint_field_map_compatibility
    {K : Type u} [Field K]
    {C : Chapter09SmoothProjectiveCurve K}
    {L : Type u} [Field L] [Algebra K L]
    (P : Chapter09ClosedPointOverK C L) :
    chapter09FieldExtensionMap K L =
      chapter09ClosedPointLPoint P ≫ C.structureMap := by
  exact P.residueIso_over

theorem chapter09_closedPoint_residueField_is_finite
    {K : Type u} [Field K]
    {C : Chapter09SmoothProjectiveCurve K}
    {L : Type u} [Field L] [Algebra K L]
    (P : Chapter09ClosedPointOverK C L) :
    FiniteDimensional K L :=
  P.finiteOverK

/- LOCAL_DEPENDENCY_GUESS: the pinned scheme API does not package the normalization of an
   arbitrary excellent Dedekind scheme in a finite field extension as one named construction.
   The following record exposes the canonical finite integral normal map, its affine
   normalization charts through Chapter 03, and the chosen generic-field map. -/
structure Chapter09BaseNormalization
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    (B : Chapter09ExcellentDedekindBase S K) where
  carrier : Scheme.{u}
  map : carrier ⟶ S
  finiteExtension : FiniteDimensional K L
  finite : IsFinite map
  normalization : Chapter03NormalizationMap map
  genericMap : Spec (CommRingCat.of L) ⟶ carrier
  genericMap_over :
    genericMap ≫ map = chapter09FieldExtensionMap K L ≫ B.genericPointMap

theorem chapter09_baseNormalization_is_normal
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    (N : Chapter09BaseNormalization (L := L) B) :
    Chapter03NormalScheme N.carrier :=
  N.normalization.normal

structure Chapter09ResidueSectionExtension
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C)
    (P : Chapter09ClosedPointOverK C L)
    (N : Chapter09BaseNormalization (L := L) B) where
  «section» : N.carrier ⟶ pullback X.structureMap N.map
  section_over : «section» ≫ pullback.snd X.structureMap N.map = 𝟙 N.carrier
  map : N.carrier ⟶ X.carrier
  map_eq : «section» ≫ pullback.fst X.structureMap N.map = map
  «over» : map ≫ X.structureMap = N.map
  generic_agreement :
    N.genericMap ≫ map =
      chapter09ClosedPointLPoint P ≫ X.genericFiberIso.inv ≫
        pullback.fst X.structureMap B.genericPointMap

noncomputable def chapter09HorizontalClosure
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {P : Chapter09ClosedPointOverK C L}
    {N : Chapter09BaseNormalization (L := L) B}
    (H : Chapter09ResidueSectionExtension X P N) : Scheme.{u} :=
  H.map.image

abbrev chapter09HorizontalClosureEmbedding
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {P : Chapter09ClosedPointOverK C L}
    {N : Chapter09BaseNormalization (L := L) B}
    (H : Chapter09ResidueSectionExtension X P N) :
    chapter09HorizontalClosure H ⟶ X.carrier :=
  H.map.imageι

abbrev chapter09HorizontalClosureMap
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {P : Chapter09ClosedPointOverK C L}
    {N : Chapter09BaseNormalization (L := L) B}
    (H : Chapter09ResidueSectionExtension X P N) :
    N.carrier ⟶ chapter09HorizontalClosure H :=
  H.map.toImage

theorem chapter09_horizontalClosure_factorization
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {P : Chapter09ClosedPointOverK C L}
    {N : Chapter09BaseNormalization (L := L) B}
    (H : Chapter09ResidueSectionExtension X P N) :
    chapter09HorizontalClosureMap H ≫ chapter09HorizontalClosureEmbedding H = H.map := by
  exact H.map.toImage_imageι

def Chapter09HorizontalClosureIsHorizontal
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {P : Chapter09ClosedPointOverK C L}
    {N : Chapter09BaseNormalization (L := L) B}
    (H : Chapter09ResidueSectionExtension X P N) : Prop :=
  ∃ g : Spec (CommRingCat.of L) ⟶ chapter09HorizontalClosure H,
    g ≫ chapter09HorizontalClosureEmbedding H ≫ X.structureMap =
      chapter09FieldExtensionMap K L ≫ B.genericPointMap

theorem chapter09_horizontalClosure_is_horizontal
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {P : Chapter09ClosedPointOverK C L}
    {N : Chapter09BaseNormalization (L := L) B}
    (H : Chapter09ResidueSectionExtension X P N) :
    Chapter09HorizontalClosureIsHorizontal H := by
  sorry

def Chapter09HorizontalClosureNormalizationStatement
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {P : Chapter09ClosedPointOverK C L}
    {N : Chapter09BaseNormalization (L := L) B}
    (H : Chapter09ResidueSectionExtension X P N) : Prop :=
  IsFinite (chapter09HorizontalClosureMap H) ∧
    Chapter03NormalizationMap (chapter09HorizontalClosureMap H)

def Chapter09HorizontalClosureIsNonregular
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    {X : Chapter09RegularProjectiveModel B C}
    {P : Chapter09ClosedPointOverK C L}
    {N : Chapter09BaseNormalization (L := L) B}
    (H : Chapter09ResidueSectionExtension X P N) : Prop :=
  ¬ Chapter01RegularScheme (chapter09HorizontalClosure H)

def Chapter09HorizontalClosureCanBeNonregular
    {S : Scheme.{u}} {K L : Type u} [Field K] [Field L] [Algebra K L]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X : Chapter09RegularProjectiveModel B C)
    (P : Chapter09ClosedPointOverK C L)
    (N : Chapter09BaseNormalization (L := L) B) : Prop :=
  ∃ H : Chapter09ResidueSectionExtension X P N,
    Chapter09HorizontalClosureIsNonregular H

/-! A regular-section interface records the effective Cartier equation and its support. -/

structure Chapter09SectionCartierData
    {X S : Scheme.{u}} {f : X ⟶ S}
    (σ : Chapter09Section f) where
  ideal : X.IdealSheafData
  locallyRegularPrincipal : chapter04IsEffectiveCartierIdeal ideal
  imageIso : ideal.subscheme ≅ σ.map.image
  imageIso_over : imageIso.hom ≫ σ.map.imageι = ideal.subschemeι
  support_eq : (ideal.support : Set X) = Set.range σ.map

def chapter09SectionLocalParameter
    {X S : Scheme.{u}} {f : X ⟶ S}
    {σ : Chapter09Section f}
    (D : Chapter09SectionCartierData σ) (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ a : Γ(X, U),
    D.ideal.ideal U = Ideal.span ({a} : Set Γ(X, U)) ∧ IsRegular a

/-! The maps in a common domination are bundled with their generic-fiber identity. -/

structure Chapter09ModelMapOverBase
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (X Y : Chapter09ProjectiveModel B C) where
  map : X.carrier ⟶ Y.carrier
  «over» : map ≫ Y.structureMap = X.structureMap
  genericFiberMap :
    pullback X.structureMap B.genericPointMap ⟶
      pullback Y.structureMap B.genericPointMap
  genericFiberMap_source :
    genericFiberMap ≫ pullback.fst Y.structureMap B.genericPointMap =
      pullback.fst X.structureMap B.genericPointMap ≫ map
  genericFiberMap_base :
    genericFiberMap ≫ pullback.snd Y.structureMap B.genericPointMap =
      pullback.snd X.structureMap B.genericPointMap
  genericFiber_is_identity :
    genericFiberMap ≫ Y.genericFiberIso.hom = X.genericFiberIso.hom

structure Chapter09FiniteProjectiveModelFamily
    {S : Scheme.{u}} {K : Type u} [Field K]
    (B : Chapter09ExcellentDedekindBase S K)
    (C : Chapter09SmoothProjectiveCurve K) where
  index : Type u
  finite : Finite index
  model : index → Chapter09ProjectiveModel B C

structure Chapter09RegularDomination
    {S : Scheme.{u}} {K : Type u} [Field K]
    {B : Chapter09ExcellentDedekindBase S K}
    {C : Chapter09SmoothProjectiveCurve K}
    (F : Chapter09FiniteProjectiveModelFamily B C) where
  model : Chapter09RegularProjectiveModel B C
  map : ∀ i, Chapter09ModelMapOverBase model.toChapter09ProjectiveModel (F.model i)
  proper : ∀ i, IsProper (map i).map
  projective : ∀ i, Chapter01ProjectiveMorphism (map i).map

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter09
