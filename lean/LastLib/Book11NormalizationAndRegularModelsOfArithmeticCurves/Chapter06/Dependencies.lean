import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open scoped AlgebraicGeometry

universe u v

/-!
Shared interfaces for Chapter 6.  The base is presented by a Dedekind domain so
that its generic field is the canonical `FractionRing`; all geometric maps use
the pinned scheme-theoretic pullback, image, and normalization constructions.
The few book-facing predicates which are not global Mathlib classes are kept as
explicit fields rather than being hidden in an overly strong typeclass.
-/

abbrev Chapter06BaseScheme (R : Type u) [CommRing R] [IsDedekindDomain R] : Scheme.{u} :=
  Spec (.of R)

abbrev Chapter06BaseField (R : Type u) [CommRing R] [IsDedekindDomain R] :=
  FractionRing R

abbrev chapter06GenericBaseMap (R : Type u) [CommRing R] [IsDedekindDomain R] :
    Spec (.of (FractionRing R)) ⟶ Chapter06BaseScheme R :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))

abbrev chapter06GenericFiber {X S : Scheme.{u}} (f : X ⟶ S)
    {K : Type u} [Field K] (η : Spec (.of K) ⟶ S) : Scheme.{u} :=
  pullback f η

abbrev chapter06GenericFiberToSource {X S : Scheme.{u}} (f : X ⟶ S)
    {K : Type u} [Field K] (η : Spec (.of K) ⟶ S) :
    chapter06GenericFiber f η ⟶ X :=
  pullback.fst f η

abbrev chapter06GenericFiberToField {X S : Scheme.{u}} (f : X ⟶ S)
    {K : Type u} [Field K] (η : Spec (.of K) ⟶ S) :
    chapter06GenericFiber f η ⟶ Spec (.of K) :=
  pullback.snd f η

/-! ### Curves over the generic field -/

structure Chapter06SmoothProjectiveCurve
    (R : Type u) [CommRing R] [IsDedekindDomain R] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (.of (FractionRing R))
  projective : chapter04Projective structureMap
  proper : IsProper structureMap
  quasiCompact : QuasiCompact structureMap
  smooth : Smooth structureMap
  geometricallyConnected : GeometricallyConnected structureMap
  integral : IsIntegral carrier
  curve : Chapter09RelativeCurve structureMap

instance (C : Chapter06SmoothProjectiveCurve R) : IsIntegral C.carrier := C.integral

instance (C : Chapter06SmoothProjectiveCurve R) : IsProper C.structureMap := C.proper

instance (C : Chapter06SmoothProjectiveCurve R) : QuasiCompact C.structureMap := C.quasiCompact

instance (C : Chapter06SmoothProjectiveCurve R) : Smooth C.structureMap := C.smooth

instance (C : Chapter06SmoothProjectiveCurve R) :
    GeometricallyConnected C.structureMap := C.geometricallyConnected

structure Chapter06ProjectiveEmbedding
    (C : Chapter06SmoothProjectiveCurve R) where
  dimension : ℕ
  map : C.carrier ⟶ chapter02ProjectiveSpace (Spec (.of (FractionRing R))) dimension
  closedImmersion : IsClosedImmersion map
  over : map ≫ chapter02ProjectiveSpaceProjection
      (Spec (.of (FractionRing R))) dimension = C.structureMap

theorem chapter06_projective_embedding_of_very_ampleness
    (C : Chapter06SmoothProjectiveCurve R)
    (L : Chapter04LineBundle C.carrier)
    (hL : chapter04VeryAmple C.structureMap L) :
    Nonempty (Chapter06ProjectiveEmbedding C) := by
  sorry

/-! A finite homogeneous list is the coefficient-level object used in the
spreading-out paragraph. -/

structure Chapter06HomogeneousEquations
    (A : Type u) [CommRing A] (N : ℕ) where
  index : Type u
  finiteIndex : Finite index
  degree : index → ℕ
  equation : index → MvPolynomial (Fin (N + 1)) A
  homogeneous : ∀ i, (equation i).IsHomogeneous (degree i)

abbrev chapter06PolynomialGenericMap
    (R : Type u) [CommRing R] [IsDedekindDomain R] (N : ℕ) :
    MvPolynomial (Fin (N + 1)) R →+* MvPolynomial (Fin (N + 1)) (FractionRing R) :=
  MvPolynomial.map (algebraMap R (FractionRing R))

structure Chapter06ClearedHomogeneousEquations
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (E : Chapter06HomogeneousEquations (FractionRing R) N) where
  base : Chapter06HomogeneousEquations R N
  scalar : E.index → FractionRing R
  scalar_ne_zero : ∀ i, scalar i ≠ 0
  generic_equation :
    ∀ i, chapter06PolynomialGenericMap R N (base.equation i) =
      scalar i * E.equation i

/-! ### Generic-fiber presentations and models -/

structure Chapter06GenericFiberIdentification
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    {X : Scheme.{u}} (f : X ⟶ Chapter06BaseScheme R) where
  iso : pullback f (chapter06GenericBaseMap R) ≅ C.carrier
  over : iso.hom ≫ C.structureMap = pullback.snd f (chapter06GenericBaseMap R)

def chapter06IsNormal (X : Scheme.{u}) : Prop :=
  ∀ (U : X.affineOpens) (_ : Nonempty U),
    IsDomain Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U)

theorem chapter06_isNormal_iff_affine_sections (X : Scheme.{u}) :
    chapter06IsNormal X ↔
      ∀ (U : X.affineOpens) (_ : Nonempty U),
        IsDomain Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) :=
  Iff.rfl

structure Chapter06Model
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Chapter06BaseScheme R
  projective : chapter04Projective structureMap
  proper : IsProper structureMap
  locallyOfFiniteType : LocallyOfFiniteType structureMap
  flat : Flat structureMap
  integral : IsIntegral carrier
  genericFiber : Chapter06GenericFiberIdentification R C structureMap

instance (X : Chapter06Model R C) : IsIntegral X.carrier := X.integral

instance (X : Chapter06Model R C) : IsProper X.structureMap := X.proper

instance (X : Chapter06Model R C) : QuasiCompact X.structureMap := by
  sorry

structure Chapter06NormalModel
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R)
    extends Chapter06Model R C where
  normal : chapter06IsNormal carrier

instance (X : Chapter06NormalModel R C) : IsIntegral X.carrier := X.integral

instance (X : Chapter06NormalModel R C) : IsProper X.structureMap := X.proper

abbrev chapter06ModelRestriction
    (X : Chapter06Model R C) (U : (Chapter06BaseScheme R).Opens) :
    (X.carrier ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  X.structureMap ∣_ U

structure Chapter06SmoothProjectiveOpenModel
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (C : Chapter06SmoothProjectiveCurve R) where
  open : (Chapter06BaseScheme R).Opens
  open_nonempty : open ≠ ⊥
  complement_finite : Set.Finite ((open : Set (Chapter06BaseScheme R))ᶜ)
  carrier : Scheme.{u}
  structureMap : carrier ⟶ open.toScheme
  projective : chapter04Projective structureMap
  smooth : Smooth structureMap
  genericMap : Spec (.of (FractionRing R)) ⟶ open.toScheme
  genericMap_over : genericMap ≫ open.ι = chapter06GenericBaseMap R
  genericFiber : Chapter06GenericFiberIdentification R C
    (structureMap ≫ open.ι)

instance (M : Chapter06SmoothProjectiveOpenModel R C) : Smooth M.structureMap := M.smooth

/-! ### Closure and normalization data -/

structure Chapter06ClosureDatum
    (C : Chapter06SmoothProjectiveCurve R) where
  dimension : ℕ
  genericAmbientIso :
    pullback
        (chapter02ProjectiveSpaceProjection (Spec (.of R)) dimension)
        (chapter06GenericBaseMap R) ≅
      chapter02ProjectiveSpace (Spec (.of (FractionRing R))) dimension
  genericEmbedding :
    C.carrier ⟶ chapter02ProjectiveSpace (Spec (.of (FractionRing R))) dimension
  genericEmbedding_closedImmersion : IsClosedImmersion genericEmbedding
  genericEmbedding_over :
    genericEmbedding ≫ chapter02ProjectiveSpaceProjection
        (Spec (.of (FractionRing R))) dimension = C.structureMap

noncomputable def chapter06GenericEmbeddingIntoBaseAmbient
    (D : Chapter06ClosureDatum C) :
    C.carrier ⟶ chapter02ProjectiveSpace (Spec (.of R)) D.dimension :=
  D.genericEmbedding ≫ D.genericAmbientIso.inv ≫
    pullback.fst
      (chapter02ProjectiveSpaceProjection (Spec (.of R)) D.dimension)
      (chapter06GenericBaseMap R)

noncomputable def chapter06SchematicClosure
    (D : Chapter06ClosureDatum C) : Scheme.{u} :=
  (chapter06GenericEmbeddingIntoBaseAmbient D).image

abbrev chapter06SchematicClosureEmbedding
    (D : Chapter06ClosureDatum C) :
    chapter06SchematicClosure D ⟶ chapter02ProjectiveSpace (Spec (.of R)) D.dimension :=
  (chapter06GenericEmbeddingIntoBaseAmbient D).imageι

noncomputable def chapter06SchematicClosureToAmbient
    (D : Chapter06ClosureDatum C) :
    C.carrier ⟶ chapter06SchematicClosure D :=
  (chapter06GenericEmbeddingIntoBaseAmbient D).toImage

abbrev chapter06SchematicClosureStructureMap
    (D : Chapter06ClosureDatum C) :
    chapter06SchematicClosure D ⟶ Chapter06BaseScheme R :=
  chapter06SchematicClosureEmbedding D ≫
    chapter02ProjectiveSpaceProjection (Spec (.of R)) D.dimension

def chapter06ClosedSubschemeContains
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y) : Prop :=
  ∃ g : X ⟶ Z, g ≫ i = f

theorem chapter06_schematicClosure_closedImmersion
    (D : Chapter06ClosureDatum C) :
    IsClosedImmersion (chapter06SchematicClosureEmbedding D) := by
  infer_instance

/-! ### Affine saturation -/

abbrev chapter06GenericFiberRing
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :=
  A ⊗[R] FractionRing R

noncomputable def chapter06GenericFiberRingMap
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    A →+* chapter06GenericFiberRing R A :=
  (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] FractionRing R).toRingHom

abbrev chapter06SaturationIdeal
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] : Ideal A :=
  RingHom.ker (chapter06GenericFiberRingMap R A)

abbrev chapter06SaturatedAffineRing
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :=
  A ⧸ chapter06SaturationIdeal R A

noncomputable def chapter06SaturationQuotientMap
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    A →+* chapter06SaturatedAffineRing R A :=
  Ideal.Quotient.mk _

noncomputable def chapter06SaturationGenericMap
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    chapter06SaturatedAffineRing R A →+*
      chapter06GenericFiberRing R A :=
  RingHom.kerLift (chapter06GenericFiberRingMap R A)

def chapter06PowerTorsion
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] (π : R) (a : A) : Prop :=
  ∃ n : ℕ, (π ^ n) • a = 0

/-! ### Birationality and the normalization input -/

def chapter06Birational {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ U : X.Opens, ∃ V : Y.Opens,
    Dense (U : Set X) ∧ Dense (V : Set Y) ∧
      ∃ e : U.toScheme ≅ V.toScheme, e.hom ≫ V.ι = U.ι ≫ f

def chapter06Modification {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsProper f ∧ chapter06Birational f

noncomputable def chapter06GenericPointMap
    (X : Scheme.{u}) [IsIntegral X] : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib API supplies relative
normalization and integral morphisms, but not the excellence theorem making
normalization finite over an excellent Dedekind base.  This class records only
that missing finite-normalization interface. -/
class Chapter06ExcellentDedekindBase
    (R : Type u) [CommRing R] [IsDedekindDomain R] : Prop where
  finite_normalization :
    ∀ (X : Scheme.{u}) (f : X ⟶ Chapter06BaseScheme R)
      [IsIntegral X] (hft : LocallyOfFiniteType f)
      [QuasiCompact f] [QuasiSeparated f]
      (hqc : QuasiCompact (chapter06GenericPointMap X))
      (hqs : QuasiSeparated (chapter06GenericPointMap X)),
      letI := hqc
      letI := hqs
      IsFinite (chapter06GenericPointMap X).fromNormalization

noncomputable def chapter06RelativeNormalization
    {X : Scheme.{u}} (hqc : QuasiCompact (chapter06GenericPointMap X))
    (hqs : QuasiSeparated (chapter06GenericPointMap X)) [IsIntegral X] : Scheme.{u} := by
  letI := hqc
  letI := hqs
  exact (chapter06GenericPointMap X).normalization

noncomputable def chapter06RelativeNormalizationMap
    {X : Scheme.{u}} (hqc : QuasiCompact (chapter06GenericPointMap X))
    (hqs : QuasiSeparated (chapter06GenericPointMap X)) [IsIntegral X] :
    chapter06RelativeNormalization hqc hqs ⟶ X := by
  letI := hqc
  letI := hqs
  exact (chapter06GenericPointMap X).fromNormalization

noncomputable def chapter06RelativeNormalizationToNormalization
    {X : Scheme.{u}} (hqc : QuasiCompact (chapter06GenericPointMap X))
    (hqs : QuasiSeparated (chapter06GenericPointMap X)) [IsIntegral X] :
    Spec X.functionField ⟶ chapter06RelativeNormalization hqc hqs := by
  letI := hqc
  letI := hqs
  exact (chapter06GenericPointMap X).toNormalization

theorem chapter06_relativeNormalization_factorization
    {X : Scheme.{u}} [IsIntegral X]
    (hqc : QuasiCompact (chapter06GenericPointMap X))
    (hqs : QuasiSeparated (chapter06GenericPointMap X)) :
    chapter06RelativeNormalizationToNormalization hqc hqs ≫
        chapter06RelativeNormalizationMap hqc hqs = chapter06GenericPointMap X := by
  letI := hqc
  letI := hqs
  exact Scheme.Hom.toNormalization_fromNormalization _

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06
