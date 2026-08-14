import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Section03DescentOfAmplenessAndProjectivity
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Section04NormsAndAddition
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section01CoveringFamilies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section02SingleCoversAndAffineReduction
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section04SeparatednessAndQuasiCompactness

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Opposite
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open scoped AlgebraicGeometry TensorProduct

universe u v w

/-! The aliases below keep the synthesis chapter on the book-facing interfaces already
    established in Chapters 2 and 11 and in the earlier positivity chapters. -/

abbrev FpqcMorphism {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Scheme.IsFpqcMorphism p

abbrev FpqcMorphismProperty : MorphismProperty Scheme :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.SchemeDescent.FpqcProperty

abbrev Book8LineBundle (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.LineBundle X

abbrev Book8IsAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : Book8LineBundle X) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsAmple f L

abbrev Book8IsProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsProjectiveMorphism f

abbrev Book8IsQuasiProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsQuasiProjectiveMorphism f

abbrev Book8RelativeImmersionWitness {X S : Scheme.{u}} (f : X ⟶ S) :=
  RelativeImmersionWitness f

abbrev Book8RelativeClosedImmersionWitness {X S : Scheme.{u}} (f : X ⟶ S) :=
  RelativeClosedImmersionWitness f

abbrev Book8IsFiniteDimensionalLocallyOnBase {S : Scheme.{u}}
    (P : RelativeProjectiveBundleData S) : Prop :=
  IsFiniteDimensionalLocallyOnBase P

abbrev Chapter10PicardOperations (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10PicardOperations X

abbrev Chapter10DeterminantLineAPI {Z T : Scheme.{u}} (q : Z ⟶ T) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10DeterminantLineAPI q

abbrev Chapter10IdealDualAPI (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10IdealDualAPI X

abbrev Chapter10LineBundle (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10LineBundle X

abbrev Chapter09AsBook8LineBundle {X : Scheme.{u}} (L : Chapter10LineBundle X) :
  Book8LineBundle X :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09AsChapter04LineBundle L

abbrev baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : Scheme.{u} :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.baseChange f g

abbrev baseChangeToSource {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    baseChange f g ⟶ X :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.baseChangeToSource f g

abbrev baseChangeToBase {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    baseChange f g ⟶ T :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.baseChangeToBase f g

abbrev baseChangeLineBundle {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : Book8LineBundle X) : Book8LineBundle (baseChange f g) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.baseChangeLineBundle
    f g L

abbrev IsBaseChangeOf {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : Book8LineBundle X) (M : Book8LineBundle (baseChange f g)) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsBaseChangeOf
    f g L M

abbrev FiniteLocallyFreeProfile {X Y : Scheme.{u}} (q : X ⟶ Y) (d : ℕ) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10FiniteLocallyFreeProfile q d

abbrev EffectiveCartierDivisor (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10EffectiveCartierDivisor X

/-! A generic effective-descent record is useful for every structured fiber category.  The
    `DescentData` object contains the overlap maps and its triple cocycle, while the comparison
    records effectivity. -/

structure EffectiveDescent
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (D : F.DescentData f) where
  descended : F.obj (.mk (op S))
  comparison : D ≅ F.toDescentData f descended

def IsEffectiveDescent
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) : Prop :=
  ∀ D : F.DescentData f, Nonempty (EffectiveDescent F f D)

def IsFullyFaithfulDescent
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) : Prop :=
  (F.toDescentData f).FullyFaithful

structure EffectiveAndFullyFaithfulDescent
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) : Prop where
  effective : IsEffectiveDescent F f
  fullyFaithful : IsFullyFaithfulDescent F f

/-! The pinned sheaf-of-modules API exposes all module sheaves.  This is the canonical ambient
    pseudofunctor from which the quasi-coherent full-subcategory interface below is formed. -/

noncomputable def moduleSheafPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of X.unop.Modules)
    (fun f => (Scheme.Modules.pullback f.unop).toCat)
    (fun X => Cat.Hom.isoMk (Scheme.Modules.pullbackId X.unop))
    (fun f g => Cat.Hom.isoMk (Scheme.Modules.pullbackComp g.unop f.unop))

def quasiCoherentModuleSheafObjectProperty :
    moduleSheafPseudofunctor.ObjectProperty where
  prop X := SheafOfModules.isQuasicoherent X.unop.ringCatSheaf

/- LOCAL_DEPENDENCY_GUESS: the pinned snapshot exposes quasi-coherent objects and the ambient
   pullback pseudofunctor separately, but not the general pullback-preservation instance needed
   to form their full-subcategory pseudofunctor. -/
instance quasiCoherentModuleSheafObjectProperty_isClosedUnderMapObj :
    quasiCoherentModuleSheafObjectProperty.IsClosedUnderMapObj where
  map_obj hM f := by
    sorry

noncomputable def quasiCoherentModuleSheafPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  quasiCoherentModuleSheafObjectProperty.fullsubcategory

abbrev ModuleSheafDescentData {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) := moduleSheafPseudofunctor.DescentData f

abbrev QuasiCoherentModuleSheafDescentData {ι : Type v} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) :=
  quasiCoherentModuleSheafPseudofunctor.DescentData f

/-! The affine and geometric overlap objects used by the displayed synthesis diagram. -/

noncomputable def schemeBaseChange {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) : Scheme.{u} :=
  pullback f p

def schemeBaseChangeMap {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) :
    schemeBaseChange f p ⟶ T :=
  pullback.snd f p

noncomputable def schemeAmitsurOverlap {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) : Scheme.{u} :=
  pullback (schemeBaseChangeMap f p) (schemeBaseChangeMap f p)

def schemeAmitsurLeft {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) :
    schemeAmitsurOverlap f p ⟶ schemeBaseChange f p :=
  pullback.fst (schemeBaseChangeMap f p) (schemeBaseChangeMap f p)

def schemeAmitsurRight {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) :
    schemeAmitsurOverlap f p ⟶ schemeBaseChange f p :=
  pullback.snd (schemeBaseChangeMap f p) (schemeBaseChangeMap f p)

/-! Tensor notation for the upper row `M → B ⊗[A] M ⇉ (B ⊗[A] B) ⊗[A] M`. -/

abbrev AmitsurFirstOverlap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  B ⊗[A] B

abbrev AmitsurSecondOverlap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  (B ⊗[A] B) ⊗[A] B

abbrev AmitsurBaseChange (A B M : Type u) [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra A B] [Module A M] :=
  B ⊗[A] M

abbrev AmitsurModuleOverlap (A B M : Type u) [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra A B] [Module A M] :=
  (B ⊗[A] B) ⊗[A] M

abbrev AmitsurTripleModuleOverlap (A B M : Type u) [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra A B] [Module A M] :=
  ((B ⊗[A] B) ⊗[A] B) ⊗[A] M

noncomputable def amitsurUnit (A B M : Type u) [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra A B] [Module A M] :
    M →ₗ[A] AmitsurBaseChange A B M :=
  TensorProduct.mk A B M 1

noncomputable def amitsurLeft (A B M : Type u) [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra A B] [Module A M] :
    AmitsurBaseChange A B M →ₗ[A] AmitsurModuleOverlap A B M :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap.rTensor M

noncomputable def amitsurRight (A B M : Type u) [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra A B] [Module A M] :
    AmitsurBaseChange A B M →ₗ[A] AmitsurModuleOverlap A B M :=
  (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap.rTensor M

noncomputable def amitsurDifference (A B M : Type u) [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra A B] [Module A M] :
    AmitsurBaseChange A B M →ₗ[A] AmitsurModuleOverlap A B M :=
  amitsurLeft A B M - amitsurRight A B M

structure AmitsurModuleDiagram (A B M : Type u) [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra A B] [Module A M] where
  unit : M →ₗ[A] AmitsurBaseChange A B M
  left : AmitsurBaseChange A B M →ₗ[A] AmitsurModuleOverlap A B M
  right : AmitsurBaseChange A B M →ₗ[A] AmitsurModuleOverlap A B M

noncomputable def canonicalAmitsurModuleDiagram (A B M : Type u) [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra A B] [Module A M] : AmitsurModuleDiagram A B M where
  unit := amitsurUnit A B M
  left := amitsurLeft A B M
  right := amitsurRight A B M

/-! Canonical affine translation and the intrinsic affine envelope. -/

def affineSpecOfRingHom {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    AlgebraicGeometry.Spec (.of B) ⟶ AlgebraicGeometry.Spec (.of A) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)

noncomputable def intrinsicAffineEnvelope (X : Scheme.{u}) : Scheme.{u} :=
  AlgebraicGeometry.Spec (.of Γ(X, ⊤))

def intrinsicAffineEnvelopeMap (X : Scheme.{u}) : X ⟶ intrinsicAffineEnvelope X :=
  X.toSpecΓ

def IsQuasiAffineViaIntrinsicAffineEnvelope (X : Scheme.{u}) : Prop :=
  CompactSpace X ∧ IsOpenImmersion (intrinsicAffineEnvelopeMap X)

/-! The morphism-property predicate used in the reusable package. -/

def IsFpqcLocalMorphismProperty (P : MorphismProperty Scheme) : Prop :=
  P.DescendsAlong FpqcMorphismProperty

def FiniteLocallyFreeMorphismProperty : MorphismProperty Scheme :=
  @IsFinite ⊓ @Flat ⊓ @LocallyOfFinitePresentation

/-! A finite-flat group scheme is represented by a group object in the slice.  This keeps the
    multiplication, unit, inverse, and all their laws in the canonical `GrpObj` interface. -/

structure FiniteFlatGroupScheme {G S : Scheme.{u}} (e : G ⟶ S) : Prop where
  finite : IsFinite e
  flat : Flat e
  groupObject : GrpObj (Over.mk e)

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17
