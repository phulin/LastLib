import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.Section01TheNerveOfACover
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09

noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

/-! ## Book-facing finite locally free and fpqc interfaces -/

/-- A finite locally free module sheaf of the constant rank `r`.

The earlier Book 8 rank interface records local freeness without choosing a global basis;
quasicoherence and finite type are kept explicit at this book boundary.
-/
def chapter09FiniteLocallyFreeOfRank {X : Scheme.{u}} (M : X.Modules) (r : ℕ) : Prop :=
  M.IsQuasicoherent ∧
    M.IsFiniteType ∧
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02LocallyFreeRank
        M r

/-- A rank-`r` vector bundle, with its finite locally free carrier exposed. -/
structure Chapter09VectorBundle (X : Scheme.{u}) (r : ℕ) where
  carrier : X.Modules
  locallyFree : chapter09FiniteLocallyFreeOfRank carrier r

/-- A line bundle is a rank-one vector bundle. -/
abbrev Chapter09LineBundle (X : Scheme.{u}) := Chapter09VectorBundle X 1

/- The Book 8 ampleness interface is phrased for its invertible-sheaf carrier.  A rank-one
finite locally free carrier is the same mathematical object; this adapter keeps that bridge
explicit until the corresponding pinned sheaf-level equivalence is available. -/
noncomputable def chapter09AsChapter04LineBundle
    {X : Scheme.{u}} (L : Chapter09LineBundle X) :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04LineBundle X :=
  { sheaf := L.carrier
    isInvertible :=
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04_isInvertible_of_chapter02Invertible
        L.locallyFree.2.2 }

instance {X : Scheme.{u}} {r : ℕ} : CoeOut (Chapter09VectorBundle X r) X.Modules :=
  ⟨Chapter09VectorBundle.carrier⟩

/-- Morphisms of vector bundles are morphisms of their module sheaves. -/
abbrev Chapter09VectorBundleMorphism
    {X : Scheme.{u}} {r s : ℕ}
    (E : Chapter09VectorBundle X r) (F : Chapter09VectorBundle X s) :=
  E.carrier ⟶ F.carrier

/-- Isomorphism of vector bundles through their underlying module sheaves. -/
def chapter09VectorBundleIsomorphic
    {X : Scheme.{u}} {r : ℕ}
    (E F : Chapter09VectorBundle X r) : Prop :=
  Nonempty (E.carrier ≅ F.carrier)

/-- An fpqc morphism used as a single-cover descent datum. -/
structure Chapter09FpqcCover {S T : Scheme.{u}} (p : T ⟶ S) : Prop where
  flat : Flat p
  quasiCompact : QuasiCompact p
  surjective : Surjective p

abbrev Chapter09PullbackModule
    {S T : Scheme.{u}} (p : T ⟶ S) (M : S.Modules) : T.Modules :=
  (Scheme.Modules.pullback p).obj M

/-- Pullback preserves the vector-bundle carrier; the preservation proof is the local module
descent bridge used by this chapter. -/
noncomputable def chapter09PullbackVectorBundle
    {S T : Scheme.{u}} (p : T ⟶ S)
    {r : ℕ} (E : Chapter09VectorBundle S r) : Chapter09VectorBundle T r where
  carrier := Chapter09PullbackModule p E.carrier
  locallyFree := by sorry

noncomputable def chapter09PullbackLineBundle
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle S) : Chapter09LineBundle T :=
  chapter09PullbackVectorBundle p L

noncomputable def chapter09PullbackCompositionIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    Chapter09PullbackModule (f ≫ g) M ≅ Chapter09PullbackModule f (Chapter09PullbackModule g M) :=
  (Scheme.Modules.pullbackComp f g).symm.app M

noncomputable def chapter09PullbackIdentityIso
    {X : Scheme.{u}} (M : X.Modules) :
    Chapter09PullbackModule (𝟙 X) M ≅ M :=
  (Scheme.Modules.pullbackId X).app M

/-! ## Čech nerve and descent data -/

abbrev Chapter09DoubleOverlap {S T : Scheme.{u}} (p : T ⟶ S) :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04PairProduct p

noncomputable def chapter09DoubleFirst
    {S T : Scheme.{u}} (p : T ⟶ S) : Chapter09DoubleOverlap p ⟶ T :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P1 p

noncomputable def chapter09DoubleSecond
    {S T : Scheme.{u}} (p : T ⟶ S) : Chapter09DoubleOverlap p ⟶ T :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P2 p

/-- The canonical comparison between the two iterated pullbacks of a module from `S` to the
double overlap. -/
noncomputable def chapter09CanonicalDescentOverlapIso
    {S T : Scheme.{u}} (p : T ⟶ S) {r : ℕ} (E : Chapter09VectorBundle S r) :
    Chapter09PullbackModule (chapter09DoubleFirst p)
        (Chapter09PullbackModule p E.carrier) ≅
      Chapter09PullbackModule (chapter09DoubleSecond p)
        (Chapter09PullbackModule p E.carrier) := by
  exact
    (chapter09PullbackCompositionIso (chapter09DoubleFirst p) p E.carrier).symm ≪≫
      eqToIso (congrArg
        (fun q : Chapter09DoubleOverlap p ⟶ S => Chapter09PullbackModule q E.carrier)
        (pullback.condition :
          chapter09DoubleFirst p ≫ p = chapter09DoubleSecond p ≫ p)) ≪≫
      chapter09PullbackCompositionIso (chapter09DoubleSecond p) p E.carrier

/-- The canonical triple overlap from the earlier Čech-nerve interface. -/
structure Chapter09CechNerve {S T : Scheme.{u}} (p : T ⟶ S) where
  triple : Scheme.{u}
  isCanonical :
    triple =
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p

theorem chapter09_cech_nerve_exists
    {S T : Scheme.{u}} (p : T ⟶ S) : Nonempty (Chapter09CechNerve p) := by
  exact ⟨{
    triple :=
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p
    isCanonical := rfl
  }⟩

noncomputable def chapter09CanonicalCechNerve
    {S T : Scheme.{u}} (p : T ⟶ S) : Chapter09CechNerve p :=
  Classical.choice (chapter09_cech_nerve_exists p)

/- The three face equalities identify the two-step pullback presentations of the triple overlap. -/
theorem chapter09CechFirstFace
    {S T : Scheme.{u}} (p : T ⟶ S) :
    LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P12 p ≫
        chapter09DoubleFirst p =
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P13 p ≫
        chapter09DoubleFirst p := by
  exact (Chapter04.chapter04P13_fst p).symm

theorem chapter09CechSecondFace
    {S T : Scheme.{u}} (p : T ⟶ S) :
    LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P12 p ≫
        chapter09DoubleSecond p =
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P23 p ≫
        chapter09DoubleFirst p := by
  exact (Chapter04.chapter04P23_fst p).symm

theorem chapter09CechThirdFace
    {S T : Scheme.{u}} (p : T ⟶ S) :
    LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P23 p ≫
        chapter09DoubleSecond p =
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P13 p ≫
        chapter09DoubleSecond p := by
  exact (Chapter04.chapter04P23_snd p).trans (Chapter04.chapter04P13_snd p).symm

/- The pullback of an overlap isomorphism along a face, with the canonical pseudofunctorial
comparison maps made explicit. -/
noncomputable def chapter09CechPullbackIso
    {S T U : Scheme.{u}} (p : T ⟶ S) (q : U ⟶ Chapter09DoubleOverlap p)
    {M : T.Modules}
    (φ : Chapter09PullbackModule (chapter09DoubleFirst p) M ≅
      Chapter09PullbackModule (chapter09DoubleSecond p) M) :
    Chapter09PullbackModule (q ≫ chapter09DoubleFirst p) M ≅
      Chapter09PullbackModule (q ≫ chapter09DoubleSecond p) M :=
  chapter09PullbackCompositionIso q (chapter09DoubleFirst p) M ≪≫
    (Scheme.Modules.pullback q).mapIso φ ≪≫
      (chapter09PullbackCompositionIso q (chapter09DoubleSecond p) M).symm

noncomputable def chapter09CechNormalizationIso
    {S T : Scheme.{u}} (p : T ⟶ S) {M : T.Modules} :
    Chapter09PullbackModule
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04Diagonal p ≫
          chapter09DoubleFirst p) M ≅
      Chapter09PullbackModule
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04Diagonal p ≫
          chapter09DoubleSecond p) M :=
  eqToIso (congrArg (fun q : T ⟶ T => Chapter09PullbackModule q M)
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04Diagonal_p1 p)) ≪≫
    chapter09PullbackIdentityIso M ≪≫
      (eqToIso (congrArg (fun q : T ⟶ T => Chapter09PullbackModule q M)
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04Diagonal_p2 p)) ≪≫
        chapter09PullbackIdentityIso M).symm

noncomputable def chapter09CechTranspositionIso
    {S T : Scheme.{u}} (p : T ⟶ S) {M : T.Modules}
    (φ : Chapter09PullbackModule (chapter09DoubleFirst p) M ≅
      Chapter09PullbackModule (chapter09DoubleSecond p) M) :
    Chapter09PullbackModule
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04Transposition p ≫
          chapter09DoubleFirst p) M ≅
      Chapter09PullbackModule
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04Transposition p ≫
          chapter09DoubleSecond p) M :=
  eqToIso (congrArg (fun q : Chapter09DoubleOverlap p ⟶ T =>
      Chapter09PullbackModule q M)
    (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04Transposition_p1 p)) ≪≫
    φ.symm ≪≫
      (eqToIso (congrArg (fun q : Chapter09DoubleOverlap p ⟶ T =>
          Chapter09PullbackModule q M)
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04Transposition_p2 p))).symm

def chapter09CechTripleCondition
    {S T : Scheme.{u}} (p : T ⟶ S) (_N : Chapter09CechNerve p)
    {M : T.Modules}
    (φ : Chapter09PullbackModule (chapter09DoubleFirst p) M ≅
      Chapter09PullbackModule (chapter09DoubleSecond p) M) : Prop :=
  (chapter09CechPullbackIso p
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P12 p) φ).hom ≫
      (eqToIso (congrArg (fun q :
          LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T =>
        Chapter09PullbackModule q M) (chapter09CechSecondFace p))).hom ≫
      (chapter09CechPullbackIso p
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P23 p) φ).hom ≫
      (eqToIso (congrArg (fun q :
          LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T =>
        Chapter09PullbackModule q M) (chapter09CechThirdFace p))).hom =
    (eqToIso (congrArg (fun q :
        LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04TripleProduct p ⟶ T =>
      Chapter09PullbackModule q M) (chapter09CechFirstFace p))).hom ≫
      (chapter09CechPullbackIso p
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04P13 p) φ).hom

def chapter09CechCocycleCondition
    {S T : Scheme.{u}} (p : T ⟶ S) (N : Chapter09CechNerve p)
    {M : T.Modules}
    (φ : Chapter09PullbackModule (chapter09DoubleFirst p) M ≅
      Chapter09PullbackModule (chapter09DoubleSecond p) M) : Prop :=
  chapter09CechTripleCondition p N φ

/- The diagonal normalization and transposition-inverse equations are consequences of the
triple-overlap cocycle. They are exposed separately so a descent datum records only the
compatibility required by the book-facing definition. -/
theorem chapter09_cech_cocycle_implies_normalization
    {S T : Scheme.{u}} (p : T ⟶ S) (N : Chapter09CechNerve p)
    {M : T.Modules}
    (φ : Chapter09PullbackModule (chapter09DoubleFirst p) M ≅
      Chapter09PullbackModule (chapter09DoubleSecond p) M)
    (hφ : chapter09CechTripleCondition p N φ) :
    (chapter09CechPullbackIso p
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04Diagonal p) φ).hom =
      (chapter09CechNormalizationIso p).hom := by
  sorry

theorem chapter09_cech_cocycle_implies_transposition
    {S T : Scheme.{u}} (p : T ⟶ S) (N : Chapter09CechNerve p)
    {M : T.Modules}
    (φ : Chapter09PullbackModule (chapter09DoubleFirst p) M ≅
      Chapter09PullbackModule (chapter09DoubleSecond p) M)
    (hφ : chapter09CechTripleCondition p N φ) :
    (chapter09CechPullbackIso p
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.chapter04Transposition p) φ).hom =
      (chapter09CechTranspositionIso p φ).hom := by
  sorry

/-- A vector-bundle descent datum consists of the object upstairs, its overlap identification, and
the triple-overlap cocycle. -/
structure Chapter09ModuleDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) (r : ℕ) where
  nerve : Chapter09CechNerve p
  upstairs : Chapter09VectorBundle T r
  overlapIso :
    Chapter09PullbackModule (chapter09DoubleFirst p) upstairs.carrier ≅
      Chapter09PullbackModule (chapter09DoubleSecond p) upstairs.carrier
  cocycle : chapter09CechCocycleCondition p nerve overlapIso

abbrev Chapter09VectorBundleDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) (r : ℕ) :=
  Chapter09ModuleDescentDatum p r

abbrev Chapter09LineBundleDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) :=
  Chapter09ModuleDescentDatum p 1

/- The canonical pullback object is itself a descent datum.  The overlap
comparison is explicit above; only the usual associativity/cocycle proof is
left for the later descent proof. -/
noncomputable def chapter09CanonicalVectorBundleDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) {r : ℕ}
    (E : Chapter09VectorBundle S r) : Chapter09VectorBundleDescentDatum p r := by
  refine {
    nerve := chapter09CanonicalCechNerve p
    upstairs := chapter09PullbackVectorBundle p E
    overlapIso := chapter09CanonicalDescentOverlapIso p E
    cocycle := ?_ }
  sorry

def chapter09DescentComparisonCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09VectorBundle S r)
    (e : (chapter09PullbackVectorBundle p E).carrier ≅ D.upstairs.carrier) : Prop := by
  exact
    (Scheme.Modules.pullback (chapter09DoubleFirst p)).map e.hom ≫ D.overlapIso.hom =
      (chapter09CanonicalDescentOverlapIso p E).hom ≫
        (Scheme.Modules.pullback (chapter09DoubleSecond p)).map e.hom

def chapter09DescentMorphismCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s)
    (f : D.upstairs.carrier ⟶ E.upstairs.carrier) : Prop := by
  exact
    D.overlapIso.hom ≫ (Scheme.Modules.pullback (chapter09DoubleSecond p)).map f =
      (Scheme.Modules.pullback (chapter09DoubleFirst p)).map f ≫ E.overlapIso.hom

/-- An effective descent result, including the comparison with the upstairs object. -/
structure Chapter09VectorBundleDescentResult
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) where
  downstairs : Chapter09VectorBundle S r
  comparison :
    (chapter09PullbackVectorBundle p downstairs).carrier ≅ D.upstairs.carrier
  compatible : chapter09DescentComparisonCompatible D downstairs comparison

/-- The comparison equation identifying two effective descents of the same datum. -/
def chapter09DescentResultsIsoCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    {D : Chapter09ModuleDescentDatum p r}
    (R R' : Chapter09VectorBundleDescentResult D)
    (e : R.downstairs.carrier ≅ R'.downstairs.carrier) : Prop :=
  (Scheme.Modules.pullback p).mapIso e ≪≫ R'.comparison = R.comparison

structure Chapter09DescentMorphism
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) where
  map : D.upstairs.carrier ⟶ E.upstairs.carrier
  compatible : chapter09DescentMorphismCompatible D E map

end
end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09
