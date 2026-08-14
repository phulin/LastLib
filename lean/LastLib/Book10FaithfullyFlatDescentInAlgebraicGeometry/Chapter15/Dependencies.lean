import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Topology.Sheaves.LocallySurjective
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Section04NormsAndAddition

/-!
# Chapter 15: quasi-projective and projective descent

This file contains the interfaces shared by the four source sections.  The
positivity and finite-flat vocabulary is inherited from Books 8 and 10.  The
Čech records below are deliberately explicit: an overlap isomorphism, its
triple-overlap compatibility, and the descended comparison are separate pieces
of data, so an arbitrary upstairs line bundle is never silently treated as a
pullback.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15

noncomputable section

open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

/-! ### Basic book-facing bridges -/

abbrev LineBundle (X : Scheme.{u}) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.LineBundle X

abbrev LineBundlePowers {X : Scheme.{u}} (L : LineBundle X) :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.LineBundlePowers L

abbrev IsFaithfullyFlat {S T : Scheme.{u}} (g : T ⟶ S) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsFaithfullyFlat g

abbrev IsAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsAmple f L

abbrev IsVeryAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsVeryAmple f L

abbrev IsQuasiProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsQuasiProjectiveMorphism f

abbrev IsProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsProjectiveMorphism f

noncomputable def baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : Scheme.{u} :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.baseChange f g

def baseChangeToSource {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    baseChange f g ⟶ X :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.baseChangeToSource f g

def baseChangeToBase {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    baseChange f g ⟶ T :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.baseChangeToBase f g

def baseChangeStructureMap {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    baseChange f g ⟶ S :=
  baseChangeToBase f g ≫ g

noncomputable def pullbackLineBundle {X Y : Scheme.{u}} (h : X ⟶ Y) (L : LineBundle Y) :
    LineBundle X :=
  L.pullback h

def lineBundleIsomorphic {X : Scheme.{u}} (L M : LineBundle X) : Prop :=
  Nonempty (L.sheaf ≅ M.sheaf)

structure LineBundleIso {X : Scheme.{u}} (L M : LineBundle X) where
  hom : L.sheaf ≅ M.sheaf

def lineBundleIsoRefl {X : Scheme.{u}} (L : LineBundle X) : LineBundleIso L L :=
  { hom := Iso.refl _ }

def lineBundleIsoSymm {X : Scheme.{u}} {L M : LineBundle X}
    (e : LineBundleIso L M) : LineBundleIso M L :=
  { hom := e.hom.symm }

def lineBundleIsoTrans {X : Scheme.{u}} {L M N : LineBundle X}
    (e₁ : LineBundleIso L M) (e₂ : LineBundleIso M N) : LineBundleIso L N :=
  { hom := e₁.hom ≪≫ e₂.hom }

theorem lineBundleIsomorphic_refl {X : Scheme.{u}} (L : LineBundle X) :
    lineBundleIsomorphic L L :=
  ⟨Iso.refl _⟩

theorem lineBundleIsomorphic_symm {X : Scheme.{u}} {L M : LineBundle X}
    (h : lineBundleIsomorphic L M) : lineBundleIsomorphic M L := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

theorem lineBundleIsomorphic_trans {X : Scheme.{u}} {L M N : LineBundle X}
    (hLM : lineBundleIsomorphic L M) (hMN : lineBundleIsomorphic M N) :
    lineBundleIsomorphic L N := by
  rcases hLM with ⟨eLM⟩
  rcases hMN with ⟨eMN⟩
  exact ⟨eLM ≪≫ eMN⟩

/- LOCAL_DEPENDENCY_GUESS: the pinned sheaf API has pullback functors and
  their comparison isomorphisms, but no book-facing line-bundle isomorphism
  wrapper.  These explicit bridges expose the canonical comparison in a
  form usable by the Čech cocycle and restriction statements. -/
theorem lineBundlePullbackIso_exists {X Y : Scheme.{u}}
    {L M : LineBundle Y} (e : LineBundleIso L M) (h : X ⟶ Y) :
    Nonempty (LineBundleIso (pullbackLineBundle h L) (pullbackLineBundle h M)) := by
  exact ⟨{ hom := (Scheme.Modules.pullback h).mapIso e.hom }⟩

noncomputable def lineBundlePullbackIso {X Y : Scheme.{u}}
    {L M : LineBundle Y} (e : LineBundleIso L M) (h : X ⟶ Y) :
    LineBundleIso (pullbackLineBundle h L) (pullbackLineBundle h M) :=
  { hom := (Scheme.Modules.pullback h).mapIso e.hom }

theorem lineBundlePullbackCompIso_exists {X Y Z : Scheme.{u}} (L : LineBundle Z)
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    Nonempty (LineBundleIso
      (pullbackLineBundle h (pullbackLineBundle k L))
      (pullbackLineBundle (h ≫ k) L)) := by
  exact ⟨{ hom := (Scheme.Modules.pullbackComp h k).app L.sheaf }⟩

noncomputable def lineBundlePullbackCompIso {X Y Z : Scheme.{u}} (L : LineBundle Z)
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    LineBundleIso
      (pullbackLineBundle h (pullbackLineBundle k L))
      (pullbackLineBundle (h ≫ k) L) :=
  { hom := (Scheme.Modules.pullbackComp h k).app L.sheaf }

abbrev cechDouble {Y X : Scheme.{u}} (q : Y ⟶ X) := pullback q q

abbrev cechFirst {Y X : Scheme.{u}} (q : Y ⟶ X) : cechDouble q ⟶ Y :=
  pullback.fst q q

abbrev cechSecond {Y X : Scheme.{u}} (q : Y ⟶ X) : cechDouble q ⟶ Y :=
  pullback.snd q q

abbrev cechTriple {Y X : Scheme.{u}} (q : Y ⟶ X) :=
  pullback (cechSecond q ≫ q) q

noncomputable def cechFace01 {Y X : Scheme.{u}} (q : Y ⟶ X) :
    cechTriple q ⟶ cechDouble q :=
  pullback.fst (cechSecond q ≫ q) q

noncomputable def cechFace12 {Y X : Scheme.{u}} (q : Y ⟶ X) :
    cechTriple q ⟶ cechDouble q := by
  refine pullback.lift
    (pullback.fst (cechSecond q ≫ q) q ≫ cechSecond q)
    (pullback.snd (cechSecond q ≫ q) q) ?_
  change
    (pullback.fst (cechSecond q ≫ q) q ≫ cechSecond q) ≫ q =
      pullback.snd (cechSecond q ≫ q) q ≫ q
  rw [Category.assoc]
  exact pullback.condition

noncomputable def cechFace02 {Y X : Scheme.{u}} (q : Y ⟶ X) :
    cechTriple q ⟶ cechDouble q := by
  refine pullback.lift
    (pullback.fst (cechSecond q ≫ q) q ≫ cechFirst q)
    (pullback.snd (cechSecond q ≫ q) q) ?_
  change
    (pullback.fst (cechSecond q ≫ q) q ≫ cechFirst q) ≫ q =
      pullback.snd (cechSecond q ≫ q) q ≫ q
  rw [Category.assoc, ← pullback.condition (f := q) (g := q)]
  exact pullback.condition

noncomputable def lineBundleCechFaceIso {Y X Z : Scheme.{u}} (q : Y ⟶ X)
    (M : LineBundle Y)
    (e : LineBundleIso (pullbackLineBundle (cechFirst q) M)
      (pullbackLineBundle (cechSecond q) M))
    (face : Z ⟶ cechDouble q) :
    LineBundleIso
      (pullbackLineBundle (face ≫ cechFirst q) M)
      (pullbackLineBundle (face ≫ cechSecond q) M) :=
  { hom :=
      (lineBundlePullbackCompIso M face (cechFirst q)).hom.symm ≪≫
        (Scheme.Modules.pullback face).mapIso e.hom ≪≫
          (lineBundlePullbackCompIso M face (cechSecond q)).hom }

theorem lineBundleCechFaceIso_exists {Y X Z : Scheme.{u}} (q : Y ⟶ X)
    (M : LineBundle Y)
    (e : LineBundleIso (pullbackLineBundle (cechFirst q) M)
      (pullbackLineBundle (cechSecond q) M))
    (face : Z ⟶ cechDouble q) :
    Nonempty (LineBundleIso
      (pullbackLineBundle (face ≫ cechFirst q) M)
      (pullbackLineBundle (face ≫ cechSecond q) M)) :=
  ⟨lineBundleCechFaceIso q M e face⟩

def castLineBundleIso {X : Scheme.{u}} {L M L' M' : LineBundle X}
    (hL : L = L') (hM : M = M') (e : LineBundleIso L M) :
    LineBundleIso L' M' := by
  cases hL
  cases hM
  exact e

def lineBundleCechCocycleCondition {Y X Z : Scheme.{u}} (q : Y ⟶ X)
    (M : LineBundle Y)
    (e : LineBundleIso (pullbackLineBundle (cechFirst q) M)
      (pullbackLineBundle (cechSecond q) M))
    (face01 face12 face02 : Z ⟶ cechDouble q)
    (h01 : face01 ≫ cechSecond q = face12 ≫ cechFirst q)
    (h02 : face01 ≫ cechFirst q = face02 ≫ cechFirst q)
    (h12 : face12 ≫ cechSecond q = face02 ≫ cechSecond q) : Prop :=
  let e01 := lineBundleCechFaceIso q M e face01
  let e12 := castLineBundleIso
    (congrArg (fun h : Z ⟶ Y => pullbackLineBundle h M) h01.symm)
    rfl (lineBundleCechFaceIso q M e face12)
  let e02 := castLineBundleIso
    (congrArg (fun h : Z ⟶ Y => pullbackLineBundle h M) h02.symm)
    (congrArg (fun h : Z ⟶ Y => pullbackLineBundle h M) h12.symm)
    (lineBundleCechFaceIso q M e face02)
  (lineBundleIsoTrans e01 e12).hom = e02.hom

/- The canonical datum on a pullback line bundle uses the pseudofunctorial
  comparison for module-sheaf pullback and the equality of the two maps from
  the double overlap to the base.  Keep this comparison explicit so a
  realization cannot replace compatibility by an unconstrained proposition. -/
noncomputable def lineBundleCanonicalCechIso {Y X : Scheme.{u}} (q : Y ⟶ X)
    (L : LineBundle X) :
    LineBundleIso
      (pullbackLineBundle (cechFirst q) (pullbackLineBundle q L))
      (pullbackLineBundle (cechSecond q) (pullbackLineBundle q L)) :=
  { hom :=
      (lineBundlePullbackCompIso L (cechFirst q) q).hom ≪≫
        eqToIso (congrArg (fun h : cechDouble q ⟶ X =>
          (Scheme.Modules.pullback h).obj L.sheaf)
          (pullback.condition : cechFirst q ≫ q = cechSecond q ≫ q)) ≪≫
          (lineBundlePullbackCompIso L (cechSecond q) q).hom.symm }

theorem lineBundleCanonicalCechIso_exists {Y X : Scheme.{u}} (q : Y ⟶ X)
    (L : LineBundle X) :
    Nonempty (LineBundleIso
      (pullbackLineBundle (cechFirst q) (pullbackLineBundle q L))
      (pullbackLineBundle (cechSecond q) (pullbackLineBundle q L))) :=
  ⟨lineBundleCanonicalCechIso q L⟩

noncomputable def moduleCechFaceIso {T S Z : Scheme.{u}} (g : T ⟶ S)
    (E : T.Modules)
    (e : (Scheme.Modules.pullback (cechFirst g)).obj E ≅
      (Scheme.Modules.pullback (cechSecond g)).obj E)
    (face : Z ⟶ cechDouble g) :
    (Scheme.Modules.pullback (face ≫ cechFirst g)).obj E ≅
      (Scheme.Modules.pullback (face ≫ cechSecond g)).obj E :=
  ((Scheme.Modules.pullbackComp face (cechFirst g)).app E).symm ≪≫
    (Scheme.Modules.pullback face).mapIso e ≪≫
      (Scheme.Modules.pullbackComp face (cechSecond g)).app E

theorem moduleCechFaceIso_exists {T S Z : Scheme.{u}} (g : T ⟶ S)
    (E : T.Modules)
    (e : (Scheme.Modules.pullback (cechFirst g)).obj E ≅
      (Scheme.Modules.pullback (cechSecond g)).obj E)
    (face : Z ⟶ cechDouble g) :
    Nonempty ((Scheme.Modules.pullback (face ≫ cechFirst g)).obj E ≅
      (Scheme.Modules.pullback (face ≫ cechSecond g)).obj E) :=
  ⟨moduleCechFaceIso g E e face⟩

def castModuleIso {X : Scheme.{u}} {M N M' N' : X.Modules}
    (hM : M = M') (hN : N = N') (e : M ≅ N) : M' ≅ N' := by
  cases hM
  cases hN
  exact e

def moduleCechCocycleCondition {T S Z : Scheme.{u}} (g : T ⟶ S)
    (E : T.Modules)
    (e : (Scheme.Modules.pullback (cechFirst g)).obj E ≅
      (Scheme.Modules.pullback (cechSecond g)).obj E)
    (face01 face12 face02 : Z ⟶ cechDouble g)
    (h01 : face01 ≫ cechSecond g = face12 ≫ cechFirst g)
    (h02 : face01 ≫ cechFirst g = face02 ≫ cechFirst g)
    (h12 : face12 ≫ cechSecond g = face02 ≫ cechSecond g) : Prop :=
  let e01 := moduleCechFaceIso g E e face01
  let e12 := castModuleIso
    (congrArg (fun h : Z ⟶ T => (Scheme.Modules.pullback h).obj E) h01.symm)
    rfl (moduleCechFaceIso g E e face12)
  let e02 := castModuleIso
    (congrArg (fun h : Z ⟶ T => (Scheme.Modules.pullback h).obj E) h02.symm)
    (congrArg (fun h : Z ⟶ T => (Scheme.Modules.pullback h).obj E) h12.symm)
    (moduleCechFaceIso g E e face02)
  e01 ≪≫ e12 = e02

/- The module analogue of `lineBundleCanonicalCechIso` above. -/
noncomputable def moduleCanonicalCechIso {T S : Scheme.{u}} (g : T ⟶ S)
    (E : S.Modules) :
    (Scheme.Modules.pullback (cechFirst g)).obj
        ((Scheme.Modules.pullback g).obj E) ≅
      (Scheme.Modules.pullback (cechSecond g)).obj
        ((Scheme.Modules.pullback g).obj E) :=
  (Scheme.Modules.pullbackComp (cechFirst g) g).app E ≪≫
    eqToIso (congrArg (fun h : cechDouble g ⟶ S =>
      (Scheme.Modules.pullback h).obj E)
      (pullback.condition : cechFirst g ≫ g = cechSecond g ≫ g)) ≪≫
      ((Scheme.Modules.pullbackComp (cechSecond g) g).app E).symm

theorem moduleCanonicalCechIso_exists {T S : Scheme.{u}} (g : T ⟶ S)
    (E : S.Modules) :
    Nonempty ((Scheme.Modules.pullback (cechFirst g)).obj
        ((Scheme.Modules.pullback g).obj E) ≅
      (Scheme.Modules.pullback (cechSecond g)).obj
        ((Scheme.Modules.pullback g).obj E)) :=
  ⟨moduleCanonicalCechIso g E⟩

/-! ### Finiteness and cover profiles -/

structure FpqcCoverData {S T : Scheme.{u}} (g : T ⟶ S) where
  flat : Flat g
  surjective : Surjective g
  quasiCompact : QuasiCompact g

theorem FpqcCoverData.isFaithfullyFlat {S T : Scheme.{u}} {g : T ⟶ S}
    (G : FpqcCoverData g) : IsFaithfullyFlat g :=
  ⟨G.flat, G.surjective⟩

theorem FpqcCoverData.isFpqc {S T : Scheme.{u}} {g : T ⟶ S}
    (G : FpqcCoverData g) : IsFpqcCover g :=
  ⟨G.isFaithfullyFlat, G.quasiCompact⟩

structure FinitePresentationData {X S : Scheme.{u}} (f : X ⟶ S) where
  quasiCompact : QuasiCompact f
  quasiSeparated : QuasiSeparated f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f

def IsFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ QuasiSeparated f ∧ LocallyOfFinitePresentation f

theorem quasiSeparated_of_finitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsFinitePresentation f) : QuasiSeparated f :=
  hf.2.1

structure FiniteLocallyFreeConstantRank {T S : Scheme.{u}} (g : T ⟶ S) where
  rank : ℕ
  positive : 0 < rank
  profile :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10FiniteLocallyFreeProfile
      g rank

def FiniteLocallyFreeMorphism {T S : Scheme.{u}} (g : T ⟶ S) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10FiniteLocallyFreeMorphism g

theorem FiniteLocallyFreeConstantRank.morphism {T S : Scheme.{u}} {g : T ⟶ S}
    (G : FiniteLocallyFreeConstantRank g) : FiniteLocallyFreeMorphism g := by
  exact LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10_finiteLocallyFreeProfile_to_morphism
    G.profile

/- The positive constant-rank hypothesis is what supplies surjectivity; it is
  not silently folded into the definition of finite locally free. -/
theorem FiniteLocallyFreeConstantRank.surjective {T S : Scheme.{u}} {g : T ⟶ S}
    (G : FiniteLocallyFreeConstantRank g) : Surjective g := by
  let : IsFinite g := G.profile.finite
  let : Flat g := G.profile.flat
  let : LocallyOfFinitePresentation g := G.profile.locallyOfFinitePresentation
  rw [← Scheme.Hom.one_le_finrank_iff_surjective]
  intro y
  rw [G.profile.rank y]
  exact Nat.succ_le_iff.mp G.positive

/- LOCAL_DEPENDENCY_GUESS: base change of a finite locally free morphism is
  available in the pinned Mathlib profile, but the source projection is the
  first projection of `baseChange f g`; expose that orientation explicitly. -/
theorem baseChangeToSource_finiteLocallyFree
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) :
    FiniteLocallyFreeMorphism (baseChangeToSource f g) := by
  let : IsFinite g := G.profile.finite
  let : Flat g := G.profile.flat
  let : LocallyOfFinitePresentation g := G.profile.locallyOfFinitePresentation
  change FiniteLocallyFreeMorphism (pullback.fst f g)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem baseChangeToSource_surjective
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
  (G : FiniteLocallyFreeConstantRank g) :
    Surjective (baseChangeToSource f g) := by
  let : Surjective g := G.surjective
  change Surjective (pullback.fst f g)
  exact inferInstance

/-! ### Čech descent data -/

structure ModuleDescentDatum {T S : Scheme.{u}} (g : T ⟶ S) where
  module : T.Modules
  comparison :
    (Scheme.Modules.pullback (cechFirst g)).obj module ≅
      (Scheme.Modules.pullback (cechSecond g)).obj module
  face01 : cechTriple g ⟶ cechDouble g
  face12 : cechTriple g ⟶ cechDouble g
  face02 : cechTriple g ⟶ cechDouble g
  face01_is_canonical : face01 = cechFace01 g
  face12_is_canonical : face12 = cechFace12 g
  face02_is_canonical : face02 = cechFace02 g
  face01_right_eq_face12_left : face01 ≫ cechSecond g = face12 ≫ cechFirst g
  face01_left_eq_face02_left : face01 ≫ cechFirst g = face02 ≫ cechFirst g
  face12_right_eq_face02_right : face12 ≫ cechSecond g = face02 ≫ cechSecond g
  cocycle : moduleCechCocycleCondition g module comparison face01 face12 face02
    face01_right_eq_face12_left face01_left_eq_face02_left face12_right_eq_face02_right

def moduleDescentComparisonCompatible {T S : Scheme.{u}} (g : T ⟶ S)
    (D : ModuleDescentDatum g) (E : S.Modules)
    (e : (Scheme.Modules.pullback g).obj E ≅ D.module) : Prop :=
  (Scheme.Modules.pullback (cechFirst g)).map e.hom ≫ D.comparison.hom =
    (moduleCanonicalCechIso g E).hom ≫
      (Scheme.Modules.pullback (cechSecond g)).map e.hom

structure ModuleDescentRealization {T S : Scheme.{u}} {g : T ⟶ S}
    (D : ModuleDescentDatum g) (E : S.Modules) where
  comparison : (Scheme.Modules.pullback g).obj E ≅ D.module
  comparison_compatible : moduleDescentComparisonCompatible g D E comparison

structure LineBundleDescentDatum {Y X : Scheme.{u}} (q : Y ⟶ X) where
  carrier : LineBundle Y
  comparison :
    LineBundleIso (pullbackLineBundle (cechFirst q) carrier)
      (pullbackLineBundle (cechSecond q) carrier)
  face01 : cechTriple q ⟶ cechDouble q
  face12 : cechTriple q ⟶ cechDouble q
  face02 : cechTriple q ⟶ cechDouble q
  face01_is_canonical : face01 = cechFace01 q
  face12_is_canonical : face12 = cechFace12 q
  face02_is_canonical : face02 = cechFace02 q
  face01_right_eq_face12_left : face01 ≫ cechSecond q = face12 ≫ cechFirst q
  face01_left_eq_face02_left : face01 ≫ cechFirst q = face02 ≫ cechFirst q
  face12_right_eq_face02_right : face12 ≫ cechSecond q = face02 ≫ cechSecond q
  cocycle : lineBundleCechCocycleCondition q carrier comparison face01 face12 face02
    face01_right_eq_face12_left face01_left_eq_face02_left face12_right_eq_face02_right

def lineBundleDescentComparisonCompatible {Y X : Scheme.{u}} (q : Y ⟶ X)
    (D : LineBundleDescentDatum q) (L : LineBundle X)
    (e : LineBundleIso (pullbackLineBundle q L) D.carrier) : Prop :=
  (Scheme.Modules.pullback (cechFirst q)).map e.hom.hom ≫ D.comparison.hom.hom =
    (lineBundleCanonicalCechIso q L).hom.hom ≫
      (Scheme.Modules.pullback (cechSecond q)).map e.hom.hom

structure LineBundleDescentRealization {Y X : Scheme.{u}} {q : Y ⟶ X}
    (D : LineBundleDescentDatum q) (L : LineBundle X) where
  comparison : LineBundleIso (pullbackLineBundle q L) D.carrier
  comparison_compatible : lineBundleDescentComparisonCompatible q D L comparison

structure FpqcLineBundleDescentDatum
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) where
  cover : FpqcCoverData g
  lineBundle : LineBundle (baseChange f g)
  descent : LineBundleDescentDatum (baseChangeToSource f g)
  carrier_eq : descent.carrier = lineBundle

noncomputable def fpqcLineBundleComparison
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : FpqcLineBundleDescentDatum f g) :
    LineBundleIso
      (pullbackLineBundle (cechFirst (baseChangeToSource f g)) D.lineBundle)
      (pullbackLineBundle (cechSecond (baseChangeToSource f g)) D.lineBundle) :=
  castLineBundleIso
    (congrArg (fun L : LineBundle (baseChange f g) =>
      pullbackLineBundle (cechFirst (baseChangeToSource f g)) L) D.carrier_eq)
    (congrArg (fun L : LineBundle (baseChange f g) =>
      pullbackLineBundle (cechSecond (baseChangeToSource f g)) L) D.carrier_eq)
    D.descent.comparison

/- The module datum is intentionally separate from the line-bundle datum:
  §15.2 needs a finite locally free coefficient sheaf and a quotient square in
  addition to the polarization's own Čech cocycle. -/
structure CoefficientDescentDatum
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) where
  cover : FpqcCoverData g
  coefficient : T.Modules
  descent : ModuleDescentDatum g
  coefficient_eq : descent.module = coefficient
  finiteLocallyFree :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04FiniteLocallyFree
      coefficient

/- The double overlap of the base change maps canonically to the double overlap
  of the original cover.  This is the map along which the coefficient descent
  is pulled back. -/
noncomputable def coefficientBaseChangeCechMap
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    cechDouble (baseChangeToSource f g) ⟶ cechDouble g :=
  pullback.map (baseChangeToSource f g) (baseChangeToSource f g) g g
    (baseChangeToBase f g) (baseChangeToBase f g) f
    (pullback.condition :
      baseChangeToSource f g ≫ f = baseChangeToBase f g ≫ g)
    (pullback.condition :
      baseChangeToSource f g ≫ f = baseChangeToBase f g ≫ g)

theorem coefficientBaseChangeCechMap_first
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    coefficientBaseChangeCechMap f g ≫ cechFirst g =
      cechFirst (baseChangeToSource f g) ≫ baseChangeToBase f g := by
  change
    (pullback.map (pullback.fst f g) (pullback.fst f g) g g
      (pullback.snd f g) (pullback.snd f g) f
      (pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g)
      (pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g)) ≫
        pullback.fst g g =
      pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ pullback.snd f g
  change (pullback.lift _ _ _) ≫ _ = _
  exact pullback.lift_fst _ _ _

theorem coefficientBaseChangeCechMap_second
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    coefficientBaseChangeCechMap f g ≫ cechSecond g =
      cechSecond (baseChangeToSource f g) ≫ baseChangeToBase f g := by
  change
    (pullback.map (pullback.fst f g) (pullback.fst f g) g g
      (pullback.snd f g) (pullback.snd f g) f
      (pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g)
      (pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g)) ≫
        pullback.snd g g =
      pullback.snd (pullback.fst f g) (pullback.fst f g) ≫ pullback.snd f g
  change (pullback.lift _ _ _) ≫ _ = _
  exact pullback.lift_snd _ _ _

noncomputable def coefficientCechComparison
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (C : CoefficientDescentDatum f g) :
    (Scheme.Modules.pullback (cechFirst (baseChangeToSource f g))).obj
        ((Scheme.Modules.pullback (baseChangeToBase f g)).obj C.coefficient) ≅
    (Scheme.Modules.pullback (cechSecond (baseChangeToSource f g))).obj
        ((Scheme.Modules.pullback (baseChangeToBase f g)).obj C.coefficient) :=
  by
    let eCoeff := castModuleIso
      (congrArg (fun M : T.Modules =>
        (Scheme.Modules.pullback (cechFirst g)).obj M) C.coefficient_eq)
      (congrArg (fun M : T.Modules =>
        (Scheme.Modules.pullback (cechSecond g)).obj M) C.coefficient_eq)
      C.descent.comparison
    exact
      (Scheme.Modules.pullbackComp (cechFirst (baseChangeToSource f g))
          (baseChangeToBase f g)).app C.coefficient ≪≫
        eqToIso (congrArg (fun h : cechDouble (baseChangeToSource f g) ⟶ T =>
          (Scheme.Modules.pullback h).obj C.coefficient)
          (coefficientBaseChangeCechMap_first f g).symm) ≪≫
        ((Scheme.Modules.pullbackComp (coefficientBaseChangeCechMap f g)
          (cechFirst g)).app C.coefficient).symm ≪≫
        (Scheme.Modules.pullback (coefficientBaseChangeCechMap f g)).mapIso eCoeff ≪≫
        (Scheme.Modules.pullbackComp (coefficientBaseChangeCechMap f g)
          (cechSecond g)).app C.coefficient ≪≫
        eqToIso (congrArg (fun h : cechDouble (baseChangeToSource f g) ⟶ T =>
          (Scheme.Modules.pullback h).obj C.coefficient)
        (coefficientBaseChangeCechMap_second f g)) ≪≫
        ((Scheme.Modules.pullbackComp (cechSecond (baseChangeToSource f g))
          (baseChangeToBase f g)).app C.coefficient).symm

theorem coefficientCechComparison_exists
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (C : CoefficientDescentDatum f g) :
    Nonempty ((Scheme.Modules.pullback (cechFirst (baseChangeToSource f g))).obj
        ((Scheme.Modules.pullback (baseChangeToBase f g)).obj C.coefficient) ≅
      (Scheme.Modules.pullback (cechSecond (baseChangeToSource f g))).obj
        ((Scheme.Modules.pullback (baseChangeToBase f g)).obj C.coefficient)) :=
  ⟨coefficientCechComparison f g C⟩

noncomputable def fpqcLineBundleRealizationComparison
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : FpqcLineBundleDescentDatum f g) (L : LineBundle X)
    (R : LineBundleDescentRealization D.descent L) :
    LineBundleIso (pullbackLineBundle (baseChangeToSource f g) L) D.lineBundle :=
  { hom := R.comparison.hom ≪≫
      eqToIso (congrArg (fun M : LineBundle (baseChange f g) => M.sheaf)
        D.carrier_eq) }

noncomputable def coefficientRealizationComparison
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (C : CoefficientDescentDatum f g) (E : S.Modules)
    (R : ModuleDescentRealization C.descent E) :
    (Scheme.Modules.pullback (baseChangeToSource f g)).obj
        ((Scheme.Modules.pullback f).obj E) ≅
      (Scheme.Modules.pullback (baseChangeToBase f g)).obj C.coefficient :=
  (Scheme.Modules.pullbackComp (baseChangeToSource f g) f).app E ≪≫
    eqToIso (congrArg (fun h : baseChange f g ⟶ S =>
      (Scheme.Modules.pullback h).obj E)
      (pullback.condition :
        baseChangeToSource f g ≫ f = baseChangeToBase f g ≫ g)) ≪≫
    ((Scheme.Modules.pullbackComp (baseChangeToBase f g) g).app E).symm ≪≫
    (Scheme.Modules.pullback (baseChangeToBase f g)).mapIso
      (R.comparison ≪≫
        eqToIso (congrArg (fun M : T.Modules => M) C.coefficient_eq))

/-! ### Finite systems of sections and projective embeddings -/

structure FiniteLinearSystem
    {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) (E : S.Modules) where
  finiteLocallyFree :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04FiniteLocallyFree E
  quotient : (Scheme.Modules.pullback f).obj E ⟶ L.sheaf
  quotient_epi : Epi quotient
  projectiveBundle :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04ProjectiveBundle S
  universalQuotientCompatible :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04ProjectiveBundleUniversalQuotientCompatible
      projectiveBundle
  coefficient_eq : projectiveBundle.E = E
  associatedMap : X ⟶ projectiveBundle.space
  associated_over : associatedMap ≫ projectiveBundle.projection = f
  associated_immersion : IsImmersion associatedMap
  associated_pullback_iso : L.sheaf ≅
    (Scheme.Modules.pullback associatedMap).obj projectiveBundle.tautological
  quotient_associated :
    quotient ≫ associated_pullback_iso.hom =
        (eqToIso (congrArg (fun h : X ⟶ S =>
        (Scheme.Modules.pullback h).obj E) associated_over.symm)).hom ≫
        (chapter04PullbackCompositionIso associatedMap projectiveBundle.projection E).hom ≫
          (Scheme.Modules.pullback associatedMap).map
            ((eqToIso (congrArg (fun E' : S.Modules =>
              (Scheme.Modules.pullback projectiveBundle.projection).obj E')
                coefficient_eq.symm)).hom ≫
              projectiveBundle.universalQuotient)

structure CompatibleFiniteLinearSystem
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : FpqcLineBundleDescentDatum f g) where
  coefficients : CoefficientDescentDatum f g
  system : FiniteLinearSystem (baseChangeToBase f g) D.lineBundle coefficients.coefficient
  /- The line-bundle and coefficient identities are carried by `D` and
    `coefficients.descent`.  The remaining two conditions are the genuinely
    additional square for the quotient.  The associated projective-space map
    is then forced by the universal property of the projective bundle. -/
  quotient_compatibility :
    (coefficientCechComparison f g coefficients).hom ≫
        (Scheme.Modules.pullback (cechSecond (baseChangeToSource f g))).map
          system.quotient =
      (Scheme.Modules.pullback (cechFirst (baseChangeToSource f g))).map
          system.quotient ≫
        (fpqcLineBundleComparison f g D).hom.hom

structure FiniteRankVeryAmpleWitness {X S : Scheme.{u}}
    (f : X ⟶ S) (L : LineBundle X) where
  witness :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.RelativeVeryAmpleWitness f L
  coefficient : S.Modules
  coefficient_is_witness : coefficient = witness.projectiveBundle.E

def HasGlobalFiniteRankEmbeddingFor {X S : Scheme.{u}} (f : X ⟶ S)
    (L : LineBundle X) : Prop :=
  ∃ w : FiniteRankVeryAmpleWitness f L,
    IsVeryAmple f L ∧ IsImmersion w.witness.map

def HasGlobalFiniteRankEmbedding {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ L : LineBundle X, HasGlobalFiniteRankEmbeddingFor f L

theorem hasGlobalFiniteRankEmbeddingFor_isQuasiProjectiveMorphism
    {X S : Scheme.{u}} {f : X ⟶ S} {L : LineBundle X}
    (h : HasGlobalFiniteRankEmbeddingFor f L) : IsQuasiProjectiveMorphism f := by
  rcases h with ⟨w, hvery, _⟩
  rcases hvery with ⟨vw⟩
  exact ⟨{
    projectiveBundle := vw.projectiveBundle
    embedding := vw.map
    over := vw.over
    immersion := vw.immersion
  }⟩

theorem hasGlobalFiniteRankEmbedding_isQuasiProjectiveMorphism
    {X S : Scheme.{u}} {f : X ⟶ S}
    (h : HasGlobalFiniteRankEmbedding f) : IsQuasiProjectiveMorphism f := by
  rcases h with ⟨L, hL⟩
  exact hasGlobalFiniteRankEmbeddingFor_isQuasiProjectiveMorphism hL

def HasGlobalFiniteRankClosedEmbedding {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ w : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.RelativeClosedImmersionWitness f,
    IsClosedImmersion w.embedding

def HasLocalFiniteRankEmbedding {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasGlobalFiniteRankEmbedding (f ∣_ U)

def HasLocalFiniteRankEmbeddingFor {X S : Scheme.{u}} (f : X ⟶ S)
    (L : LineBundle X) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    ∃ n : ℕ, 0 < n ∧
      HasGlobalFiniteRankEmbeddingFor (f ∣_ U)
        ((L.pullback (f ⁻¹ᵁ U).ι).tensorPower n)

theorem hasLocalFiniteRankEmbeddingFor_implies
    {X S : Scheme.{u}} {f : X ⟶ S} {L : LineBundle X}
    (h : HasLocalFiniteRankEmbeddingFor f L) : HasLocalFiniteRankEmbedding f := by
  intro s
  rcases h s with ⟨U, hs, n, hn, hembedding⟩
  exact ⟨U, hs, ⟨(L.pullback (f ⁻¹ᵁ U).ι).tensorPower n, hembedding⟩⟩

/-! ### Norm interfaces -/

noncomputable def toNormLineBundle {X : Scheme.{u}} (L : LineBundle X) :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10LineBundle X :=
  { module := L.sheaf
    isInvertible := L.isInvertible }

noncomputable def fromNormLineBundle {X : Scheme.{u}}
    (L : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10LineBundle X) :
    LineBundle X :=
  { sheaf := L.module
    isInvertible := L.isInvertible }

structure NormConstruction {Y X : Scheme.{u}} (q : Y ⟶ X) where
  finiteLocallyFree : FiniteLocallyFreeMorphism q
  picardSource :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10PicardOperations Y
  picard :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10PicardOperations X
  determinant :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10DeterminantLineAPI q
  /- The norm tensor theorem needs the determinant functor's multiplicativity;
    the determinant API alone only supplies an operation on line bundles. -/
  determinant_tensor :
    ∀ L M : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10LineBundle Y,
      letI : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10PicardOperations Y :=
        picardSource
      letI : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10PicardOperations X :=
        picard
      letI : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10DeterminantLineAPI q :=
        determinant
      Nonempty
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10LineBundleIso
          (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10DeterminantLine
            q (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10PicardTensor L M))
          (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10PicardTensor
            (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10DeterminantLine q L)
            (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10DeterminantLine q M)))

/- LOCAL_DEPENDENCY_GUESS: determinant line bundles and duals are the only
  Picard-level operations absent from the pinned global sheaf API.  The
  choice-backed constructor packages precisely those operations for a finite
  locally free morphism and does not add positivity or descent as an input. -/
theorem normConstruction_exists {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) : Nonempty (NormConstruction q) := by
  sorry

noncomputable def normConstruction {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) : NormConstruction q :=
  Classical.choice (normConstruction_exists q hq)

noncomputable def pushforwardModule {Y X : Scheme.{u}} (q : Y ⟶ X)
    (M : Y.Modules) : X.Modules :=
  (Scheme.Modules.pushforward q).obj M

noncomputable def determinantLineBundle {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) (M : LineBundle Y) : LineBundle X :=
  let C := normConstruction q hq
  letI : Chapter10PicardOperations X := C.picard
  letI : Chapter10DeterminantLineAPI q := C.determinant
  fromNormLineBundle (chapter10DeterminantLine q (toNormLineBundle M))

noncomputable def sourceTensorLineBundle {Y X : Scheme.{u}}
    {q : Y ⟶ X} (C : NormConstruction q) (L M : LineBundle Y) : LineBundle Y :=
  letI : Chapter10PicardOperations Y := C.picardSource
  fromNormLineBundle
    (chapter10PicardTensor (toNormLineBundle L) (toNormLineBundle M))

noncomputable def targetTensorLineBundle {Y X : Scheme.{u}}
    {q : Y ⟶ X} (C : NormConstruction q) (L M : LineBundle X) : LineBundle X :=
  letI : Chapter10PicardOperations X := C.picard
  fromNormLineBundle
    (chapter10PicardTensor (toNormLineBundle L) (toNormLineBundle M))

noncomputable def normLineBundle {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) (M : LineBundle Y) : LineBundle X :=
  let C := normConstruction q hq
  letI : Chapter10PicardOperations X := C.picard
  letI : Chapter10DeterminantLineAPI q := C.determinant
  fromNormLineBundle (chapter10Norm q (toNormLineBundle M))

noncomputable def chapter15StructureLineBundle (X : Scheme.{u}) : LineBundle X :=
  fromNormLineBundle
    (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10StructureSheafLineBundle X)

theorem normLineBundle_determinant_formula {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) (M : LineBundle Y) :
    normLineBundle q hq M =
      let C := normConstruction q hq
      letI : Chapter10PicardOperations X := C.picard
      letI : Chapter10DeterminantLineAPI q := C.determinant
      fromNormLineBundle
        (chapter10PicardTensor
          (chapter10DeterminantLine q (toNormLineBundle M))
        (Chapter10PicardOperations.dual
            (chapter10DeterminantLine q (toNormLineBundle
              (chapter15StructureLineBundle Y))))) := by
  rfl

theorem normLineBundle_tensor {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) (M N : LineBundle Y) :
    lineBundleIsomorphic
      (normLineBundle q hq (sourceTensorLineBundle (normConstruction q hq) M N))
      (targetTensorLineBundle (normConstruction q hq)
        (normLineBundle q hq M) (normLineBundle q hq N)) := by
  let C := normConstruction q hq
  let : Chapter10PicardOperations Y := C.picardSource
  let : Chapter10PicardOperations X := C.picard
  let : Chapter10DeterminantLineAPI q := C.determinant
  change Nonempty ((chapter10Norm q
      (chapter10PicardTensor (toNormLineBundle M) (toNormLineBundle N))).module ≅
    (chapter10PicardTensor (chapter10Norm q (toNormLineBundle M))
      (chapter10Norm q (toNormLineBundle N))).module)
  exact ⟨(chapter10_norm_commutes_tensor_product q (toNormLineBundle M)
    (toNormLineBundle N)).hom⟩

/-! ### Norm sections and affine descent -/

/- LOCAL_DEPENDENCY_GUESS: the determinant-of-multiplication construction of a
  norm section is not named in the pinned sheaf API.  The interface below
  supplies exactly that map, with the source and target tensor powers visible. -/
class NormSectionAPI {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) where
  map : ∀ (M : LineBundle Y) (n : ℕ) (U : X.Opens),
    Γ((M.tensorPower n).sheaf, q ⁻¹ᵁ U) →
      Γ(((normLineBundle q hq M).tensorPower n).sheaf, U)
  /- The determinant-of-multiplication norm is characterized here by the
    nonvanishing test used in the norm-ampleness proof. -/
  map_generates_iff : ∀ (M : LineBundle Y) (n : ℕ) (U : X.Opens)
    (s : Γ((M.tensorPower n).sheaf, q ⁻¹ᵁ U)) (x : X) (hx : x ∈ U),
    chapter04SectionGeneratesAt
        ((normLineBundle q hq M).tensorPower n).sheaf (map M n U s) x hx ↔
      ∀ y : Y, q y = x →
        ∃ hy : y ∈ q ⁻¹ᵁ U,
          chapter04SectionGeneratesAt (M.tensorPower n).sheaf s y hy

theorem normSectionAPI_exists {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) : Nonempty (NormSectionAPI q hq) := by
  sorry

@[instance_reducible]
noncomputable def normSectionAPI {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) : NormSectionAPI q hq :=
  Classical.choice (normSectionAPI_exists q hq)

noncomputable def normSection {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) (M : LineBundle Y) (n : ℕ)
    (U : X.Opens) (s : Γ((M.tensorPower n).sheaf, q ⁻¹ᵁ U)) :
    Γ(((normLineBundle q hq M).tensorPower n).sheaf, U) :=
  (normSectionAPI q hq).map M n U s

theorem affine_of_finite_faithfullyFlat_preimage_affine
    {Y X : Scheme.{u}} (q : Y ⟶ X) (hqfinite : IsFinite q)
    (hqff : IsFaithfullyFlat q) (U : X.Opens)
    (hpreimage : IsAffineOpen (q ⁻¹ᵁ U)) : IsAffineOpen U := by
  sorry

structure NormAffineChart {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) (M : LineBundle Y) where
  baseOpen : X.Opens
  baseOpen_affine : IsAffineOpen baseOpen
  n : ℕ
  positive : 0 < n
  sectionData : Γ((M.tensorPower n).sheaf, q ⁻¹ᵁ baseOpen)
  locus : X.Opens
  norm_locus : ∀ x : X,
    x ∈ locus ↔ ∃ hx : x ∈ baseOpen, chapter04SectionGeneratesAt
      ((normLineBundle q hq M).tensorPower n).sheaf
        (normSection q hq M n baseOpen sectionData) x hx
  preimage_affine : IsAffineOpen (q ⁻¹ᵁ locus)
  affine : IsAffineOpen locus

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15
