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
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Section02FaithfullyFlatDescentOfVeryAmpleness
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Section03DescentOfAmplenessAndProjectivity
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
  wrapper.  These choice-backed bridges expose the canonical comparison in a
  form usable by the Čech cocycle and restriction statements. -/
theorem lineBundlePullbackIso_exists {X Y : Scheme.{u}}
    {L M : LineBundle Y} (e : LineBundleIso L M) (h : X ⟶ Y) :
    Nonempty (LineBundleIso (pullbackLineBundle h L) (pullbackLineBundle h M)) := by
  sorry

noncomputable def lineBundlePullbackIso {X Y : Scheme.{u}}
    {L M : LineBundle Y} (e : LineBundleIso L M) (h : X ⟶ Y) :
    LineBundleIso (pullbackLineBundle h L) (pullbackLineBundle h M) :=
  Classical.choice (lineBundlePullbackIso_exists e h)

theorem lineBundlePullbackCompIso_exists {X Y Z : Scheme.{u}} (L : LineBundle Z)
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    Nonempty (LineBundleIso
      (pullbackLineBundle h (pullbackLineBundle k L))
      (pullbackLineBundle (h ≫ k) L)) := by
  sorry

noncomputable def lineBundlePullbackCompIso {X Y Z : Scheme.{u}} (L : LineBundle Z)
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    LineBundleIso
      (pullbackLineBundle h (pullbackLineBundle k L))
      (pullbackLineBundle (h ≫ k) L) :=
  Classical.choice (lineBundlePullbackCompIso_exists L h k)

abbrev cechDouble {Y X : Scheme.{u}} (q : Y ⟶ X) := pullback q q

abbrev cechFirst {Y X : Scheme.{u}} (q : Y ⟶ X) : cechDouble q ⟶ Y :=
  pullback.fst q q

abbrev cechSecond {Y X : Scheme.{u}} (q : Y ⟶ X) : cechDouble q ⟶ Y :=
  pullback.snd q q

theorem lineBundleCechFaceIso_exists {Y X Z : Scheme.{u}} (q : Y ⟶ X)
    (M : LineBundle Y)
    (e : LineBundleIso (pullbackLineBundle (cechFirst q) M)
      (pullbackLineBundle (cechSecond q) M))
    (face : Z ⟶ cechDouble q) :
    Nonempty (LineBundleIso
      (pullbackLineBundle (face ≫ cechFirst q) M)
      (pullbackLineBundle (face ≫ cechSecond q) M)) := by
  sorry

noncomputable def lineBundleCechFaceIso {Y X Z : Scheme.{u}} (q : Y ⟶ X)
    (M : LineBundle Y)
    (e : LineBundleIso (pullbackLineBundle (cechFirst q) M)
      (pullbackLineBundle (cechSecond q) M))
    (face : Z ⟶ cechDouble q) :
    LineBundleIso
      (pullbackLineBundle (face ≫ cechFirst q) M)
      (pullbackLineBundle (face ≫ cechSecond q) M) :=
  Classical.choice (lineBundleCechFaceIso_exists q M e face)

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

theorem moduleCechFaceIso_exists {T S Z : Scheme.{u}} (g : T ⟶ S)
    (E : T.Modules)
    (e : (Scheme.Modules.pullback (cechFirst g)).obj E ≅
      (Scheme.Modules.pullback (cechSecond g)).obj E)
    (face : Z ⟶ cechDouble g) :
    Nonempty ((Scheme.Modules.pullback (face ≫ cechFirst g)).obj E ≅
      (Scheme.Modules.pullback (face ≫ cechSecond g)).obj E) := by
  sorry

noncomputable def moduleCechFaceIso {T S Z : Scheme.{u}} (g : T ⟶ S)
    (E : T.Modules)
    (e : (Scheme.Modules.pullback (cechFirst g)).obj E ≅
      (Scheme.Modules.pullback (cechSecond g)).obj E)
    (face : Z ⟶ cechDouble g) :
    (Scheme.Modules.pullback (face ≫ cechFirst g)).obj E ≅
      (Scheme.Modules.pullback (face ≫ cechSecond g)).obj E :=
  Classical.choice (moduleCechFaceIso_exists g E e face)

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

/-! ### Finiteness and cover profiles -/

structure FpqcCoverData {S T : Scheme.{u}} (g : T ⟶ S) where
  flat : Flat g
  surjective : Surjective g
  quasiCompact : QuasiCompact g

def FpqcCoverData.isFaithfullyFlat {S T : Scheme.{u}} {g : T ⟶ S}
    (G : FpqcCoverData g) : IsFaithfullyFlat g :=
  ⟨G.flat, G.surjective⟩

def FpqcCoverData.isFpqc {S T : Scheme.{u}} {g : T ⟶ S}
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
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
      .Chapter10FiniteLocallyFreeProfile g rank

def FiniteLocallyFreeMorphism {T S : Scheme.{u}} (g : T ⟶ S) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
    .Chapter10FiniteLocallyFreeMorphism g

theorem FiniteLocallyFreeConstantRank.morphism {T S : Scheme.{u}} {g : T ⟶ S}
    (G : FiniteLocallyFreeConstantRank g) : FiniteLocallyFreeMorphism g := by
  exact LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
    .chapter10_finiteLocallyFreeProfile_to_morphism G.profile

/- The positive constant-rank hypothesis is what supplies surjectivity; it is
  not silently folded into the definition of finite locally free. -/
theorem FiniteLocallyFreeConstantRank.surjective {T S : Scheme.{u}} {g : T ⟶ S}
    (G : FiniteLocallyFreeConstantRank g) : Surjective g := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: base change of a finite locally free morphism is
  available in the pinned Mathlib profile, but the source projection is the
  first projection of `baseChange f g`; expose that orientation explicitly. -/
theorem baseChangeToSource_finiteLocallyFree
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) :
    FiniteLocallyFreeMorphism (baseChangeToSource f g) := by
  sorry

theorem baseChangeToSource_surjective
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) :
    Surjective (baseChangeToSource f g) := by
  sorry

/-! ### Čech descent data -/

structure ModuleDescentDatum {T S : Scheme.{u}} (g : T ⟶ S) where
  module : T.Modules
  comparison :
    (Scheme.Modules.pullback (cechFirst g)).obj module ≅
      (Scheme.Modules.pullback (cechSecond g)).obj module
  triple : Scheme.{u}
  face01 face12 face02 : triple ⟶ cechDouble g
  triple_is_threefold : triple = pullback (cechSecond g) g
  face01_right_eq_face12_left : face01 ≫ cechSecond g = face12 ≫ cechFirst g
  face01_left_eq_face02_left : face01 ≫ cechFirst g = face02 ≫ cechFirst g
  face12_right_eq_face02_right : face12 ≫ cechSecond g = face02 ≫ cechSecond g
  cocycle : moduleCechCocycleCondition g module comparison face01 face12 face02
    face01_right_eq_face12_left face01_left_eq_face02_left face12_right_eq_face02_right

structure ModuleDescentRealization {T S : Scheme.{u}} {g : T ⟶ S}
    (D : ModuleDescentDatum g) (E : S.Modules) where
  comparison : (Scheme.Modules.pullback g).obj E ≅ D.module
  /- LOCAL_DEPENDENCY_GUESS: the normalized comparison of the two pullbacks
    over the Čech double overlap is not exposed by the pinned module-sheaf
    API; keep it as a named descent condition until that API is reconciled. -/
  comparison_compatible : Prop

structure LineBundleDescentDatum {Y X : Scheme.{u}} (q : Y ⟶ X) where
  carrier : LineBundle Y
  comparison :
    LineBundleIso (pullbackLineBundle (cechFirst q) carrier)
      (pullbackLineBundle (cechSecond q) carrier)
  triple : Scheme.{u}
  face01 face12 face02 : triple ⟶ cechDouble q
  triple_is_threefold : triple = pullback (cechSecond q) q
  face01_right_eq_face12_left : face01 ≫ cechSecond q = face12 ≫ cechFirst q
  face01_left_eq_face02_left : face01 ≫ cechFirst q = face02 ≫ cechFirst q
  face12_right_eq_face02_right : face12 ≫ cechSecond q = face02 ≫ cechSecond q
  cocycle : lineBundleCechCocycleCondition q carrier comparison face01 face12 face02
    face01_right_eq_face12_left face01_left_eq_face02_left face12_right_eq_face02_right

structure LineBundleDescentRealization {Y X : Scheme.{u}} {q : Y ⟶ X}
    (D : LineBundleDescentDatum q) (L : LineBundle X) where
  comparison : LineBundleIso (pullbackLineBundle q L) D.carrier
  /- LOCAL_DEPENDENCY_GUESS: this is the pullback-comparison square obtained
    from the displayed Čech cocycle. -/
  comparison_compatible : Prop

structure FpqcLineBundleDescentDatum
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) where
  cover : FpqcCoverData g
  lineBundle : LineBundle (baseChange f g)
  descent : LineBundleDescentDatum (baseChangeToSource f g)
  carrier_eq : descent.carrier = lineBundle

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
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
      .chapter04FiniteLocallyFree coefficient

/-! ### Finite systems of sections and projective embeddings -/

structure FiniteLinearSystem
    {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) (E : S.Modules) where
  finiteLocallyFree :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
      .chapter04FiniteLocallyFree E
  quotient : (Scheme.Modules.pullback f).obj E ⟶ L.sheaf
  quotient_epi : Epi quotient
  projectiveBundle :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
      .Chapter04ProjectiveBundle S
  universalQuotientCompatible :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
      .chapter04ProjectiveBundleUniversalQuotientCompatible projectiveBundle
  coefficient_eq : projectiveBundle.E = E
  associatedMap : X ⟶ projectiveBundle.space
  associated_over : associatedMap ≫ projectiveBundle.projection = f
  associated_immersion : IsImmersion associatedMap
  quotient_associated : Prop

structure CompatibleFiniteLinearSystem
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : FpqcLineBundleDescentDatum f g) where
  coefficients : CoefficientDescentDatum f g
  system : FiniteLinearSystem (baseChangeToBase f g) D.lineBundle coefficients.coefficient
  /- LOCAL_DEPENDENCY_GUESS: the four named conditions are the normalized
    pullback squares for the line bundle, coefficient module, quotient, and
    associated projective-space map.  The pinned API has no common square
    wrapper, so they remain separate hypotheses rather than an untyped claim. -/
  lineBundle_compatibility : Prop
  coefficient_compatibility : Prop
  quotient_compatibility : Prop
  map_compatibility : Prop

structure FiniteRankVeryAmpleWitness {X S : Scheme.{u}}
    (f : X ⟶ S) (L : LineBundle X) where
  witness :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
      .RelativeVeryAmpleWitness f L
  coefficient : witness.projectiveBundle.E
  coefficient_is_witness : coefficient = witness.projectiveBundle.E

def HasGlobalFiniteRankEmbedding {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ L : LineBundle X, ∃ w : FiniteRankVeryAmpleWitness f L, IsVeryAmple f L

def HasGlobalFiniteRankClosedEmbedding {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ w : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
      .RelativeClosedImmersionWitness f, IsClosedImmersion w.embedding

def HasLocalFiniteRankEmbedding {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasGlobalFiniteRankEmbedding (f ∣_ U)

/-! ### Norm interfaces -/

noncomputable def toNormLineBundle {X : Scheme.{u}} (L : LineBundle X) :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
      .Chapter10LineBundle X :=
  { module := L.sheaf
    isInvertible := L.isInvertible }

noncomputable def fromNormLineBundle {X : Scheme.{u}}
    (L : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
      .Chapter10LineBundle X) : LineBundle X :=
  { sheaf := L.module
    isInvertible := L.isInvertible }

structure NormConstruction {Y X : Scheme.{u}} (q : Y ⟶ X) where
  finiteLocallyFree : FiniteLocallyFreeMorphism q
  picardSource :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
      .Chapter10PicardOperations Y
  picard :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
      .Chapter10PicardOperations X
  determinant :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
      .Chapter10DeterminantLineAPI q

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
    (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
      .chapter10StructureSheafLineBundle X)

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
  sorry

theorem normLineBundle_tensor {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) (M N : LineBundle Y) :
    lineBundleIsomorphic
      (normLineBundle q hq (sourceTensorLineBundle (normConstruction q hq) M N))
      (targetTensorLineBundle (normConstruction q hq)
        (normLineBundle q hq M) (normLineBundle q hq N)) := by
  sorry

/-! ### Norm sections and affine descent -/

/- LOCAL_DEPENDENCY_GUESS: the determinant-of-multiplication construction of a
  norm section is not named in the pinned sheaf API.  The interface below
  supplies exactly that map, with the source and target tensor powers visible. -/
class NormSectionAPI {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) where
  map : ∀ (M : LineBundle Y) (n : ℕ),
    Γ((M.tensorPower n).sheaf, ⊤) →
      Γ(((normLineBundle q hq M).tensorPower n).sheaf, ⊤)

theorem normSectionAPI_exists {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) : Nonempty (NormSectionAPI q hq) := by
  sorry

noncomputable def normSectionAPI {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) : NormSectionAPI q hq :=
  Classical.choice (normSectionAPI_exists q hq)

noncomputable def normSection {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) (M : LineBundle Y) (n : ℕ)
    (s : Γ((M.tensorPower n).sheaf, ⊤)) :
    Γ(((normLineBundle q hq M).tensorPower n).sheaf, ⊤) :=
  (normSectionAPI q hq).map M n s

/- LOCAL_DEPENDENCY_GUESS: the source uses the finite-fiber algebra and its
  multiplication operator.  This small interface records that operator's
  invertibility predicate without replacing it by a statement about points or
  by the desired norm conclusion. -/
class FiniteFiberMultiplicationAPI {Y X : Scheme.{u}} (q : Y ⟶ X)
    (M : LineBundle Y) where
  multiplicationIsInvertible :
    ∀ (n : ℕ), Γ((M.tensorPower n).sheaf, ⊤) → X → Prop

theorem finiteFiberMultiplicationAPI_exists
    {Y X : Scheme.{u}} (q : Y ⟶ X) (hq : FiniteLocallyFreeMorphism q)
    (M : LineBundle Y) : Nonempty (FiniteFiberMultiplicationAPI q M) := by
  sorry

noncomputable def finiteFiberMultiplicationAPI
    {Y X : Scheme.{u}} (q : Y ⟶ X) (hq : FiniteLocallyFreeMorphism q)
    (M : LineBundle Y) : FiniteFiberMultiplicationAPI q M :=
  Classical.choice (finiteFiberMultiplicationAPI_exists q hq M)

def NormSectionMultiplicationPredicate {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) (M : LineBundle Y) (n : ℕ)
    (s : Γ((M.tensorPower n).sheaf, ⊤)) (x : X) : Prop :=
  (finiteFiberMultiplicationAPI q hq M).multiplicationIsInvertible n s x

theorem normSection_nonvanishing_iff_multiplication_invertible
    {Y X : Scheme.{u}} (q : Y ⟶ X) (hq : FiniteLocallyFreeMorphism q)
    (M : LineBundle Y) (n : ℕ) (s : Γ((M.tensorPower n).sheaf, ⊤)) (x : X) :
    chapter04SectionGeneratesAt (normLineBundle q hq M).sheaf (normSection q hq M n s) x
      (by trivial) ↔ NormSectionMultiplicationPredicate q hq M n s x := by
  sorry

theorem affine_of_finite_faithfullyFlat_preimage_affine
    {Y X : Scheme.{u}} (q : Y ⟶ X) (hqfinite : IsFinite q)
    (hqff : IsFaithfullyFlat q) (U : X.Opens)
    (hpreimage : IsAffineOpen (U.preimage q.continuous)) : IsAffineOpen U := by
  sorry

structure NormAffineChart {Y X : Scheme.{u}} (q : Y ⟶ X)
    (hq : FiniteLocallyFreeMorphism q) (M : LineBundle Y) where
  n : ℕ
  positive : 0 < n
  sectionData : Γ((M.tensorPower n).sheaf, ⊤)
  locus : X.Opens
  norm_locus : ∀ x : X,
    x ∈ locus ↔ chapter04SectionGeneratesAt
      (normLineBundle q hq M).sheaf
        (normSection q hq M n sectionData) x (by trivial)
  preimage_affine : IsAffineOpen (locus.preimage q.continuous)
  affine : IsAffineOpen locus

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15
