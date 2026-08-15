import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.RingHom.Flat
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Section05TensorPowersAndOperations

/-!
# Chapter 5: base change and descent

This file contains the book-facing interfaces used by the four sections of the chapter.  The
scheme-theoretic operations are the pinned Mathlib operations; the positivity vocabulary is kept
small so that it can be replaced by the canonical line-bundle API supplied by the earlier chapters.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05

noncomputable section

/- LOCAL_DEPENDENCY_GUESS: Mathlib exposes `Flat` and `Surjective` separately for scheme
morphisms, while the book uses the combined phrase faithfully flat.  This is the weakest
book-facing proposition needed in this chapter. -/
def IsFaithfullyFlat {S T : Scheme.{u}} (g : T ⟶ S) : Prop :=
  Flat g ∧ Surjective g

def IsFpqcCover {S T : Scheme.{u}} (g : T ⟶ S) : Prop :=
  IsFaithfullyFlat g ∧ QuasiCompact g

/- The preceding chapter supplies the book-facing line-bundle interface.  Reusing it is important
for coherence: the tensor powers, affine-open definition of ampleness, and projective-bundle
tautological sheaf must all refer to the same invertible-sheaf object. -/
abbrev IsInvertibleSheaf (X : Scheme.{u}) (M : X.Modules) : Prop :=
  Chapter04.chapter04IsInvertible M

abbrev LineBundle (X : Scheme.{u}) := Chapter04.Chapter04LineBundle X

abbrev LineBundle.sheaf {X : Scheme.{u}} (L : LineBundle X) : X.Modules :=
  Chapter04.Chapter04LineBundle.sheaf L

instance {X : Scheme.{u}} : Coe (LineBundle X) X.Modules := ⟨LineBundle.sheaf⟩

noncomputable def LineBundle.trivial (X : Scheme.{u}) : LineBundle X :=
  Chapter04.chapter04TrivialLineBundle X

def LineBundle.Isomorphic {X : Scheme.{u}} (L M : LineBundle X) : Prop :=
  Nonempty (L.sheaf ≅ M.sheaf)

@[ext]
theorem LineBundle.ext {X : Scheme.{u}} {L M : LineBundle X}
    (h : L.sheaf = M.sheaf) : L = M := by
  cases L
  cases M
  cases h
  rfl

theorem lineBundle_isomorphic_refl {X : Scheme.{u}} (L : LineBundle X) :
    L.Isomorphic L :=
  ⟨Iso.refl _⟩

theorem lineBundle_isomorphic_symm {X : Scheme.{u}} {L M : LineBundle X}
    (h : L.Isomorphic M) : M.Isomorphic L := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

theorem lineBundle_isomorphic_trans {X : Scheme.{u}} {L M N : LineBundle X}
    (hLM : L.Isomorphic M) (hMN : M.Isomorphic N) : L.Isomorphic N := by
  rcases hLM with ⟨eLM⟩
  rcases hMN with ⟨eMN⟩
  exact ⟨eLM ≪≫ eMN⟩

noncomputable def LineBundle.pullback {X Y : Scheme.{u}} (L : LineBundle Y) (f : X ⟶ Y) :
    LineBundle X :=
  Chapter04.chapter04PullbackLineBundle f L

@[simp]
theorem LineBundle.pullback_sheaf {X Y : Scheme.{u}} (L : LineBundle Y) (f : X ⟶ Y) :
    (L.pullback f).sheaf = (Scheme.Modules.pullback f).obj L.sheaf := rfl

theorem lineBundle_pullback_id {X : Scheme.{u}} (L : LineBundle X) :
    (L.pullback (𝟙 X)).Isomorphic L := by
  exact ⟨(Scheme.Modules.pullbackId X).app L.sheaf⟩

theorem lineBundle_pullback_comp {X Y Z : Scheme.{u}} (L : LineBundle Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((L.pullback g).pullback f).Isomorphic (L.pullback (f ≫ g)) := by
  exact ⟨(Chapter04.chapter04PullbackCompositionIso f g L.sheaf).symm⟩

theorem lineBundle_isomorphic_pullback {X Y : Scheme.{u}} {L M : LineBundle Y}
    (hLM : L.Isomorphic M) (f : X ⟶ Y) :
    (L.pullback f).Isomorphic (M.pullback f) := by
  rcases hLM with ⟨e⟩
  exact ⟨(Scheme.Modules.pullback f).mapIso e⟩

noncomputable def LineBundle.tensorPower {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) :
    LineBundle X :=
  Chapter04.chapter04LineBundleTensorPower L n

/- Pullback compatibility is the coherence bridge used when a power system is transported to a
base change. -/
theorem lineBundle_pullback_tensorPower {X Y : Scheme.{u}} (L : LineBundle Y)
    (f : X ⟶ Y) (n : ℕ) :
    ((L.tensorPower n).pullback f).Isomorphic ((L.pullback f).tensorPower n) := by sorry

/- A power system must identify every indexed object with the actual tensor power.  Merely
specifying degrees zero and one would allow an unrelated bundle in every higher degree and would
make the positive-power descent assertions vacuous. -/
structure LineBundlePowers {X : Scheme.{u}} (L : LineBundle X) where
  power : ℕ → LineBundle X
  power_iso : ∀ n, (power n).Isomorphic (L.tensorPower n)

noncomputable def LineBundlePowers.pullback {X Y : Scheme.{u}} {L : LineBundle Y}
    (P : LineBundlePowers L) (f : X ⟶ Y) : LineBundlePowers (L.pullback f) where
  power n := (P.power n).pullback f
  power_iso := by
    intro n
    exact lineBundle_isomorphic_trans
      (lineBundle_isomorphic_pullback (P.power_iso n) f)
      (lineBundle_pullback_tensorPower L f n)

noncomputable def chapter04QuotientClassMapEquiv
    {S : Scheme.{u}} {E F : S.Modules} (e : E ≅ F) :
    Chapter04.Chapter04InvertibleQuotientClass E ≃
      Chapter04.Chapter04InvertibleQuotientClass F := by
  let forward :
      Chapter04.Chapter04InvertibleQuotientClass E →
        Chapter04.Chapter04InvertibleQuotientClass F :=
    Quotient.lift
      (fun p => Chapter04.chapter04QuotientClassMk
        { line := p.line
          quotient := e.inv ≫ p.quotient
          quotient_is_epi := by
            exact epi_comp' (by infer_instance) p.quotient_is_epi }) (by
        intro p q hp
        apply Quotient.sound
        obtain ⟨a, ha⟩ := hp
        refine ⟨a, ?_⟩
        change (e.inv ≫ p.quotient) ≫ a.hom = e.inv ≫ q.quotient
        rw [Category.assoc, ha])
  let backward :
      Chapter04.Chapter04InvertibleQuotientClass F →
        Chapter04.Chapter04InvertibleQuotientClass E :=
    Quotient.lift
      (fun p => Chapter04.chapter04QuotientClassMk
        { line := p.line
          quotient := e.hom ≫ p.quotient
          quotient_is_epi := by
            exact epi_comp' (by infer_instance) p.quotient_is_epi }) (by
        intro p q hp
        apply Quotient.sound
        obtain ⟨a, ha⟩ := hp
        refine ⟨a, ?_⟩
        change (e.hom ≫ p.quotient) ≫ a.hom = e.hom ≫ q.quotient
        rw [Category.assoc, ha])
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro p
        refine Quotient.inductionOn p (fun q => ?_)
        apply Quotient.sound
        refine ⟨Iso.refl _, ?_⟩
        simp
      right_inv := by
        intro p
        refine Quotient.inductionOn p (fun q => ?_)
        apply Quotient.sound
        refine ⟨Iso.refl _, ?_⟩
        simp }

theorem chapter04PullbackQuotientClassAlong_mapEquiv
    {S T U : Scheme.{u}} (f : T ⟶ S) (h : U ⟶ T)
    {E F : S.Modules} (e : E ≅ F)
    (q : Chapter04.Chapter04InvertibleQuotientClass
      ((Scheme.Modules.pullback f).obj E)) :
    Chapter04.chapter04PullbackQuotientClassAlong f h
        (chapter04QuotientClassMapEquiv ((Scheme.Modules.pullback f).mapIso e) q) =
      chapter04QuotientClassMapEquiv
        ((Scheme.Modules.pullback (h ≫ f)).mapIso e)
        (Chapter04.chapter04PullbackQuotientClassAlong f h q) := by
  refine Quotient.inductionOn q (fun p => ?_)
  apply Quotient.sound
  refine ⟨Iso.refl _, ?_⟩
  change
    ((Chapter04.chapter04PullbackCompositionIso h f F).hom ≫
        (Scheme.Modules.pullback h).map
          ((Scheme.Modules.pullback f).map e.inv ≫ p.quotient)) ≫ (Iso.refl _).hom =
      (Scheme.Modules.pullback (h ≫ f)).map e.inv ≫
        (Chapter04.chapter04PullbackCompositionIso h f E).hom ≫
          (Scheme.Modules.pullback h).map p.quotient
  simp only [Iso.refl_hom, Category.comp_id]
  have hn :
      (Scheme.Modules.pullback (h ≫ f)).map e.inv ≫
          (Chapter04.chapter04PullbackCompositionIso h f E).hom =
        (Chapter04.chapter04PullbackCompositionIso h f F).hom ≫
          (Scheme.Modules.pullback h).map ((Scheme.Modules.pullback f).map e.inv) := by
    exact (Scheme.Modules.pullbackComp h f).inv.naturality e.inv
  rw [(Scheme.Modules.pullback h).map_comp, ← Category.assoc, ← hn]
  simp only [Category.assoc]

noncomputable def chapter04BaseChangePointEquiv
    {S T U : Scheme.{u}} (P : Chapter04.Chapter04ProjectiveBundle S)
    (g : T ⟶ S) (f : U ⟶ T) :
    {u : U ⟶ pullback P.projection g // u ≫ pullback.snd P.projection g = f} ≃
      {v : U ⟶ P.space // v ≫ P.projection = f ≫ g} :=
  { toFun := fun u =>
      ⟨u.1 ≫ pullback.fst P.projection g, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, u.2]⟩
    invFun := fun v =>
      ⟨pullback.lift v.1 f v.2, pullback.lift_snd _ _ _⟩
    left_inv := by
      intro u
      apply Subtype.ext
      apply pullback.hom_ext
      · exact pullback.lift_fst _ _ _
      · exact (pullback.lift_snd
          (f := P.projection) (g := g)
          (u.1 ≫ pullback.fst P.projection g) f _).trans u.2.symm
    right_inv := by
      intro v
      apply Subtype.ext
      exact pullback.lift_fst _ _ _ }

/- Reuse the preceding chapter's projective-bundle interface.  In particular, the ambient object
carries the finite locally free module, its structure morphism, and its tautological line bundle;
the source-order `ambient` name below is only a vocabulary adapter. -/
abbrev RelativeProjectiveBundleData (S : Scheme.{u}) :=
  Chapter04.Chapter04ProjectiveBundle S

abbrev RelativeProjectiveBundleData.ambient {S : Scheme.{u}}
    (P : RelativeProjectiveBundleData S) : Scheme.{u} :=
  P.space

abbrev RelativeProjectiveBundleData.projection {S : Scheme.{u}}
    (P : RelativeProjectiveBundleData S) : P.ambient ⟶ S :=
  Chapter04.Chapter04ProjectiveBundle.projection P

noncomputable def RelativeProjectiveBundleData.baseChange
    {S T : Scheme.{u}} (P : RelativeProjectiveBundleData S) (g : T ⟶ S) :
    RelativeProjectiveBundleData T where
  E := (Scheme.Modules.pullback g).obj P.E
  finiteLocallyFree := by sorry
  space := pullback (Chapter04.Chapter04ProjectiveBundle.projection P) g
  projection := pullback.snd (Chapter04.Chapter04ProjectiveBundle.projection P) g
  tautological :=
    (Scheme.Modules.pullback
      (pullback.fst (Chapter04.Chapter04ProjectiveBundle.projection P) g)).obj P.tautological
  tautological_isInvertible := by
    exact (Chapter04.chapter04PullbackLineBundle
      (pullback.fst (Chapter04.Chapter04ProjectiveBundle.projection P) g)
      { sheaf := P.tautological
        isInvertible := P.tautological_isInvertible }).isInvertible
  universalQuotient :=
    (Chapter04.chapter04PullbackCompositionIso
        (pullback.snd (Chapter04.Chapter04ProjectiveBundle.projection P) g) g P.E).inv ≫
      (Scheme.Modules.pullbackCongr
        (f := pullback.snd (Chapter04.Chapter04ProjectiveBundle.projection P) g ≫ g)
        (g := pullback.fst (Chapter04.Chapter04ProjectiveBundle.projection P) g ≫
          Chapter04.Chapter04ProjectiveBundle.projection P)
        pullback.condition.symm).hom.app P.E ≫
      (Chapter04.chapter04PullbackCompositionIso
          (pullback.fst (Chapter04.Chapter04ProjectiveBundle.projection P) g)
          (Chapter04.Chapter04ProjectiveBundle.projection P) P.E).hom ≫
      (Scheme.Modules.pullback
        (pullback.fst (Chapter04.Chapter04ProjectiveBundle.projection P) g)).map
        P.universalQuotient
  universalQuotient_is_epi := by
    let _ : Epi ((Scheme.Modules.pullback
        (pullback.fst (Chapter04.Chapter04ProjectiveBundle.projection P) g)).map
        P.universalQuotient) :=
      @Functor.map_epi _ _ _ _
        (Scheme.Modules.pullback
          (pullback.fst (Chapter04.Chapter04ProjectiveBundle.projection P) g))
        (Functor.preservesEpimorphisms_of_adjunction
          (Scheme.Modules.pullbackPushforwardAdjunction
            (pullback.fst (Chapter04.Chapter04ProjectiveBundle.projection P) g)))
        _ _ P.universalQuotient P.universalQuotient_is_epi
    infer_instance
  universal_equiv := by
    intro U f
    exact (chapter04BaseChangePointEquiv P g f).trans
      ((P.universal_equiv (f ≫ g)).trans
        (chapter04QuotientClassMapEquiv
          (Chapter04.chapter04PullbackCompositionIso f g P.E)))
  universal_natural := by sorry
  projection_isProper := by
    infer_instance

def IsFiniteDimensionalLocallyOnBase {S : Scheme.{u}}
    (P : RelativeProjectiveBundleData S) : Prop :=
  Chapter04.chapter04FiniteLocallyFree P.E

theorem relativeProjectiveBundleData_finiteDimensional {S : Scheme.{u}}
    (P : RelativeProjectiveBundleData S) : IsFiniteDimensionalLocallyOnBase P :=
  P.finiteLocallyFree

structure RelativeImmersionWitness {X S : Scheme.{u}} (f : X ⟶ S) where
  projectiveBundle : RelativeProjectiveBundleData S
  embedding : X ⟶ projectiveBundle.ambient
  over : embedding ≫ projectiveBundle.projection = f
  immersion : IsImmersion embedding

abbrev RelativeClosedImmersionWitness {X S : Scheme.{u}} (f : X ⟶ S) :=
  Chapter04.Chapter04ProjectiveWitness f

abbrev RelativeClosedImmersionWitness.embedding {X S : Scheme.{u}} {f : X ⟶ S}
    (w : RelativeClosedImmersionWitness f) : X ⟶ w.projectiveBundle.space :=
  w.map

abbrev RelativeVeryAmpleWitness {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) :=
  Chapter04.Chapter04VeryAmpleWitness f L

abbrev RelativeVeryAmpleWitness.embedding {X S : Scheme.{u}} {f : X ⟶ S}
    {L : LineBundle X} (w : RelativeVeryAmpleWitness f L) : X ⟶ w.projectiveBundle.space :=
  w.map

abbrev IsVeryAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  Chapter04.chapter04VeryAmple f L

def IsQuasiProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Nonempty (RelativeImmersionWitness f)

abbrev IsProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter04.chapter04Projective f

/- Use the affine nonvanishing definition from Chapter 4 rather than replacing ampleness by a
cover of the base on which some power is very ample.  The latter is only equivalent under extra
finite-presentation hypotheses and is not the source definition. -/
abbrev RelativeAmpleWitness {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) :=
  Chapter04.Chapter04AmpleWitness f L

abbrev IsAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  Chapter04.chapter04Ample f L

theorem isVeryAmple_congr {X S : Scheme.{u}} (f : X ⟶ S)
    {L M : LineBundle X} (hLM : L.Isomorphic M) :
    IsVeryAmple f L ↔ IsVeryAmple f M := by
  constructor
  · rintro ⟨w⟩
    rcases hLM with ⟨e⟩
    refine ⟨{ projectiveBundle := w.projectiveBundle
              map := w.map
              immersion := w.immersion
              over := w.over
              pullback_iso := e.symm ≪≫ w.pullback_iso }⟩
  · rintro ⟨w⟩
    rcases hLM with ⟨e⟩
    refine ⟨{ projectiveBundle := w.projectiveBundle
              map := w.map
              immersion := w.immersion
              over := w.over
              pullback_iso := e ≪≫ w.pullback_iso }⟩

theorem isAmple_congr {X S : Scheme.{u}} (f : X ⟶ S)
    {L M : LineBundle X} (hLM : L.Isomorphic M) :
    IsAmple f L ↔ IsAmple f M := by
  exact Chapter04.chapter04_ample_iff_of_lineBundleIsomorphic f hLM

noncomputable def baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : Scheme.{u} :=
  pullback f g

def baseChangeToSource {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    baseChange f g ⟶ X :=
  pullback.fst f g

def baseChangeToBase {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    baseChange f g ⟶ T :=
  pullback.snd f g

noncomputable def baseChangeLineBundle {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : LineBundle X) : LineBundle (baseChange f g) :=
  L.pullback (baseChangeToSource f g)

def IsBaseChangeOf {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (L : LineBundle X)
    (M : LineBundle (baseChange f g)) : Prop :=
  M.Isomorphic (baseChangeLineBundle f g L)

theorem baseChangeLineBundle_isBaseChangeOf {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : LineBundle X) : IsBaseChangeOf f g L (baseChangeLineBundle f g L) :=
  lineBundle_isomorphic_refl _

structure FiniteAffineOpenCover (X : Scheme.{u}) where
  index : Type u
  finite_index : Finite index
  opens : index → X.Opens
  affine : ∀ i, IsAffineOpen (opens i)
  cover : iSup opens = ⊤

structure FiniteSectionFamily {X : Scheme.{u}} (M : X.Modules) where
  index : Type u
  finite_index : Finite index
  sections : index → M.val.sections
  generates : Epi (M.freeHomEquiv.symm sections)

def IsFiberwiseVeryAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  ∀ s, IsVeryAmple (f.fiberToSpecResidueField s) (L.pullback (f.fiberι s))

def IsFiberwiseAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  ∀ s, IsAmple (f.fiberToSpecResidueField s) (L.pullback (f.fiberι s))

def IsVeryAmpleAfterPositivePower {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (P : LineBundlePowers L) : Prop :=
  ∃ n, 0 < n ∧ IsVeryAmple f (P.power n)

def PowerRootSeparationFailure {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (P : LineBundlePowers L) : Prop :=
  ∃ n, 0 < n ∧ IsVeryAmple f (P.power n) ∧ ¬ IsVeryAmple f L

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
