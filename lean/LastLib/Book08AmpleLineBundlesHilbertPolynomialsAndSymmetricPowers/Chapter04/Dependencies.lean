import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Sheaves.LocallySurjective
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section01ProjectiveBundles

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open scoped AlgebraicGeometry

universe u v

/-!
Evaluation is the counit of the pullback/pushforward adjunction, tensor products
use Mathlib's presheaf tensor product followed by sheafification, and the
field-extension and cohomology interfaces below are tied to canonical earlier
Book 8 constructions rather than to unrelated choices at each use.
-/

/-! ### Evaluation and invertible sheaves -/

/-- A morphism of module sheaves is surjective in the sheaf-theoretic sense. -/
def chapter04SheafSurjective {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) : Prop :=
  TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf

theorem chapter04SheafSurjective_iff_stalkwise
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    chapter04SheafSurjective φ ↔
      ∀ x : X, Function.Surjective
        ((TopCat.Presheaf.stalkFunctor Ab x).map φ.mapPresheaf) := by
  change TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf ↔ _
  exact TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.mapPresheaf

/-- The relative evaluation map `f* f_* M ⟶ M`. -/
noncomputable def chapter04EvaluationMap
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj M) ⟶ M :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M

@[simp] theorem chapter04EvaluationMap_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) :
    chapter04EvaluationMap f M =
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M :=
  rfl

/-! The preceding projective-bundle chapter supplies the canonical section map
through the structure-sheaf comparison and the pullback of the unit morphism.
Re-export that interface here so restriction maps cannot be chosen
independently for each length-two subscheme. -/
abbrev Chapter04PullbackSectionData
    {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) :=
  Chapter02PullbackSectionData g M

/-- The finite locally free rank-one condition for a line bundle. -/
def chapter04IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop :=
    SheafOfModules.IsLocallyFree M ∧ SheafOfModules.IsFiniteType M ∧
    ∀ x : X,
      letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
        change Module (X.presheaf.stalk x) (↑(TopCat.Presheaf.stalk M.val.presheaf x))
        exact
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) M.val x
      Module.Invertible (X.presheaf.stalk x)
        (M.presheaf.stalk x)

/-- The canonical rank-one local-generator interface from Chapter 2 supplies the
    stalkwise invertible-sheaf interface used by this chapter. -/
theorem chapter04_isInvertible_of_chapter02Invertible
    {X : Scheme.{u}} {M : X.Modules}
    (hM : Chapter02InvertibleModule M) :
    chapter04IsInvertible M := by
  sorry

/-- A line bundle, represented by an invertible module sheaf. -/
structure Chapter04LineBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  isInvertible : chapter04IsInvertible sheaf

/-- The structure sheaf with its canonical line-bundle interpretation. -/
noncomputable def chapter04TrivialLineBundle (X : Scheme.{u}) : Chapter04LineBundle X :=
  { sheaf := SheafOfModules.unit X.ringCatSheaf
    isInvertible := by
      sorry }

/-! ### Tensor products and powers -/

/-- Tensor product of two module sheaves, formed by presheaf tensor and sheafification. -/
noncomputable def chapter04Tensor
    {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj M.val N.val)

/-- The zeroth tensor power is the structure sheaf. -/
noncomputable def chapter04TensorPower
    {X : Scheme.{u}} (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => chapter04Tensor (chapter04TensorPower M n) M

/-- Tensor powers of a line bundle, with the invertibility proof left for the proof pass. -/
noncomputable def chapter04LineBundleTensorPower
    {X : Scheme.{u}} (L : Chapter04LineBundle X) (n : ℕ) : Chapter04LineBundle X :=
  { sheaf := chapter04TensorPower L.sheaf n
    isInvertible := by
      sorry }

/-- Tensor product of line bundles. -/
noncomputable def chapter04LineBundleTensor
    {X : Scheme.{u}} (L M : Chapter04LineBundle X) : Chapter04LineBundle X :=
  { sheaf := chapter04Tensor L.sheaf M.sheaf
    isInvertible := by
      sorry }

/-- Pullback of a line bundle along a scheme morphism. -/
noncomputable def chapter04PullbackLineBundle
    {X Y : Scheme.{u}} (g : Y ⟶ X) (L : Chapter04LineBundle X) :
    Chapter04LineBundle Y :=
  { sheaf := (Scheme.Modules.pullback g).obj L.sheaf
    isInvertible := by
      sorry }

/-- An invertible quotient of a module sheaf. -/
structure Chapter04InvertibleQuotientPair
    {S : Scheme.{u}} (E : S.Modules) where
  line : Chapter04LineBundle S
  quotient : E ⟶ line.sheaf
  quotient_is_epi : Epi quotient

/-- Equivalence of invertible quotient presentations. -/
def chapter04QuotientPairEquivalent
    {S : Scheme.{u}} {E : S.Modules}
    (p q : Chapter04InvertibleQuotientPair E) : Prop :=
  ∃ e : p.line.sheaf ≅ q.line.sheaf, p.quotient ≫ e.hom = q.quotient

instance {S : Scheme.{u}} {E : S.Modules} : Setoid (Chapter04InvertibleQuotientPair E) where
  r := chapter04QuotientPairEquivalent
  iseqv := by
    sorry

/-- Isomorphism classes of invertible quotients. -/
abbrev Chapter04InvertibleQuotientClass
    {S : Scheme.{u}} (E : S.Modules) :=
  Quotient (inferInstance : Setoid (Chapter04InvertibleQuotientPair E))

def chapter04QuotientClassMk
    {S : Scheme.{u}} {E : S.Modules}
    (p : Chapter04InvertibleQuotientPair E) : Chapter04InvertibleQuotientClass E :=
  Quotient.mk _ p

theorem chapter04QuotientClass_eq_iff
    {S : Scheme.{u}} {E : S.Modules}
    (p q : Chapter04InvertibleQuotientPair E) :
    chapter04QuotientClassMk p = chapter04QuotientClassMk q ↔
      chapter04QuotientPairEquivalent p q := by
  sorry

/-- Pullback of an invertible quotient presentation. -/
def chapter04PullbackInvertibleQuotientPair
    {S T : Scheme.{u}} (f : T ⟶ S) {E : S.Modules}
    (p : Chapter04InvertibleQuotientPair E) :
    Chapter04InvertibleQuotientPair ((Scheme.Modules.pullback f).obj E) where
  line := chapter04PullbackLineBundle f p.line
  quotient := (Scheme.Modules.pullback f).map p.quotient
  quotient_is_epi := by
    sorry

/-- Base change on isomorphism classes of invertible quotient presentations. -/
noncomputable def chapter04PullbackQuotientClass
    {S T : Scheme.{u}} (f : T ⟶ S) {E : S.Modules} :
    Chapter04InvertibleQuotientClass E →
      Chapter04InvertibleQuotientClass ((Scheme.Modules.pullback f).obj E) :=
  Quotient.lift
    (fun p => chapter04QuotientClassMk (chapter04PullbackInvertibleQuotientPair f p)) (by
      intro p q hp
      sorry)

/-!
The module-sheaf pullback has a canonical composition comparison.  Naming the
object-level form keeps the universal-quotient compatibility statement below
readable and exposes the direction of the comparison explicitly.
-/
noncomputable def chapter04PullbackCompositionIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    ((Scheme.Modules.pullback (f ≫ g)).obj M) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackComp f g).symm.app M

noncomputable def chapter04PullbackIdentityIso
    {X : Scheme.{u}} (M : X.Modules) :
    (Scheme.Modules.pullback (𝟙 X)).obj M ≅ M :=
  (Scheme.Modules.pullbackId X).app M

/-!
The section maps must be chosen coherently.  Choosing a
`Chapter02PullbackSectionData` independently for each morphism does not imply the
identity and composition laws below, so the selected data is obtained from one
bundled system carrying those laws.
-/
structure Chapter04PullbackSectionDataSystem where
  data : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules),
    Chapter04PullbackSectionData g M
  map_id : ∀ {X : Scheme.{u}} (M : X.Modules) (s : M.val.sections),
    SheafOfModules.sectionsMap (chapter04PullbackIdentityIso M).hom
        ((data (𝟙 X) M).map s) = s
  map_comp :
    ∀ {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ Y)
      (M : X.Modules) (s : M.val.sections),
      (data (h ≫ g) M).map s =
        SheafOfModules.sectionsMap (chapter04PullbackCompositionIso h g M).inv
          ((data h ((Scheme.Modules.pullback g).obj M)).map
            ((data g M).map s))

theorem chapter04_pullback_section_data_system_exists :
    Nonempty Chapter04PullbackSectionDataSystem := by
  sorry

noncomputable def chapter04CanonicalPullbackSectionDataSystem :
    Chapter04PullbackSectionDataSystem :=
  Classical.choice chapter04_pullback_section_data_system_exists

noncomputable def chapter04PullbackSectionData
    {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) :
  Chapter04PullbackSectionData g M :=
  chapter04CanonicalPullbackSectionDataSystem.data g M

/-- Functoriality laws for the canonical pullback of global sections. -/
structure Chapter04PullbackSectionFunctoriality
    {X : Scheme.{u}} (M : X.Modules) where
  map_id : ∀ s : M.val.sections,
    SheafOfModules.sectionsMap (chapter04PullbackIdentityIso M).hom
        ((chapter04PullbackSectionData (𝟙 X) M).map s) = s
  map_comp :
    ∀ {Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ Y) (s : M.val.sections),
      (chapter04PullbackSectionData (h ≫ g) M).map s =
        SheafOfModules.sectionsMap (chapter04PullbackCompositionIso h g M).inv
          ((chapter04PullbackSectionData h ((Scheme.Modules.pullback g).obj M)).map
            ((chapter04PullbackSectionData g M).map s))

theorem chapter04_pullback_section_functoriality_exists
    {X : Scheme.{u}} (M : X.Modules) :
    Nonempty (Chapter04PullbackSectionFunctoriality M) := by
  exact ⟨{
    map_id := chapter04CanonicalPullbackSectionDataSystem.map_id M
    map_comp := by
      intro Y Z g h s
      exact chapter04CanonicalPullbackSectionDataSystem.map_comp g h M s }⟩

theorem chapter04PullbackSectionFunctoriality
    {X : Scheme.{u}} (M : X.Modules) :
    Chapter04PullbackSectionFunctoriality M := by
  exact Classical.choice (chapter04_pullback_section_functoriality_exists M)

/-! A field homomorphism gives the canonical scheme-theoretic field extension
and its pullback.  The preceding functoriality laws apply to these maps and to
composites of them. -/
def chapter04FieldExtensionMap
    {K L : Type u} [Field K] [Field L] (φ : K →+* L) :
    AlgebraicGeometry.Spec (.of L) ⟶ AlgebraicGeometry.Spec (.of K) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)

abbrev chapter04FieldExtensionBaseChange
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) (φ : K →+* L) : Scheme.{u} :=
  Limits.pullback f (chapter04FieldExtensionMap φ)

def chapter04FieldExtensionPullbackMap
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) (φ : K →+* L) :
    chapter04FieldExtensionBaseChange f φ ⟶ X :=
  Limits.pullback.fst f (chapter04FieldExtensionMap φ)

def chapter04FieldExtensionStructureMap
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) (φ : K →+* L) :
    chapter04FieldExtensionBaseChange f φ ⟶ AlgebraicGeometry.Spec (.of L) :=
  Limits.pullback.snd f (chapter04FieldExtensionMap φ)

noncomputable def chapter04FieldExtensionPullbackSectionData
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) (φ : K →+* L) (M : X.Modules) :
    Chapter04PullbackSectionData (chapter04FieldExtensionPullbackMap f φ) M :=
  chapter04PullbackSectionData (chapter04FieldExtensionPullbackMap f φ) M

/-- Base change of a quotient class, with its target normalized along composition. -/
noncomputable def chapter04PullbackQuotientClassAlong
    {S T U : Scheme.{u}} (f : T ⟶ S) (h : U ⟶ T) {E : S.Modules} :
    Chapter04InvertibleQuotientClass ((Scheme.Modules.pullback f).obj E) →
      Chapter04InvertibleQuotientClass
        ((Scheme.Modules.pullback (h ≫ f)).obj E) :=
  Quotient.lift
    (fun p => chapter04QuotientClassMk
      { line := chapter04PullbackLineBundle h p.line
        quotient :=
          (chapter04PullbackCompositionIso h f E).hom ≫
            (Scheme.Modules.pullback h).map p.quotient
        quotient_is_epi := by sorry }) (by
      intro p q hp
      sorry)

/-- A scheme morphism is constant when it factors through one residue-field point. -/
def chapter04UnderlyingConstant
    {X Y : Scheme.{u}} (g : Y ⟶ X) : Prop :=
  ∃ x : X, ∃ c : Y ⟶ AlgebraicGeometry.Spec (X.residueField x),
    c ≫ X.fromSpecResidueField x = g

/-- The twist `F ⊗ L^n` used by both global generation and Serre's criterion. -/
def chapter04TwistedModule
    {X : Scheme.{u}} (F : X.Modules) (L : Chapter04LineBundle X) (n : ℕ) : X.Modules :=
  chapter04Tensor F (chapter04TensorPower L.sheaf n)

/-- Relative global generation of a coherent sheaf after a tensor-power twist. -/
def chapter04TwistGeneratedByRelativeGlobalSections
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (L : Chapter04LineBundle X) (n : ℕ) : Prop :=
  chapter04SheafSurjective (chapter04EvaluationMap f (chapter04TwistedModule F L n))

/-! ### Relative very ampleness and projective bundles -/

/-- Finite locally free module sheaves, using Mathlib's local-generator predicates. -/
def chapter04FiniteLocallyFree {S : Scheme.{u}} (E : S.Modules) : Prop :=
  SheafOfModules.IsLocallyFree E ∧ SheafOfModules.IsFiniteType E

/-- The relative projective bundle and its tautological invertible sheaf. -/
structure Chapter04ProjectiveBundle (S : Scheme.{u}) where
  E : S.Modules
  finiteLocallyFree : chapter04FiniteLocallyFree E
  space : Scheme.{u}
  projection : space ⟶ S
  tautological : space.Modules
  tautological_isInvertible : chapter04IsInvertible tautological
  universalQuotient :
    (Scheme.Modules.pullback projection).obj E ⟶ tautological
  universalQuotient_is_epi : Epi universalQuotient
  universal_equiv :
    ∀ {T : Scheme.{u}} (f : T ⟶ S),
      {u : T ⟶ space // u ≫ projection = f} ≃
        Chapter04InvertibleQuotientClass ((Scheme.Modules.pullback f).obj E)
  /-- The equivalences are compatible with pullback of test schemes. -/
  universal_natural :
    ∀ {T U : Scheme.{u}} (f : T ⟶ S) (h : U ⟶ T)
      (u : {u : T ⟶ space // u ≫ projection = f}),
      universal_equiv (h ≫ f)
          ⟨h ≫ u.1, by simp [CategoryTheory.Category.assoc, u.2]⟩ =
        chapter04PullbackQuotientClassAlong f h (universal_equiv f u)
  projection_isProper : IsProper projection

instance chapter04ProjectiveBundle_isProper
    {S : Scheme.{u}} (P : Chapter04ProjectiveBundle S) : IsProper P.projection :=
  P.projection_isProper

noncomputable def chapter04ProjectiveBundleTautological
    {S : Scheme.{u}} (P : Chapter04ProjectiveBundle S) :
    Chapter04LineBundle P.space :=
  { sheaf := P.tautological
    isInvertible := P.tautological_isInvertible }

/-! Canonical relative-Proj bundles carry the following compatibility between
their universal quotient and quotient-valued universal property. -/
def chapter04ProjectiveBundleUniversalQuotientCompatible
    {S : Scheme.{u}} (P : Chapter04ProjectiveBundle S) : Prop :=
  ∀ {T : Scheme.{u}} (u : T ⟶ P.space),
    ∃ p : Chapter04InvertibleQuotientPair
        ((Scheme.Modules.pullback (u ≫ P.projection)).obj P.E),
      P.universal_equiv (u ≫ P.projection) ⟨u, rfl⟩ =
          chapter04QuotientClassMk p ∧
        ∃ e : p.line.sheaf ≅ (Scheme.Modules.pullback u).obj P.tautological,
          p.quotient ≫ e.hom =
          (chapter04PullbackCompositionIso u P.projection P.E).hom ≫
              (Scheme.Modules.pullback u).map P.universalQuotient

/-! Existence for finite locally free modules is retained in the source-facing
bundle interface; the companion theorem below also supplies the canonical
universal-quotient compatibility. -/

theorem chapter04_relative_projective_bundle_exists
    {S : Scheme.{u}} (E : S.Modules) (hE : chapter04FiniteLocallyFree E) :
    ∃ P : Chapter04ProjectiveBundle S, P.E = E := by
  sorry

/-- The relative-Proj existence interface supplies the displayed universal
quotient compatibility, not merely an unrelated universal equivalence. -/
structure Chapter04CanonicalProjectiveBundle
    (S : Scheme.{u}) (E : S.Modules) where
  bundle : Chapter04ProjectiveBundle S
  bundle_eq : bundle.E = E
  universalQuotientCompatible :
    chapter04ProjectiveBundleUniversalQuotientCompatible bundle

theorem chapter04_relative_projective_bundle_exists_with_universal_quotient_compatible
    {S : Scheme.{u}} (E : S.Modules) (hE : chapter04FiniteLocallyFree E) :
    Nonempty (Chapter04CanonicalProjectiveBundle S E) := by
  sorry

noncomputable def chapter04CanonicalProjectiveBundle
    {S : Scheme.{u}} (E : S.Modules) (hE : chapter04FiniteLocallyFree E) :
    Chapter04CanonicalProjectiveBundle S E :=
  Classical.choice
    (chapter04_relative_projective_bundle_exists_with_universal_quotient_compatible E hE)

abbrev Chapter04ProjectiveBundlePoint
    {S T : Scheme.{u}} (P : Chapter04ProjectiveBundle S) (f : T ⟶ S) :=
  {u : T ⟶ P.space // u ≫ P.projection = f}

theorem chapter04_projective_bundle_universal_equiv_injective
    {S T : Scheme.{u}} (P : Chapter04ProjectiveBundle S) (f : T ⟶ S)
    {u v : Chapter04ProjectiveBundlePoint P f}
    (h : P.universal_equiv f u = P.universal_equiv f v) : u = v := by
  exact (P.universal_equiv f).injective h

/-!
The following bridge is the compatibility condition supplied by the canonical
relative-Proj construction.  It is kept as an explicit hypothesis so that the
interim projective-bundle record cannot silently identify an arbitrary
equivalence with the displayed universal quotient.
-/
theorem chapter04_projective_bundle_universal_point_is_pullback_universal_quotient
    {S T : Scheme.{u}} (P : Chapter04ProjectiveBundle S) (u : T ⟶ P.space)
    (hcompat : chapter04ProjectiveBundleUniversalQuotientCompatible P) :
    ∃ p : Chapter04InvertibleQuotientPair
        ((Scheme.Modules.pullback (u ≫ P.projection)).obj P.E),
      P.universal_equiv (u ≫ P.projection) ⟨u, rfl⟩ =
          chapter04QuotientClassMk p ∧
      ∃ e : p.line.sheaf ≅ (Scheme.Modules.pullback u).obj P.tautological,
        p.quotient ≫ e.hom =
          (chapter04PullbackCompositionIso u P.projection P.E).hom ≫
            (Scheme.Modules.pullback u).map P.universalQuotient := by
  exact hcompat u

/-- A relative projective-space witness for very ampleness. -/
structure Chapter04VeryAmpleWitness
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) where
  projectiveBundle : Chapter04ProjectiveBundle S
  universalQuotientCompatible :
    chapter04ProjectiveBundleUniversalQuotientCompatible projectiveBundle
  map : X ⟶ projectiveBundle.space
  immersion : IsImmersion map
  over : map ≫ projectiveBundle.projection = f
  pullback_iso : L.sheaf ≅
    (Scheme.Modules.pullback map).obj projectiveBundle.tautological

/-- Relative very ampleness. -/
def chapter04VeryAmple
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) : Prop :=
  Nonempty (Chapter04VeryAmpleWitness f L)

/-- A projective morphism witness, with a closed immersion into a relative projective bundle. -/
structure Chapter04ProjectiveWitness
    {X S : Scheme.{u}} (f : X ⟶ S) where
  projectiveBundle : Chapter04ProjectiveBundle S
  universalQuotientCompatible :
    chapter04ProjectiveBundleUniversalQuotientCompatible projectiveBundle
  map : X ⟶ projectiveBundle.space
  closedImmersion : IsClosedImmersion map
  over : map ≫ projectiveBundle.projection = f

def chapter04Projective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Nonempty (Chapter04ProjectiveWitness f)

/-! ### Relative generation and affine charts -/

/-- Finite relative generators over a chosen open of the base. -/
def chapter04FiniteRelativeGenerationOn
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) (U : S.Opens) : Prop :=
  ∃ σ : (((Scheme.Modules.pushforward f).obj L.sheaf).over U).GeneratingSections,
    Finite σ.I

/-- Relative generation by finitely many sections, locally on the base. -/
def chapter04LocallyFiniteRelativeGeneration
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U ∧
    chapter04FiniteRelativeGenerationOn f L U

/-- The locus on which a local section generates the stalk of a module sheaf. -/
def chapter04SectionGeneratesAt
    {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (s : Γ(M, U))
    (x : X) (hx : x ∈ U) : Prop :=
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
    change Module (X.presheaf.stalk x) (↑(TopCat.Presheaf.stalk M.val.presheaf x))
    exact
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) M.val x
  Submodule.span (X.presheaf.stalk x)
      ({TopCat.Presheaf.germ M.presheaf U x hx s} :
        Set (M.presheaf.stalk x)) = ⊤

/-- A section of a positive tensor power together with its nonvanishing affine chart. -/
structure Chapter04AffineNonvanishingSection
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) (U : S.Opens) where
  n : ℕ
  positive : 0 < n
  power : Chapter04LineBundle X
  power_iso : power.sheaf ≅ (chapter04LineBundleTensorPower L n).sheaf
  sectionData : Γ(power.sheaf, f ⁻¹ᵁ U)
  locus : X.Opens
  locus_spec : ∀ x : X,
    x ∈ locus ↔
      ∃ hx : x ∈ f ⁻¹ᵁ U, chapter04SectionGeneratesAt power.sheaf sectionData x hx
  affine : IsAffineOpen locus

/-- The affine-open cover formulation of relative ampleness. -/
structure Chapter04AmpleWitness
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) where
  I : Type u
  base_open : I → S.Opens
  base_open_affine : ∀ i, IsAffineOpen (base_open i)
  base_open_cover : ∀ s : S, ∃ i, s ∈ base_open i
  J : I → Type u
  chart : ∀ i, J i → Chapter04AffineNonvanishingSection f L (base_open i)
  chart_cover : ∀ i (x : X), x ∈ f ⁻¹ᵁ (base_open i) → ∃ j, x ∈ (chart i j).locus

/-- Relative ampleness in the affine-open definition used in Chapter 4. -/
def chapter04Ample
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) : Prop :=
  Nonempty (Chapter04AmpleWitness f L)

/-! ### Canonical projective line interfaces -/

abbrev chapter04ProjectiveLine (K : Type u) [Field K] : Scheme.{u} :=
  chapter02ProjectiveSpace (AlgebraicGeometry.Spec (.of K)) 1

abbrev chapter04ProjectiveLineStructureMap (K : Type u) [Field K] :
    chapter04ProjectiveLine K ⟶ AlgebraicGeometry.Spec (.of K) :=
  chapter02ProjectiveSpaceProjection (AlgebraicGeometry.Spec (.of K)) 1

abbrev chapter04ProjectivePoint (K : Type u) [Field K] : Scheme.{u} :=
  chapter02ProjectiveSpace (AlgebraicGeometry.Spec (.of K)) 0

abbrev chapter04ProjectivePointStructureMap (K : Type u) [Field K] :
    chapter04ProjectivePoint K ⟶ AlgebraicGeometry.Spec (.of K) :=
  chapter02ProjectiveSpaceProjection (AlgebraicGeometry.Spec (.of K)) 0

noncomputable def chapter04ProjectiveLineTrivialLineBundle
    (K : Type u) [Field K] : Chapter04LineBundle (chapter04ProjectiveLine K) :=
  chapter04TrivialLineBundle (chapter04ProjectiveLine K)

noncomputable def chapter04ProjectiveLineTautologicalLineBundle
    (K : Type u) [Field K] : Chapter04LineBundle (chapter04ProjectiveLine K) :=
  { sheaf :=
      (chapter02ProjectiveSpaceTwistingLine (AlgebraicGeometry.Spec (.of K)) 1).carrier
    isInvertible :=
      chapter04_isInvertible_of_chapter02Invertible
        (chapter02ProjectiveSpaceTwistingLine (AlgebraicGeometry.Spec (.of K)) 1).invertible }

noncomputable def chapter04ProjectiveLineTautologicalBasis
    (K : Type u) [Field K] :
    Fin 2 → (chapter04ProjectiveLineTautologicalLineBundle K).sheaf.sections :=
  chapter02ProjectiveSpaceCoordinates (AlgebraicGeometry.Spec (.of K)) 1

structure Chapter04ProjectiveLineExample (K : Type u) [Field K] where
  constant_map : chapter04ProjectiveLine K ⟶ chapter04ProjectivePoint K
  constant_map_over :
    constant_map ≫ chapter04ProjectivePointStructureMap K =
      chapter04ProjectiveLineStructureMap K
  constant_map_is_constant : chapter04UnderlyingConstant constant_map

/-! ### Length-two subschemes and the field criterion -/

/-- The module-theoretic length of a scheme finite over a coefficient field. -/
noncomputable def chapter04SchemeLength
    (K : Type u) [Field K] (Z : Scheme.{u})
    (g : Z ⟶ AlgebraicGeometry.Spec (.of K)) : ℕ∞ :=
  letI := g.appTop.hom.toAlgebra
  letI : Module K Γ(Z, ⊤) :=
    Module.compHom _ (((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom)
  Module.length K Γ(Z, ⊤)

/-- The additive-group structure on global sections of a module sheaf. -/
noncomputable instance chapter04SectionsAddCommGroup
    {Z : Scheme.{u}} (M : Z.Modules) : AddCommGroup M.val.sections := by
  sorry

/-- The module structure of global sections over the ring of global functions. -/
@[instance_reducible]
noncomputable def chapter04SectionsModuleOverGlobalSections
    {Z : Scheme.{u}} (M : Z.Modules)
    [addCommGroup : AddCommGroup M.val.sections] :
    Module (Γ(Z, ⊤)) M.val.sections := by
  sorry

/-- Sections of a module sheaf on a scheme over a field carry the scalar action
    induced by the structure morphism. -/
@[instance_reducible]
noncomputable def chapter04SectionsModuleOverField
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ AlgebraicGeometry.Spec (.of K)) (M : Z.Modules)
    [addCommGroup : AddCommGroup M.val.sections] :
    Module K M.val.sections := by
  letI : Module (Γ(Z, ⊤)) M.val.sections :=
    chapter04SectionsModuleOverGlobalSections M
  letI := g.appTop.hom.toAlgebra
  exact Module.compHom M.val.sections
    (((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom)

/-- A closed subscheme of length two in a scheme over a field. -/
structure Chapter04LengthTwoClosedSubscheme
    (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) where
  Z : Scheme.{u}
  inclusion : Z ⟶ X
  closed : IsClosedImmersion inclusion
  structureMap : Z ⟶ AlgebraicGeometry.Spec (.of K)
  over : inclusion ≫ f = structureMap
  finite : IsFinite structureMap
  length_two : chapter04SchemeLength K Z structureMap = 2

/-- A finite-dimensional family of global sections and its restrictions to length-two subschemes. -/
structure Chapter04FiniteSectionSystem
    (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) (L : Chapter04LineBundle X) where
  I : Type u
  [addCommGroupI : AddCommGroup I]
  [moduleI : Module K I]
  [addCommGroupSections : AddCommGroup L.sheaf.val.sections]
  [moduleSections : Module K L.sheaf.val.sections]
  addCommGroupSections_canonical :
    addCommGroupSections = chapter04SectionsAddCommGroup L.sheaf
  moduleSections_canonical :
    moduleSections = chapter04SectionsModuleOverField f L.sheaf
  finite : Module.Finite K I
  sectionMap : I →ₗ[K] L.sheaf.val.sections
  section_injective : Function.Injective sectionMap
  generates : Epi (L.sheaf.freeHomEquiv.symm (fun i => sectionMap i))
  restriction : ∀ Z : Chapter04LengthTwoClosedSubscheme K f,
    I → ((Scheme.Modules.pullback Z.inclusion).obj L.sheaf).val.sections
  restriction_eq : ∀ (Z : Chapter04LengthTwoClosedSubscheme K f) (i : I),
    restriction Z i =
      (chapter04PullbackSectionData Z.inclusion L.sheaf).map (sectionMap i)

/-- The restriction-surjectivity form of separation over the original field. -/
def chapter04SeparatesLengthTwoOverBase
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L) : Prop :=
  ∀ Z : Chapter04LengthTwoClosedSubscheme K f,
    Function.Surjective (V.restriction Z)

/-- The restriction map of a section system after a field extension. -/
noncomputable def chapter04FieldExtensionRestriction
    {K K' : Type u} [Field K] [Field K'] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) (L : Chapter04LineBundle X)
    (V : Chapter04FiniteSectionSystem K f L) (φ : K →+* K')
    (Z : Chapter04LengthTwoClosedSubscheme K'
      (chapter04FieldExtensionStructureMap f φ)) (i : V.I) :
    (((Scheme.Modules.pullback Z.inclusion).obj
      ((Scheme.Modules.pullback (chapter04FieldExtensionPullbackMap f φ)).obj L.sheaf)).val).sections :=
  (chapter04PullbackSectionData Z.inclusion
      ((Scheme.Modules.pullback (chapter04FieldExtensionPullbackMap f φ)).obj L.sheaf)).map
    ((chapter04FieldExtensionPullbackSectionData f φ L.sheaf).map (V.sectionMap i))

/-- Separation of points and tangent directions after every field extension.

    The span formulation is the scalar-extension form of surjectivity of
    `V ⊗ K' → H⁰(Z, L|_Z)`. -/
def chapter04SeparatesLengthTwo
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L) : Prop :=
  chapter04SeparatesLengthTwoOverBase V ∧
    ∀ (K' : Type u) [Field K'] (φ : K →+* K')
      (Z : Chapter04LengthTwoClosedSubscheme K'
        (chapter04FieldExtensionStructureMap f φ)),
      let M :=
        ((Scheme.Modules.pullback Z.inclusion).obj
          ((Scheme.Modules.pullback (chapter04FieldExtensionPullbackMap f φ)).obj L.sheaf))
      letI : AddCommGroup M.val.sections := chapter04SectionsAddCommGroup M
      letI : Module K' M.val.sections :=
        chapter04SectionsModuleOverField Z.structureMap M
      Submodule.span K' (Set.range (chapter04FieldExtensionRestriction f L V φ Z)) = ⊤

/-! ### Serre interfaces -/

/-- Finite-type quasi-coherent module sheaves. -/
def chapter04FiniteTypeQuasiCoherent {X : Scheme.{u}} (F : X.Modules) : Prop :=
  F.IsQuasicoherent ∧ F.IsFiniteType

/-- A coherent ideal sheaf as a finite-type quasi-coherent submodule of `𝒪_X`. -/
structure Chapter04CoherentIdealSheaf (X : Scheme.{u}) where
  carrier : X.Modules
  inclusion : carrier ⟶ SheafOfModules.unit X.ringCatSheaf
  inclusion_mono : Mono inclusion
  quasiCoherent : carrier.IsQuasicoherent
  finiteType : carrier.IsFiniteType

/-! ### Canonical coherent cohomology -/

noncomputable def chapter04Cohomology
    {X : Scheme.{u}} (F : X.Modules) (i : ℕ) : AddCommGrpCat.{u + 1} := by
  letI : CategoryTheory.HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    CategoryTheory.HasExt.standard _
  exact CategoryTheory.Sheaf.H'
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) i (⊤ : X.Opens)

/-! The context fixes the canonical cohomology object and records its
functoriality in coefficient sheaves. -/
structure Chapter04CohomologyContext (X : Scheme.{u}) where
  map : ∀ {F G : X.Modules} (_φ : F ⟶ G) (i : ℕ),
    chapter04Cohomology F i ⟶ chapter04Cohomology G i
  map_id : ∀ (F : X.Modules) (i : ℕ), map (𝟙 F) i = 𝟙 _
  map_comp : ∀ {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (i : ℕ),
    map (φ ≫ ψ) i = map φ i ≫ map ψ i

abbrev Chapter04CohomologyContext.H
    {X : Scheme.{u}} (_C : Chapter04CohomologyContext X)
    (F : X.Modules) (i : ℕ) : AddCommGrpCat.{u + 1} :=
  chapter04Cohomology F i

noncomputable def chapter04CanonicalCohomologyContext (X : Scheme.{u}) :
    Chapter04CohomologyContext X :=
  { map := by
      sorry
    map_id := by
      sorry
    map_comp := by
      sorry }

def chapter04CohomologyVanishes
    {X : Scheme.{u}} (F : X.Modules) (i : ℕ) : Prop :=
  ∀ x : chapter04Cohomology F i, x = 0

def Chapter04CohomologyContext.Vanishes
    {X : Scheme.{u}} (C : Chapter04CohomologyContext X)
    (F : X.Modules) (i : ℕ) : Prop :=
  ∀ x : C.H F i, x = 0

theorem chapter04CohomologyContext_vanishes_iff_isZero
    {X : Scheme.{u}} (C : Chapter04CohomologyContext X)
    (F : X.Modules) (i : ℕ) :
    C.Vanishes F i ↔ IsZero (C.H F i) := by
  sorry

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
