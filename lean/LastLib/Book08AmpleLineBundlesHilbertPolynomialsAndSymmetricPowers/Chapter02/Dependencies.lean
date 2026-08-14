import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.Section01ProjectiveGeometryOverABase
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory

/-!
## Shared interfaces for Chapter 2

The pinned Mathlib checkout contains affine `Proj`, sheaves of modules, pullback, and the
canonical notions of quasi-coherence, local freeness, finite presentation, and closed immersion.
It does not yet expose the relative Proj of a quasi-coherent module, its universal quotient, or a
tensor product of sheaves of modules.  The interfaces below keep those book-facing constructions
bundled and make the missing dependencies explicit.  They are propositions or data interfaces,
never axioms asserting a desired theorem.
-/

/-- A quasi-coherent `𝒪_S`-module, bundled for the relative Proj interfaces. -/
structure Chapter02QuasiCoherentModule (S : Scheme.{u}) where
  carrier : S.Modules
  is_quasi_coherent : carrier.IsQuasicoherent

def chapter02AsChapter01QuasiCoherentModule {S : Scheme.{u}}
    (E : Chapter02QuasiCoherentModule S) :
    Chapter01.Chapter01QuasiCoherentModule S where
  carrier := E.carrier
  isQuasicoherent := E.is_quasi_coherent

abbrev Chapter02RelativeGradedAlgebra (S : Scheme.{u}) :=
  Chapter01.Chapter01RelativeGradedAlgebra S

abbrev Chapter02RelativeProj {S : Scheme.{u}}
    (𝒜 : Chapter02RelativeGradedAlgebra S) :=
  Chapter01.Chapter01RelativeProj 𝒜

noncomputable def chapter02RelativeProj {S : Scheme.{u}}
    (𝒜 : Chapter02RelativeGradedAlgebra S) : Chapter02RelativeProj 𝒜 :=
  Chapter01.chapter01RelativeProj 𝒜

abbrev chapter02RelativeProjBaseChange {S T : Scheme.{u}}
    (𝒜 : Chapter02RelativeGradedAlgebra S) (g : T ⟶ S) : Scheme.{u} :=
  Chapter01.chapter01RelativeProjBaseChange 𝒜 g

abbrev chapter02RelativePullback {S T : Scheme.{u}}
    (𝒜 : Chapter02RelativeGradedAlgebra S) (g : T ⟶ S) :
    Chapter02RelativeGradedAlgebra T :=
  Chapter01.chapter01RelativePullback 𝒜 g

abbrev chapter02RelativeFiberAlgebra {S : Scheme.{u}}
    (𝒜 : Chapter02RelativeGradedAlgebra S) (s : S) :
    Chapter02RelativeGradedAlgebra (AlgebraicGeometry.Spec
      (CommRingCat.of (S.residueField s))) :=
  Chapter01.chapter01RelativeFiberAlgebra 𝒜 s

theorem chapter02_relative_proj_base_change
    {S T : Scheme.{u}} (𝒜 : Chapter02RelativeGradedAlgebra S) (g : T ⟶ S) :
    ∃ (e : chapter02RelativeProjBaseChange 𝒜 g ⟶
      (chapter02RelativeProj (chapter02RelativePullback 𝒜 g)).scheme),
      IsIso e ∧
        e ≫ (chapter02RelativeProj (chapter02RelativePullback 𝒜 g)).projection =
          Limits.pullback.snd (chapter02RelativeProj 𝒜).projection g := by
  exact Chapter01.chapter01_relative_proj_base_change 𝒜 g

theorem chapter02_relative_proj_fiber
    {S : Scheme.{u}} (𝒜 : Chapter02RelativeGradedAlgebra S) (s : S) :
    ∃ (e : (chapter02RelativeProj 𝒜).projection.fiber s ⟶
      (chapter02RelativeProj (chapter02RelativeFiberAlgebra 𝒜 s)).scheme),
      IsIso e ∧
        e ≫ (chapter02RelativeProj (chapter02RelativeFiberAlgebra 𝒜 s)).projection =
        (chapter02RelativeProj 𝒜).projection.fiberToSpecResidueField s := by
  exact Chapter01.chapter01_relative_proj_fiber 𝒜 s

/-- Pullback of the underlying sheaf of modules. -/
abbrev chapter02PullbackModule {S T : Scheme.{u}} (f : T ⟶ S)
    (E : Chapter02QuasiCoherentModule S) : T.Modules :=
  (Scheme.Modules.pullback f).obj E.carrier

theorem chapter02_pullback_preserves_quasi_coherent
    {S T : Scheme.{u}} (f : T ⟶ S) (E : Chapter02QuasiCoherentModule S) :
    (chapter02PullbackModule f E).IsQuasicoherent := by
  sorry

/-- The book-facing quasi-coherent pullback; the preservation proof is supplied by the later API. -/
def chapter02PullbackQuasiCoherentModule {S T : Scheme.{u}} (f : T ⟶ S)
    (E : Chapter02QuasiCoherentModule S) : Chapter02QuasiCoherentModule T where
  carrier := chapter02PullbackModule f E
  is_quasi_coherent := chapter02_pullback_preserves_quasi_coherent f E

/-!
`LocalGeneratorsData` is the canonical Mathlib interface for local presentations.  Requiring
each free generator to have an index set equivalent to `Fin n` records the constant finite rank
condition without choosing a trivialization globally.
-/
abbrev Chapter02LocallyFreeRank {S : Scheme.{u}} (E : S.Modules) (n : ℕ) : Prop :=
  Chapter01.Chapter01LocallyFreeRank E n

def Chapter02InvertibleModule {S : Scheme.{u}} (L : S.Modules) : Prop :=
  Chapter02LocallyFreeRank L 1

/-- A line bundle is an invertible sheaf of modules. -/
structure Chapter02LineBundle (S : Scheme.{u}) where
  carrier : S.Modules
  invertible : Chapter02InvertibleModule carrier

private theorem chapter02_invertible_module_iff_chapter01_line_bundle
    {S : Scheme.{u}} {L : S.Modules} :
    Chapter02InvertibleModule L ↔ Chapter01.Chapter01IsLineBundle L := by
  unfold Chapter02InvertibleModule Chapter02LocallyFreeRank
    Chapter01.Chapter01IsLineBundle Chapter01.Chapter01LocallyFreeRank
  constructor
  · rintro ⟨q, hq, hrank⟩
    refine ⟨q, hq, ?_⟩
    intro i
    obtain ⟨e⟩ := hrank i
    refine ⟨e.symm 0, ?_⟩
    intro j
    apply e.injective
    exact Subsingleton.elim _ _
  · rintro ⟨q, hq, hsingle⟩
    refine ⟨q, hq, ?_⟩
    intro i
    obtain ⟨e, he⟩ := hsingle i
    refine ⟨{
      toFun := fun _ => 0
      invFun := fun _ => e
      left_inv := fun j => (he j).symm
      right_inv := fun j => Subsingleton.elim _ _ }⟩

theorem chapter02_pullback_preserves_invertible_module
    {S T : Scheme.{u}} (f : T ⟶ S) {L : S.Modules}
    (hL : Chapter02InvertibleModule L) :
    Chapter02InvertibleModule ((Scheme.Modules.pullback f).obj L) := by
  apply chapter02_invertible_module_iff_chapter01_line_bundle.mpr
  exact (Chapter01.chapter01PullbackLineBundle f
    ⟨L, chapter02_invertible_module_iff_chapter01_line_bundle.mp hL⟩).isLineBundle

/-- An invertible quotient of a quasi-coherent module. -/
structure Chapter02InvertibleQuotientPair {S : Scheme.{u}} (E : S.Modules) where
  line : Chapter02LineBundle S
  quotient : E ⟶ line.carrier
  quotient_is_epi : Epi quotient

/-- Isomorphism of quotient pairs, with the quotient square as its compatibility equation. -/
def chapter02QuotientPairEquivalent
    {S : Scheme.{u}} {E : S.Modules}
    (p q : Chapter02InvertibleQuotientPair E) : Prop :=
  ∃ e : p.line.carrier ≅ q.line.carrier, p.quotient ≫ e.hom = q.quotient

instance {S : Scheme.{u}} {E : S.Modules} : Setoid (Chapter02InvertibleQuotientPair E) where
  r := chapter02QuotientPairEquivalent
  iseqv := by
    constructor
    · intro p
      refine ⟨Iso.refl _, ?_⟩
      simp
    · intro p q h
      obtain ⟨e, he⟩ := h
      refine ⟨e.symm, ?_⟩
      calc
        q.quotient ≫ e.symm.hom = (p.quotient ≫ e.hom) ≫ e.symm.hom := by rw [he]
        _ = p.quotient := by simp [Category.assoc]
    · intro p q r h₁ h₂
      obtain ⟨e, he⟩ := h₁
      obtain ⟨f, hf⟩ := h₂
      refine ⟨e ≪≫ f, ?_⟩
      calc
        p.quotient ≫ (e ≪≫ f).hom = (p.quotient ≫ e.hom) ≫ f.hom := by
          simp [Category.assoc]
        _ = q.quotient ≫ f.hom := by rw [he]
        _ = r.quotient := hf

abbrev Chapter02InvertibleQuotientClass {S : Scheme.{u}} (E : S.Modules) :=
  Quotient (inferInstance : Setoid (Chapter02InvertibleQuotientPair E))

def chapter02QuotientClassMk {S : Scheme.{u}} {E : S.Modules}
    (p : Chapter02InvertibleQuotientPair E) : Chapter02InvertibleQuotientClass E :=
  Quotient.mk _ p

theorem chapter02QuotientClass_eq_iff {S : Scheme.{u}} {E : S.Modules}
    (p q : Chapter02InvertibleQuotientPair E) :
    chapter02QuotientClassMk p = chapter02QuotientClassMk q ↔
      chapter02QuotientPairEquivalent p q := by
  exact Quotient.eq

/-- Pullback preserves the line-bundle condition. -/
def chapter02PullbackLineBundle {S T : Scheme.{u}} (f : T ⟶ S)
    (L : Chapter02LineBundle S) : Chapter02LineBundle T where
  carrier := (Scheme.Modules.pullback f).obj L.carrier
  invertible := chapter02_pullback_preserves_invertible_module f L.invertible

def chapter02PullbackInvertibleQuotientPair
    {S T : Scheme.{u}} (f : T ⟶ S) {E : S.Modules}
    (p : Chapter02InvertibleQuotientPair E) :
    Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback f).obj E) where
  line := chapter02PullbackLineBundle f p.line
  quotient := (Scheme.Modules.pullback f).map p.quotient
  quotient_is_epi := by
    exact @Functor.map_epi _ _ _ _ (Scheme.Modules.pullback f)
      (Functor.preservesEpimorphisms_of_adjunction
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      _ _ p.quotient p.quotient_is_epi

/-!
The relative projective bundle package records exactly the scheme, structure morphism, twisting
line bundle, and universal quotient used in the book.  The existence theorem is the one natural
dependency not supplied by pinned Mathlib: affine `Proj` is available, but relative `Proj_S(Sym E)`
and its universal quotient are not.
-/

noncomputable def chapter02PullbackCompositionIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    ((Scheme.Modules.pullback (f ≫ g)).obj M) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackComp f g).symm.app M

/-!
Pulling an invertible quotient through a composite uses the canonical comparison between composite
pullback and iterated pullback.  This is placed before the representability package so its
naturality field can state the required base-change compatibility without referring forward to a
later section.
-/
def chapter02PullbackInvertibleQuotientPairAlongComposition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {E : Z.Modules}
    (p : Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback g).obj E)) :
    Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback (f ≫ g)).obj E) where
  line := chapter02PullbackLineBundle f p.line
  quotient :=
    (chapter02PullbackCompositionIso f g E).hom ≫
      (Scheme.Modules.pullback f).map p.quotient
  quotient_is_epi := by
    exact epi_comp' (by infer_instance)
      (@Functor.map_epi _ _ _ _ (Scheme.Modules.pullback f)
        (Functor.preservesEpimorphisms_of_adjunction
          (Scheme.Modules.pullbackPushforwardAdjunction f))
        _ _ p.quotient p.quotient_is_epi)

def chapter02ProjectiveBundlePointPostcompose
    {S T U Z : Scheme.{u}} (projection : Z ⟶ S) (f : T ⟶ S) (g : U ⟶ T)
    (u : {u : T ⟶ Z // u ≫ projection = f}) :
    {u : U ⟶ Z // u ≫ projection = g ≫ f} :=
  ⟨g ≫ u.1, by
    simpa [Category.assoc] using congrArg (fun h => g ≫ h) u.2⟩

structure Chapter02ProjectiveBundleData
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) where
  scheme : Scheme.{u}
  projection : scheme ⟶ S
  twistingLineBundle : Chapter02LineBundle scheme
  universalQuotient :
    (Scheme.Modules.pullback projection).obj E.carrier ⟶ twistingLineBundle.carrier
  universalQuotient_is_epi : Epi universalQuotient
  /-- The representability statement that identifies this package with relative Proj. -/
  universalProperty : ∀ {T : Scheme.{u}} (f : T ⟶ S),
    {u : T ⟶ scheme // u ≫ projection = f} ≃
      Chapter02InvertibleQuotientClass ((Scheme.Modules.pullback f).obj E.carrier)
  /-- The representing equivalence is natural under base change of test schemes. -/
  universalProperty_natural :
    ∀ {T U : Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T)
      (u : {u : T ⟶ scheme // u ≫ projection = f}),
      ∃ p : Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback f).obj E.carrier),
        universalProperty f u = chapter02QuotientClassMk p ∧
          universalProperty (g ≫ f)
              (chapter02ProjectiveBundlePointPostcompose projection f g u) =
            chapter02QuotientClassMk
              (chapter02PullbackInvertibleQuotientPairAlongComposition g f p)
  /-- The universal equivalence is normalized by the displayed universal quotient. -/
  universalProperty_compatible :
    ∀ {T : Scheme.{u}} (f : T ⟶ S)
      (u : {u : T ⟶ scheme // u ≫ projection = f}),
      ∃ p : Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback f).obj E.carrier),
        universalProperty f u = chapter02QuotientClassMk p ∧
          ∃ e : p.line.carrier ≅ (Scheme.Modules.pullback u.1).obj twistingLineBundle.carrier,
            p.quotient ≫ e.hom =
              (Scheme.Modules.pullbackCongr u.2).inv.app E.carrier ≫
                (Scheme.Modules.pullbackComp u.1 projection).inv.app E.carrier ≫
                (Scheme.Modules.pullback u.1).map universalQuotient

abbrev Chapter02CanonicalProjectiveBundleData {S : Scheme.{u}}
    (E : Chapter02QuasiCoherentModule S) :=
  Chapter01.Chapter01ProjectiveBundleData
    S (chapter02AsChapter01QuasiCoherentModule E)

theorem chapter02_canonical_relative_projective_bundle_exists
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Nonempty (Chapter02CanonicalProjectiveBundleData E) := by
  exact ⟨Chapter01.chapter01ProjectiveBundleData S (chapter02AsChapter01QuasiCoherentModule E)⟩

noncomputable def chapter02CanonicalRelativeProjectiveBundle
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Chapter02CanonicalProjectiveBundleData E :=
  Classical.choice (chapter02_canonical_relative_projective_bundle_exists S E)

private def chapter02LineBundleToChapter01
    {S : Scheme.{u}} (L : Chapter02LineBundle S) :
    Chapter01.Chapter01LineBundle S where
  module := L.carrier
  isLineBundle :=
    chapter02_invertible_module_iff_chapter01_line_bundle.mp L.invertible

private def chapter01LineBundleToChapter02
    {S : Scheme.{u}} (L : Chapter01.Chapter01LineBundle S) :
    Chapter02LineBundle S where
  carrier := L.module
  invertible :=
    chapter02_invertible_module_iff_chapter01_line_bundle.mpr L.isLineBundle

private def chapter02InvertibleQuotientPairToChapter01
    {S T : Scheme.{u}} {E : S.Modules} (f : T ⟶ S)
    (p : Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback f).obj E)) :
    Chapter01.Chapter01InvertibleQuotient E f where
  lineBundle := chapter02LineBundleToChapter01 p.line
  quotient := p.quotient
  quotient_is_epi := p.quotient_is_epi

private def chapter01InvertibleQuotientToChapter02
    {S T : Scheme.{u}} {E : S.Modules} (f : T ⟶ S)
    (p : Chapter01.Chapter01InvertibleQuotient E f) :
    Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback f).obj E) where
  line := chapter01LineBundleToChapter02 p.lineBundle
  quotient := p.quotient
  quotient_is_epi := p.quotient_is_epi

private def chapter02QuotientClassToChapter01
    {S T : Scheme.{u}} (f : T ⟶ S) (E : S.Modules) :
    Chapter02InvertibleQuotientClass ((Scheme.Modules.pullback f).obj E) ⟶
      Chapter01.Chapter01InvertibleQuotientClass E f := by
  refine TypeCat.ofHom ?_
  refine Quotient.lift
    (fun p : Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback f).obj E) =>
      Chapter01.chapter01InvertibleQuotientClassMk
        (chapter02InvertibleQuotientPairToChapter01 f p)) ?_
  intro p q h
  apply Quotient.sound
  obtain ⟨e, he⟩ := h
  exact ⟨e, he⟩

private def chapter01QuotientClassToChapter02
    {S T : Scheme.{u}} (f : T ⟶ S) (E : S.Modules) :
    Chapter01.Chapter01InvertibleQuotientClass E f ⟶
      Chapter02InvertibleQuotientClass ((Scheme.Modules.pullback f).obj E) := by
  refine TypeCat.ofHom ?_
  refine Quotient.lift
    (fun p : Chapter01.Chapter01InvertibleQuotient E f =>
      chapter02QuotientClassMk
        (chapter01InvertibleQuotientToChapter02 f p)) ?_
  intro p q h
  apply Quotient.sound
  obtain ⟨e, he⟩ := h
  exact ⟨e, he⟩

private def chapter02QuotientClassEquivChapter01
    {S T : Scheme.{u}} (f : T ⟶ S) (E : S.Modules) :
    Chapter02InvertibleQuotientClass ((Scheme.Modules.pullback f).obj E) ≃
      Chapter01.Chapter01InvertibleQuotientClass E f where
  toFun := chapter02QuotientClassToChapter01 f E
  invFun := chapter01QuotientClassToChapter02 f E
  left_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    intro p
    simp only [chapter01QuotientClassToChapter02, chapter02QuotientClassToChapter01,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
    apply (chapter02QuotientClass_eq_iff _ _).2
    exact ⟨Iso.refl _, rfl⟩
  right_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    intro p
    simp only [chapter01QuotientClassToChapter02, chapter02QuotientClassToChapter01,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
    apply (Chapter01.chapter01InvertibleQuotientClass_eq_iff _ _).2
    exact ⟨Iso.refl _, rfl⟩

/- LOCAL_DEPENDENCY_GUESS: relative Proj of a quasi-coherent module and the universal quotient. -/
theorem chapter02_relative_projective_bundle_exists
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Nonempty (Chapter02ProjectiveBundleData S E) := by
  obtain ⟨P⟩ := Chapter01.chapter01_projective_bundle_exists S
    (chapter02AsChapter01QuasiCoherentModule E)
  dsimp [chapter02AsChapter01QuasiCoherentModule] at P
  refine ⟨{
    scheme := P.scheme
    projection := P.projection
    twistingLineBundle := chapter01LineBundleToChapter02 P.tautological
    universalQuotient := P.universalQuotient
    universalQuotient_is_epi := P.universalQuotient_is_epi
    universalProperty := ?_
    universalProperty_natural := ?_
    universalProperty_compatible := ?_ }⟩
  · intro T f
    exact (P.universalProperty f).trans
      (chapter02QuotientClassEquivChapter01 f E.carrier).symm
  · intro T U f g u
    obtain ⟨p, hp, hnat⟩ := P.universalProperty_natural f g u
    let p₂ := chapter01InvertibleQuotientToChapter02 f p
    refine ⟨p₂, ?_, ?_⟩
    · change (chapter02QuotientClassEquivChapter01 f E.carrier).symm
          (P.universalProperty f u) = chapter02QuotientClassMk p₂
      rw [hp]
      simp only [chapter02QuotientClassEquivChapter01, chapter01QuotientClassToChapter02,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      apply (chapter02QuotientClass_eq_iff _ _).2
      exact ⟨Iso.refl _, rfl⟩
    · change (chapter02QuotientClassEquivChapter01 (g ≫ f) E.carrier).symm
          (P.universalProperty (g ≫ f) _) = _
      have hnat' :
          P.universalProperty (g ≫ f)
              (chapter02ProjectiveBundlePointPostcompose P.projection f g u) =
            Chapter01.chapter01InvertibleQuotientClassMk
              (Chapter01.chapter01PullbackInvertibleQuotientAlong f g p) := by
        simpa [chapter02ProjectiveBundlePointPostcompose] using hnat
      rw [hnat']
      simp only [chapter02QuotientClassEquivChapter01, chapter01QuotientClassToChapter02,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      apply (chapter02QuotientClass_eq_iff _ _).2
      exact ⟨Iso.refl _, rfl⟩
  · intro T f u
    obtain ⟨p, hp, e, he⟩ := P.universalProperty_compatible f u
    let p₂ := chapter01InvertibleQuotientToChapter02 f p
    refine ⟨p₂, ?_, ?_⟩
    · change (chapter02QuotientClassEquivChapter01 f E.carrier).symm
          (P.universalProperty f u) = chapter02QuotientClassMk p₂
      rw [hp]
      simp only [chapter02QuotientClassEquivChapter01, chapter01QuotientClassToChapter02,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      apply (chapter02QuotientClass_eq_iff _ _).2
      exact ⟨Iso.refl _, rfl⟩
    · refine ⟨e, ?_⟩
      exact he

noncomputable def chapter02ProjectiveBundleData
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Chapter02ProjectiveBundleData S E :=
  Classical.choice (chapter02_relative_projective_bundle_exists S E)

abbrev chapter02ProjectiveBundle
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) : Scheme.{u} :=
  (chapter02ProjectiveBundleData S E).scheme

abbrev chapter02ProjectiveBundleProjection
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    chapter02ProjectiveBundle S E ⟶ S :=
  (chapter02ProjectiveBundleData S E).projection

abbrev chapter02ProjectiveBundleTwistingLine
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Chapter02LineBundle (chapter02ProjectiveBundle S E) :=
  (chapter02ProjectiveBundleData S E).twistingLineBundle

abbrev chapter02ProjectiveBundleOOne
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Chapter02LineBundle (chapter02ProjectiveBundle S E) :=
  chapter02ProjectiveBundleTwistingLine S E

abbrev chapter02ProjectiveBundleUniversalQuotient
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    (Scheme.Modules.pullback (chapter02ProjectiveBundleProjection S E)).obj E.carrier ⟶
      (chapter02ProjectiveBundleTwistingLine S E).carrier :=
  (chapter02ProjectiveBundleData S E).universalQuotient

def chapter02ProjectiveBundleMapOver
    {S T : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (f : T ⟶ S) (u : T ⟶ chapter02ProjectiveBundle S E) : Prop :=
  u ≫ chapter02ProjectiveBundleProjection S E = f

/-!
The arbitrary quasi-coherent relative Proj above is deliberately not assumed to be of finite type.
For the finite locally free case, this package keeps the canonical universal quotient together
with the morphism properties needed by later projective and quasi-projective constructions.
-/

def Chapter02FiniteLocallyFreeModule {S : Scheme.{u}}
    (E : Chapter02QuasiCoherentModule S) : Prop :=
  Chapter01.Chapter01FiniteLocallyFree E.carrier

/-! Canonical variable-rank package.  The fixed-rank `Chapter01FiniteProjectiveBundle` remains
available for the notation `P^r`, while this interface is the one used for an arbitrary finite
locally free module and carries properness and finite presentation with its relative Proj. -/
abbrev Chapter02FiniteLocallyFreeProjectiveBundle
    (S : Scheme.{u}) (E : S.Modules) :=
  Chapter01.Chapter01FiniteLocallyFreeProjectiveBundle S E

theorem chapter02_finite_locally_free_projective_bundle_exists
    {S : Scheme.{u}} (E : S.Modules)
    (hE : Chapter01.Chapter01FiniteLocallyFree E) :
    Nonempty (Chapter02FiniteLocallyFreeProjectiveBundle S E) := by
  sorry

abbrev Chapter02CanonicalFiniteProjectiveBundle
    (S : Scheme.{u}) (r : ℕ) :=
  Chapter01.Chapter01FiniteProjectiveBundle S r

theorem chapter02_canonical_finite_relative_projective_bundle_exists
    {S : Scheme.{u}} {r : ℕ} (E : S.Modules)
    (hE : Chapter01.Chapter01FiniteLocallyFree E)
    (hr : Chapter01.Chapter01LocallyFreeRank E (r + 1)) :
    ∃ P : Chapter02CanonicalFiniteProjectiveBundle S r, P.E = E := by
  exact Chapter01.chapter01_finite_projective_bundle_exists E hE hr

/-!
This is the canonical finite relative projective-bundle interface.  The `data` field is the
universal quotient package, while the last two fields expose the standard finiteness properties of
the finite locally free construction without replacing it by an unrelated ambient scheme.
-/
structure Chapter02RelativeProjectiveBundle
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) where
  finiteLocallyFree : Chapter02FiniteLocallyFreeModule E
  /-- The canonical variable-rank finite relative-Proj package on the underlying module. -/
  canonical : Chapter02FiniteLocallyFreeProjectiveBundle S E.carrier
  data : Chapter02ProjectiveBundleData S E
  /-- The chosen book-facing package is transported from the canonical finite package. -/
  comparison : data.scheme ≅ canonical.scheme
  comparison_over : comparison.hom ≫ canonical.projection = data.projection
  proper : IsProper data.projection
  finite_presentation : LocallyOfFinitePresentation data.projection

abbrev Chapter02RelativeProjectiveBundle.carrier
    {S : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02RelativeProjectiveBundle S E) : Scheme.{u} :=
  P.data.scheme

abbrev Chapter02RelativeProjectiveBundle.projection
    {S : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02RelativeProjectiveBundle S E) : P.carrier ⟶ S :=
  P.data.projection

abbrev Chapter02RelativeProjectiveBundle.twistingLineBundle
    {S : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02RelativeProjectiveBundle S E) :
    Chapter02LineBundle P.carrier :=
  P.data.twistingLineBundle

abbrev Chapter02RelativeProjectiveBundle.universalQuotient
    {S : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02RelativeProjectiveBundle S E) :
    (Scheme.Modules.pullback P.projection).obj E.carrier ⟶
      P.twistingLineBundle.carrier :=
  P.data.universalQuotient

theorem chapter02_finite_relative_projective_bundle_transfer
    {S : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (P : Chapter02RelativeProjectiveBundle S E) :
    ∃ e : P.data.scheme ≅ P.canonical.scheme,
      e.hom ≫ P.canonical.projection = P.data.projection :=
  ⟨P.comparison, P.comparison_over⟩

/- LOCAL_DEPENDENCY_GUESS: finite locally free relative Proj is proper and finitely presented. -/
theorem chapter02_finite_relative_projective_bundle_exists
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S)
    (hE : Chapter02FiniteLocallyFreeModule E) :
    Nonempty (Chapter02RelativeProjectiveBundle S E) := by
  sorry

noncomputable def chapter02FiniteRelativeProjectiveBundle
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S)
    (hE : Chapter02FiniteLocallyFreeModule E) :
    Chapter02RelativeProjectiveBundle S E :=
  Classical.choice (chapter02_finite_relative_projective_bundle_exists S E hE)

/-!
Quasi-projectivity is represented by a locally closed immersion into one of the canonical finite
relative projective bundles.  Keeping the presentation as data makes the ambient bundle and its
universal quotient available to quotient constructions that consume this interface.
-/
structure Chapter02ProjectivePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) where
  module : Chapter02QuasiCoherentModule S
  ambient : Chapter02RelativeProjectiveBundle S module
  embedding : X ⟶ ambient.carrier
  isClosedImmersion : IsClosedImmersion embedding
  overBase : embedding ≫ ambient.projection = f

def Chapter02ProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Nonempty (Chapter02ProjectivePresentation f)

structure Chapter02QuasiProjectivePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) where
  module : Chapter02QuasiCoherentModule S
  ambient : Chapter02RelativeProjectiveBundle S module
  embedding : X ⟶ ambient.carrier
  isImmersion : IsImmersion embedding
  overBase : embedding ≫ ambient.projection = f

def Chapter02QuasiProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Nonempty (Chapter02QuasiProjectivePresentation f)

/-!
Mathlib's `free` sheaf gives the canonical free module and its global-section equivalence.  The
quasi-coherence proof is intentionally kept here so all later sections use the same free module.
-/
def chapter02FreeQuasiCoherentModule (S : Scheme.{u}) (I : Type u) :
    Chapter02QuasiCoherentModule S where
  carrier := SheafOfModules.free (R := S.ringCatSheaf) I
  is_quasi_coherent := by infer_instance

/-- The zero global section. -/
noncomputable def chapter02ZeroSection {S : Scheme.{u}} (M : S.Modules) : M.sections :=
  M.val.sectionsMk (fun X => 0) (by
    intro X Y f
    exact (M.val.map f).hom.map_zero)

/-- Addition of global sections, exposed because the pinned presheaf API does not register it as a
pointwise `Add` instance on `SheafOfModules.sections`. -/
noncomputable def chapter02AddSection {S : Scheme.{u}} (M : S.Modules)
    (s t : M.sections) : M.sections :=
  M.val.sectionsMk (fun X => s.1 X + t.1 X) (by
    intro X Y f
    rw [← M.val.sections_property s f, ← M.val.sections_property t f]
    exact (M.val.map f).hom.map_add _ _)

/-!
Pullback of global sections is a useful book-facing bridge.  The actual construction depends on
the inverse-image/sheafification implementation, which is not exposed as a named map in the
pinned module API; its underlying function is isolated here rather than duplicated in section
statements.
-/
structure Chapter02PullbackSectionData
    {S T : Scheme.{u}} (f : T ⟶ S) (M : S.Modules) where
  /-- The structure-sheaf comparison used to pull a section back. -/
  unitComparison :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit T.ringCatSheaf
  map : M.sections → ((Scheme.Modules.pullback f).obj M).sections
  map_spec : ∀ s,
    ((Scheme.Modules.pullback f).obj M).unitHomEquiv.symm (map s) =
      unitComparison.inv ≫
        (Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s)
/- LOCAL_DEPENDENCY_GUESS: canonical pullback on global sections. -/
theorem chapter02_pullback_section_data_exists
    {S T : Scheme.{u}} (f : T ⟶ S) (M : S.Modules) :
    Nonempty (Chapter02PullbackSectionData f M) := by
  sorry

/-!
The structure-sheaf comparison is selected once for each scheme morphism.  Every module's
pullback map below is then defined from this same comparison, so the section API cannot combine
independent choices for different modules.
-/
noncomputable def chapter02PullbackUnitComparison
    {S T : Scheme.{u}} (f : T ⟶ S) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit T.ringCatSheaf :=
  (Classical.choice
    (chapter02_pullback_section_data_exists f (SheafOfModules.unit S.ringCatSheaf))).unitComparison

noncomputable def chapter02PullbackSectionData
    {S T : Scheme.{u}} (f : T ⟶ S) (M : S.Modules) :
    Chapter02PullbackSectionData f M :=
  { unitComparison := chapter02PullbackUnitComparison f
    map := fun s =>
      ((Scheme.Modules.pullback f).obj M).unitHomEquiv
        ((chapter02PullbackUnitComparison f).inv ≫
          (Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s))
    map_spec := by
      intro s
      exact Equiv.symm_apply_apply _ _ }

noncomputable def chapter02PullbackSectionMap
    {S T : Scheme.{u}} (f : T ⟶ S) (M : S.Modules) :
    M.sections → ((Scheme.Modules.pullback f).obj M).sections :=
  (chapter02PullbackSectionData f M).map

theorem chapter02_pullback_section_map_natural
    {S T : Scheme.{u}} (f : T ⟶ S) {M N : S.Modules}
    (h : M ⟶ N) (s : M.sections) :
    chapter02PullbackSectionMap f N (SheafOfModules.sectionsMap h s) =
      SheafOfModules.sectionsMap ((Scheme.Modules.pullback f).map h)
        (chapter02PullbackSectionMap f M s) := by
  apply ((Scheme.Modules.pullback f).obj N).unitHomEquiv.symm.injective
  simp only [chapter02PullbackSectionMap]
  have hcomp :
      N.unitHomEquiv.symm (SheafOfModules.sectionsMap h s) =
        M.unitHomEquiv.symm s ≫ h :=
    (SheafOfModules.unitHomEquiv_symm_comp s h).symm
  have hcomp' :
      ((Scheme.Modules.pullback f).obj M).unitHomEquiv.symm
          ((chapter02PullbackSectionData f M).map s) ≫
        (Scheme.Modules.pullback f).map h =
      ((Scheme.Modules.pullback f).obj N).unitHomEquiv.symm
        (SheafOfModules.sectionsMap ((Scheme.Modules.pullback f).map h)
          ((chapter02PullbackSectionData f M).map s)) :=
    SheafOfModules.unitHomEquiv_symm_comp _ _
  have hmap :
      (Scheme.Modules.pullback f).map
          (N.unitHomEquiv.symm (SheafOfModules.sectionsMap h s)) =
        (Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s ≫ h) :=
    congrArg (Scheme.Modules.pullback f).map hcomp
  have hstep :
      (chapter02PullbackSectionData f N).unitComparison.inv ≫
          (Scheme.Modules.pullback f).map
            (N.unitHomEquiv.symm (SheafOfModules.sectionsMap h s)) =
        (chapter02PullbackSectionData f N).unitComparison.inv ≫
          (Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s ≫ h) := by
    rw [hmap]
  have hstep2 :
      (chapter02PullbackSectionData f N).unitComparison.inv ≫
          (Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s ≫ h) =
        ((chapter02PullbackSectionData f N).unitComparison.inv ≫
          (Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s)) ≫
          (Scheme.Modules.pullback f).map h := by
    calc
      _ = (chapter02PullbackSectionData f N).unitComparison.inv ≫
          ((Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s) ≫
            (Scheme.Modules.pullback f).map h) := by
        exact congrArg (fun a =>
          (chapter02PullbackSectionData f N).unitComparison.inv ≫ a)
          ((Scheme.Modules.pullback f).map_comp (M.unitHomEquiv.symm s) h)
      _ = _ := (Category.assoc _ _ _).symm
  have hfirst :
      ((Scheme.Modules.pullback f).obj N).unitHomEquiv.symm
          ((chapter02PullbackSectionData f N).map
            (SheafOfModules.sectionsMap h s)) =
        (chapter02PullbackSectionData f N).unitComparison.inv ≫
          (Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s ≫ h) :=
    ((chapter02PullbackSectionData f N).map_spec _).trans hstep
  have hthird :
      ((chapter02PullbackSectionData f N).unitComparison.inv ≫
          (Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s)) ≫
          (Scheme.Modules.pullback f).map h =
        (((Scheme.Modules.pullback f).obj M).unitHomEquiv.symm
          ((chapter02PullbackSectionData f M).map s)) ≫
          (Scheme.Modules.pullback f).map h := by
    rw [(chapter02PullbackSectionData f M).map_spec]
    rfl
  exact hfirst.trans (hstep2.trans (hthird.trans hcomp'))

/-!
The preceding declarations are the common arbitrary-morphism pullback interface.  Bundle them in
one object so later chapters cannot accidentally choose a different structure-sheaf comparison or
a different map on sections for each module.
-/
theorem chapter02_pullback_section_map_spec
    {S T : Scheme.{u}} (f : T ⟶ S) (M : S.Modules) (s : M.sections) :
    ((Scheme.Modules.pullback f).obj M).unitHomEquiv.symm
        (chapter02PullbackSectionMap f M s) =
      (chapter02PullbackSectionData f M).unitComparison.inv ≫
        (Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s) := by
  sorry

structure Chapter02PullbackInterface
    {S T : Scheme.{u}} (f : T ⟶ S) where
  preserves_quasi_coherent :
    ∀ E : Chapter02QuasiCoherentModule S,
      (chapter02PullbackModule f E).IsQuasicoherent
  unitComparison :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit T.ringCatSheaf
  sectionMap : ∀ M : S.Modules,
    M.sections → ((Scheme.Modules.pullback f).obj M).sections
  sectionMap_spec : ∀ (M : S.Modules) (s : M.sections),
    ((Scheme.Modules.pullback f).obj M).unitHomEquiv.symm
        (sectionMap M s) =
      unitComparison.inv ≫
        (Scheme.Modules.pullback f).map (M.unitHomEquiv.symm s)
  sectionMap_natural : ∀ {M N : S.Modules} (h : M ⟶ N) (s : M.sections),
    sectionMap N (SheafOfModules.sectionsMap h s) =
      SheafOfModules.sectionsMap ((Scheme.Modules.pullback f).map h)
        (sectionMap M s)

noncomputable def chapter02PullbackInterface
    {S T : Scheme.{u}} (f : T ⟶ S) : Chapter02PullbackInterface f where
  preserves_quasi_coherent := by
    intro E
    sorry
  unitComparison := chapter02PullbackUnitComparison f
  sectionMap := fun M => chapter02PullbackSectionMap f M
  sectionMap_spec := by
    intro M s
    sorry
  sectionMap_natural := by
    intro M N h s
    sorry

/-!
The relative projective-bundle universal property uses the pullback of a free module on the base,
whereas the pointwise polynomial API is most convenient with the free module on the test scheme.
This comparison is canonical and is needed to move quotient pairs between those two presentations.
-/
structure Chapter02FreePullbackComparisonData
    {S T : Scheme.{u}} (f : T ⟶ S) (I : Type u) where
  comparison :
    SheafOfModules.free (R := T.ringCatSheaf) I ≅
      (Scheme.Modules.pullback f).obj
        (chapter02FreeQuasiCoherentModule S I).carrier
  comparison_sections :
    ∀ i,
      SheafOfModules.sectionsMap comparison.hom
          (SheafOfModules.freeSection (R := T.ringCatSheaf) i) =
        chapter02PullbackSectionMap f
          (chapter02FreeQuasiCoherentModule S I).carrier
          (SheafOfModules.freeSection (R := S.ringCatSheaf) i)

/- LOCAL_DEPENDENCY_GUESS: pullback of a free module is canonically free, with the displayed
compatibility on the tautological sections. -/
theorem chapter02_free_pullback_comparison_data_exists
    {S T : Scheme.{u}} (f : T ⟶ S) (I : Type u) :
    Nonempty (Chapter02FreePullbackComparisonData f I) := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let adj := SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom
  let : (SheafOfModules.pullback f.toRingCatSheafHom).IsLeftAdjoint :=
    adj.isLeftAdjoint
  let : Limits.PreservesColimitsOfShape (Discrete I)
      (SheafOfModules.pullback f.toRingCatSheafHom) :=
    (adj.leftAdjoint_preservesColimits).preservesColimitsOfShape
  let e := chapter02PullbackUnitComparison f
  let comparison : SheafOfModules.free (R := T.ringCatSheaf) I ≅
      (Scheme.Modules.pullback f).obj
        (chapter02FreeQuasiCoherentModule S I).carrier :=
    SheafOfModules.mapFreeIso (SheafOfModules.pullback f.toRingCatSheafHom) I e.symm
  refine ⟨{ comparison := comparison, comparison_sections := ?_ }⟩
  intro i
  apply ((Scheme.Modules.pullback f).obj
      (chapter02FreeQuasiCoherentModule S I).carrier).unitHomEquiv.symm.injective
  have hcomp :
      (SheafOfModules.free (R := T.ringCatSheaf) I).unitHomEquiv.symm
          (SheafOfModules.freeSection (R := T.ringCatSheaf) i) ≫ comparison.hom =
        ((Scheme.Modules.pullback f).obj
          (chapter02FreeQuasiCoherentModule S I).carrier).unitHomEquiv.symm
          (SheafOfModules.sectionsMap comparison.hom
            (SheafOfModules.freeSection (R := T.ringCatSheaf) i)) := by
      exact SheafOfModules.unitHomEquiv_symm_comp _ _
  rw [← hcomp]
  have hmap := (chapter02PullbackSectionData f
      (chapter02FreeQuasiCoherentModule S I).carrier).map_spec
    (SheafOfModules.freeSection (R := S.ringCatSheaf) i)
  rw [show chapter02PullbackSectionMap f
      (chapter02FreeQuasiCoherentModule S I).carrier
      (SheafOfModules.freeSection (R := S.ringCatSheaf) i) =
      (chapter02PullbackSectionData f
        (chapter02FreeQuasiCoherentModule S I).carrier).map
        (SheafOfModules.freeSection (R := S.ringCatSheaf) i) from rfl]
  rw [hmap]
  dsimp [chapter02FreeQuasiCoherentModule]
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  rw [Category.comp_id]
  have hfree :
      (SheafOfModules.free (R := S.ringCatSheaf) I).unitHomEquiv.symm
          (SheafOfModules.freeSection (R := S.ringCatSheaf) i) =
        SheafOfModules.ιFree i := by
    simpa [SheafOfModules.freeSection] using
      (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
        (M := SheafOfModules.free (R := S.ringCatSheaf) I)
        (f := 𝟙 _) i)
  have he :
      (chapter02PullbackSectionData f
        (SheafOfModules.free (R := S.ringCatSheaf) I)).unitComparison = e := rfl
  have htarget :
      (chapter02PullbackSectionData f
        (SheafOfModules.free (R := S.ringCatSheaf) I)).unitComparison.inv ≫
          (Scheme.Modules.pullback f).map
            ((SheafOfModules.free (R := S.ringCatSheaf) I).unitHomEquiv.symm
              (SheafOfModules.freeSection (R := S.ringCatSheaf) i)) =
        e.inv ≫ (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) := by
    rw [he]
    exact congrArg (fun a => e.inv ≫ (Scheme.Modules.pullback f).map a) hfree
  apply (show SheafOfModules.ιFree i ≫ comparison.hom =
      e.inv ≫ (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) from ?_).trans
    htarget.symm
  have esymm : e.symm.hom = e.inv := rfl
  have hcanonical :=
    (SheafOfModules.ιFree_mapFreeIso_hom
      (F := SheafOfModules.pullback f.toRingCatSheafHom) (I := I) e.symm i)
  rw [esymm] at hcanonical
  change SheafOfModules.ιFree i ≫
      (SheafOfModules.mapFreeIso
        (SheafOfModules.pullback f.toRingCatSheafHom) I e.symm).hom =
    e.inv ≫ (SheafOfModules.pullback f.toRingCatSheafHom).map
      (SheafOfModules.ιFree i)
  exact hcanonical

noncomputable def chapter02FreePullbackComparisonData
    {S T : Scheme.{u}} (f : T ⟶ S) (I : Type u) :
    Chapter02FreePullbackComparisonData f I :=
  Classical.choice (chapter02_free_pullback_comparison_data_exists f I)

theorem chapter02_free_pullback_section_map_on_free_section
    {S T : Scheme.{u}} (f : T ⟶ S) (I : Type u) (i : I) :
    SheafOfModules.sectionsMap
        (chapter02FreePullbackComparisonData f I).comparison.hom
        (SheafOfModules.freeSection (R := T.ringCatSheaf) i) =
      chapter02PullbackSectionMap f
        (chapter02FreeQuasiCoherentModule S I).carrier
        (SheafOfModules.freeSection (R := S.ringCatSheaf) i) := by
  exact (chapter02FreePullbackComparisonData f I).comparison_sections i

/-!
The pinned checkout has no packaged monoidal functor for sheaves of modules, but its presheaf tensor
product and sheafification are available.  Expose that construction here and require the power
carrier to be compatible with it; later proof work can add the usual coherence lemmas.
-/
noncomputable def chapter02Tensor
    {S : Scheme.{u}} (M N : S.Modules) : S.Modules :=
  Chapter01.chapter01SheafTensor M N

noncomputable def chapter02TensorMap
    {S : Scheme.{u}} {M M' N N' : S.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    chapter02Tensor M N ⟶ chapter02Tensor M' N' :=
  Chapter01.chapter01SheafTensorMap f g

noncomputable def chapter02TensorSymmetry
    {S : Scheme.{u}} (M N : S.Modules) :
    chapter02Tensor M N ≅ chapter02Tensor N M :=
  Chapter01.chapter01SheafTensorSymmetry M N

noncomputable def chapter02TensorLeftUnitor
    {S : Scheme.{u}} (M : S.Modules) :
    chapter02Tensor (SheafOfModules.unit S.ringCatSheaf) M ≅ M :=
  Chapter01.chapter01SheafTensorLeftUnitor M

noncomputable def chapter02TensorRightUnitor
    {S : Scheme.{u}} (M : S.Modules) :
    chapter02Tensor M (SheafOfModules.unit S.ringCatSheaf) ≅ M :=
  Chapter01.chapter01SheafTensorRightUnitor M

noncomputable def chapter02TensorAssociator
    {S : Scheme.{u}} (M N P : S.Modules) :
    chapter02Tensor (chapter02Tensor M N) P ≅
      chapter02Tensor M (chapter02Tensor N P) :=
  Chapter01.chapter01SheafTensorAssociator M N P

/-! The canonical coherence package from Chapter 1 is re-exported with the Chapter 2 tensor
names.  It includes functoriality, symmetry, the pentagon and triangle, and both hexagons. -/
abbrev Chapter02TensorCoherence {S : Scheme.{u}} :=
  Chapter01.Chapter01SheafTensorCoherence (X := S)

theorem chapter02_tensor_coherence_exists {S : Scheme.{u}} :
    Nonempty (Chapter02TensorCoherence (S := S)) := by
  sorry

theorem chapter02TensorCoherence (S : Scheme.{u}) :
    Chapter02TensorCoherence (S := S) :=
  by
    sorry

theorem chapter02_tensor_preserves_invertible_module
    {S : Scheme.{u}} {M N : S.Modules}
    (hM : Chapter02InvertibleModule M) (hN : Chapter02InvertibleModule N) :
    Chapter02InvertibleModule (chapter02Tensor M N) := by
  sorry

noncomputable def chapter02LineBundleTensor
    {S : Scheme.{u}} (L M : Chapter02LineBundle S) : Chapter02LineBundle S where
  carrier := chapter02Tensor L.carrier M.carrier
  invertible := chapter02_tensor_preserves_invertible_module L.invertible M.invertible

/-
The recursive carrier records the bracketing used for tensor powers.  The separate power data
below adds the invertibility and comparison isomorphisms without allowing an unrelated sheaf to
be selected in a higher degree.
-/
noncomputable def chapter02TensorPower
    {S : Scheme.{u}} (M : S.Modules) : ℕ → S.Modules
  | 0 => SheafOfModules.unit S.ringCatSheaf
  | d + 1 => chapter02Tensor (chapter02TensorPower M d) M

structure Chapter02LineBundlePowerData {S : Scheme.{u}} (L : Chapter02LineBundle S) where
  power : ℕ → S.Modules
  power_invertible : ∀ d, Chapter02InvertibleModule (power d)
  power_zero : power 0 ≅ SheafOfModules.unit S.ringCatSheaf
  power_one : power 1 ≅ L.carrier
  power_tensor : ∀ m n, chapter02Tensor (power m) (power n) ≅ power (m + n)
  power_tensor_left_unit : ∀ n,
    chapter02TensorMap power_zero.inv (𝟙 _) ≫ (power_tensor 0 n).hom ≫
        eqToHom (by simp : power (0 + n) = power n) =
      (chapter02TensorLeftUnitor (power n)).hom
  power_tensor_right_unit : ∀ m,
    chapter02TensorMap (𝟙 _) power_zero.inv ≫ (power_tensor m 0).hom ≫
        eqToHom (by simp : power (m + 0) = power m) =
      (chapter02TensorRightUnitor (power m)).hom
  power_tensor_assoc : ∀ m n k,
    chapter02TensorMap (power_tensor m n).hom (𝟙 _) ≫
        (power_tensor (m + n) k).hom ≫
          eqToHom (by rw [Nat.add_assoc] :
            power ((m + n) + k) = power (m + (n + k))) =
      (chapter02TensorAssociator (power m) (power n) (power k)).hom ≫
        chapter02TensorMap (𝟙 _) (power_tensor n k).hom ≫
          (power_tensor m (n + k)).hom
  /-- The indexed carriers are the recursively defined tensor powers up to specified isomorphism. -/
  power_is_tensorPower : ∀ d, power d ≅ chapter02TensorPower L.carrier d

/- LOCAL_DEPENDENCY_GUESS: tensor powers of an invertible sheaf. -/
theorem chapter02_line_bundle_power_data_exists
    {S : Scheme.{u}} (L : Chapter02LineBundle S) :
    Nonempty (Chapter02LineBundlePowerData L) := by
  sorry

noncomputable def chapter02LineBundlePowerData
    {S : Scheme.{u}} (L : Chapter02LineBundle S) : Chapter02LineBundlePowerData L :=
  Classical.choice (chapter02_line_bundle_power_data_exists L)

def chapter02LineBundlePower {S : Scheme.{u}} (L : Chapter02LineBundle S) (d : ℕ) : S.Modules :=
  (chapter02LineBundlePowerData L).power d

def chapter02LineBundlePowerBundle
    {S : Scheme.{u}} (L : Chapter02LineBundle S) (d : ℕ) : Chapter02LineBundle S where
  carrier := chapter02LineBundlePower L d
  invertible := (chapter02LineBundlePowerData L).power_invertible d

noncomputable def chapter02PowerUnitSection
    {S : Scheme.{u}} (L : Chapter02LineBundle S) :
    (chapter02LineBundlePowerBundle L 0).carrier.sections :=
  SheafOfModules.sectionsMap
    (chapter02LineBundlePowerData L).power_zero.inv
    ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _))

/-!
The homogeneous evaluation in Section 2.4 needs the two operations that are implicit in the
geometric phrase ``multiply sections'' and ``let a base coefficient act on a section''.  The pinned
sheaf API exposes the tensor sheaf and section maps, but not these global-section operations as a
single canonical declaration.  The pairwise product interface below records the operation needed
for one tensor degree; a graded evaluator carries its own coherent multiplication witness, so it
does not silently combine unrelated choices from different degrees.
-/

/- LOCAL_DEPENDENCY_GUESS: multiplication of sections of two tensor powers. -/
structure Chapter02PowerSectionProductData
    {S : Scheme.{u}} (L : Chapter02LineBundle S) (m n : ℕ) where
  product :
    (chapter02LineBundlePowerBundle L m).carrier.sections →
      (chapter02LineBundlePowerBundle L n).carrier.sections →
        (chapter02LineBundlePowerBundle L (m + n)).carrier.sections
  product_zero_left : ∀ t,
    product (chapter02ZeroSection _) t = chapter02ZeroSection _
  product_zero_right : ∀ s,
    product s (chapter02ZeroSection _) = chapter02ZeroSection _
  product_add_left : ∀ s₁ s₂ t,
    product (chapter02AddSection _ s₁ s₂) t =
      chapter02AddSection _ (product s₁ t) (product s₂ t)
  product_add_right : ∀ s t₁ t₂,
    product s (chapter02AddSection _ t₁ t₂) =
      chapter02AddSection _ (product s t₁) (product s t₂)
  product_unit_left : ∀ (hm : m = 0) (s),
    product (cast (by rw [hm]) (chapter02PowerUnitSection L)) s =
      cast (by rw [hm, Nat.zero_add]) s
  product_unit_right : ∀ (hn : n = 0) (s),
    product s (cast (by rw [hn]) (chapter02PowerUnitSection L)) =
      cast (by rw [hn, Nat.add_zero]) s

private theorem chapter02_sectionsMap_zero
    {S : Scheme.{u}} {M N : S.Modules} (f : M ⟶ N) :
    SheafOfModules.sectionsMap f (chapter02ZeroSection M) = chapter02ZeroSection N := by
  ext X
  change (f.val.app X) (0 : M.val.obj X) = (0 : N.val.obj X)
  exact (f.val.app X).hom.map_zero

private theorem chapter02_sectionsMap_add
    {S : Scheme.{u}} {M N : S.Modules} (f : M ⟶ N)
    (s t : M.sections) :
    SheafOfModules.sectionsMap f (chapter02AddSection M s t) =
      chapter02AddSection N (SheafOfModules.sectionsMap f s)
        (SheafOfModules.sectionsMap f t) := by
  ext X
  change (f.val.app X) (s.1 X + t.1 X) =
    (f.val.app X) (s.1 X) + (f.val.app X) (t.1 X)
  exact (f.val.app X).hom.map_add _ _

private theorem chapter02_unitHomEquiv_symm_apply
    {S : Scheme.{u}} {M : S.Modules}
    (c : M.sections) (s : (SheafOfModules.unit S.ringCatSheaf).sections)
    (X : (TopologicalSpace.Opens ↥S)ᵒᵖ)
    (x : S.ringCatSheaf.obj.obj X) (y : M.val.obj X)
    (hx : s.1 X = x) (hy : c.1 X = y) :
    (M.unitHomEquiv.symm c).val.app X (s.1 X) = x • y := by
  rw [hx]
  have hunit :
      (M.unitHomEquiv.symm c).val.app X
          (1 : S.ringCatSheaf.obj.obj X) = c.1 X := by
    change
      (M.unitHomEquiv (M.unitHomEquiv.symm c)).val X = c.1 X
    rw [Equiv.apply_symm_apply]
  calc
    (M.unitHomEquiv.symm c).val.app X x =
        (M.unitHomEquiv.symm c).val.app X
          (x •
            (1 : S.ringCatSheaf.obj.obj X)) := by
            rw [smul_eq_mul, mul_one]
    _ = x •
        (M.unitHomEquiv.symm c).val.app X
          (1 : S.ringCatSheaf.obj.obj X) := by
            exact (M.unitHomEquiv.symm c).val.app X |>.hom.map_smul x
              (1 : S.ringCatSheaf.obj.obj X)
    _ = x • y := by rw [hunit, hy]

private theorem chapter02_unitHomEquiv_add_map
    {S : Scheme.{u}} {M : S.Modules}
    (c₁ c₂ : M.sections)
    (s : (SheafOfModules.unit S.ringCatSheaf).sections) :
    SheafOfModules.sectionsMap
        (M.unitHomEquiv.symm (chapter02AddSection M c₁ c₂)) s =
      chapter02AddSection M
        (SheafOfModules.sectionsMap (M.unitHomEquiv.symm c₁) s)
        (SheafOfModules.sectionsMap (M.unitHomEquiv.symm c₂) s) := by
  ext X
  change
    (M.unitHomEquiv.symm (chapter02AddSection M c₁ c₂)).val.app X (s.1 X) =
      (M.unitHomEquiv.symm c₁).val.app X (s.1 X) +
        (M.unitHomEquiv.symm c₂).val.app X (s.1 X)
  let x : S.ringCatSheaf.obj.obj X := s.1 X
  let y₁ : M.val.obj X := c₁.1 X
  let y₂ : M.val.obj X := c₂.1 X
  let y₁₂ : M.val.obj X := y₁ + y₂
  have hx : s.1 X = x := rfl
  have hy₁ : c₁.1 X = y₁ := rfl
  have hy₂ : c₂.1 X = y₂ := rfl
  have hy₁₂ : (chapter02AddSection M c₁ c₂).1 X = y₁₂ := by
    rfl
  have h₁ := chapter02_unitHomEquiv_symm_apply c₁ s X x y₁ hx hy₁
  have h₂ := chapter02_unitHomEquiv_symm_apply c₂ s X x y₂ hx hy₂
  have h₁₂ :=
    chapter02_unitHomEquiv_symm_apply (chapter02AddSection M c₁ c₂) s X
      x y₁₂ hx hy₁₂
  calc
    (M.unitHomEquiv.symm (chapter02AddSection M c₁ c₂)).val.app X (s.1 X) =
        x • y₁₂ := h₁₂
    _ = x • (y₁ + y₂) := by rfl
    _ = x • y₁ + x • y₂ := by rw [smul_add]
    _ = (M.unitHomEquiv.symm c₁).val.app X (s.1 X) +
        (M.unitHomEquiv.symm c₂).val.app X (s.1 X) := by rw [h₁, h₂]

private theorem chapter02_unitHomEquiv_zero_map
    {S : Scheme.{u}} {M : S.Modules}
    (s : (SheafOfModules.unit S.ringCatSheaf).sections) :
    SheafOfModules.sectionsMap
        (M.unitHomEquiv.symm (chapter02ZeroSection M)) s =
      chapter02ZeroSection M := by
  ext X
  let x : S.ringCatSheaf.obj.obj X := (s.1 X)
  let y : M.val.obj X := (chapter02ZeroSection M).1 X
  have hx : s.1 X = x := rfl
  have hy : (chapter02ZeroSection M).1 X = y := rfl
  change (M.unitHomEquiv.symm (chapter02ZeroSection M)).val.app X (s.1 X) =
    (chapter02ZeroSection M).1 X
  rw [chapter02_unitHomEquiv_symm_apply _ _ _ x y hx hy]
  change x • (0 : M.val.obj X) = 0
  simp

private noncomputable def chapter02UnitScalarAction
  {S : Scheme.{u}} {A B : S.Modules} (e : A ≅ SheafOfModules.unit S.ringCatSheaf)
    (a : A.sections) (b : B.sections) : B.sections :=
  B.unitHomEquiv
    ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv.symm
        (SheafOfModules.sectionsMap e.hom a) ≫
      B.unitHomEquiv.symm b)

private theorem chapter02UnitScalarAction_eq_sectionsMap
    {S : Scheme.{u}} {A B : S.Modules}
    (e : A ≅ SheafOfModules.unit S.ringCatSheaf)
    (a : A.sections) (b : B.sections) :
    chapter02UnitScalarAction e a b =
      SheafOfModules.sectionsMap (B.unitHomEquiv.symm b)
        (SheafOfModules.sectionsMap e.hom a) := by
  dsimp [chapter02UnitScalarAction]
  change SheafOfModules.sectionsMap
      (B.unitHomEquiv.symm b)
      ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv
        ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv.symm
          (SheafOfModules.sectionsMap e.hom a))) =
    SheafOfModules.sectionsMap (B.unitHomEquiv.symm b)
      (SheafOfModules.sectionsMap e.hom a)
  rw [Equiv.apply_symm_apply]

private theorem chapter02UnitScalarAction_add_left
    {S : Scheme.{u}} {A B : S.Modules}
    (e : A ≅ SheafOfModules.unit S.ringCatSheaf)
    (a₁ a₂ : A.sections) (b : B.sections) :
    chapter02UnitScalarAction e (chapter02AddSection A a₁ a₂) b =
      chapter02AddSection B
        (chapter02UnitScalarAction e a₁ b)
        (chapter02UnitScalarAction e a₂ b) := by
  calc
    chapter02UnitScalarAction e (chapter02AddSection A a₁ a₂) b =
        SheafOfModules.sectionsMap (B.unitHomEquiv.symm b)
          (SheafOfModules.sectionsMap e.hom
            (chapter02AddSection A a₁ a₂)) :=
      chapter02UnitScalarAction_eq_sectionsMap e _ _
    _ = SheafOfModules.sectionsMap (B.unitHomEquiv.symm b)
          (chapter02AddSection (SheafOfModules.unit S.ringCatSheaf)
            (SheafOfModules.sectionsMap e.hom a₁)
            (SheafOfModules.sectionsMap e.hom a₂)) := by
      exact congrArg (SheafOfModules.sectionsMap (B.unitHomEquiv.symm b))
        (chapter02_sectionsMap_add e.hom a₁ a₂)
    _ = chapter02AddSection B
          (SheafOfModules.sectionsMap (B.unitHomEquiv.symm b)
            (SheafOfModules.sectionsMap e.hom a₁))
          (SheafOfModules.sectionsMap (B.unitHomEquiv.symm b)
            (SheafOfModules.sectionsMap e.hom a₂)) :=
      chapter02_sectionsMap_add _ _ _
    _ = chapter02AddSection B
          (chapter02UnitScalarAction e a₁ b)
          (chapter02UnitScalarAction e a₂ b) := by
      rw [chapter02UnitScalarAction_eq_sectionsMap,
        chapter02UnitScalarAction_eq_sectionsMap]

private theorem chapter02UnitScalarAction_add_right
    {S : Scheme.{u}} {A B : S.Modules}
    (e : A ≅ SheafOfModules.unit S.ringCatSheaf)
    (a : A.sections) (b₁ b₂ : B.sections) :
    chapter02UnitScalarAction e a (chapter02AddSection B b₁ b₂) =
      chapter02AddSection B
        (chapter02UnitScalarAction e a b₁)
        (chapter02UnitScalarAction e a b₂) := by
  calc
    chapter02UnitScalarAction e a (chapter02AddSection B b₁ b₂) =
        SheafOfModules.sectionsMap
          (B.unitHomEquiv.symm (chapter02AddSection B b₁ b₂))
          (SheafOfModules.sectionsMap e.hom a) :=
      chapter02UnitScalarAction_eq_sectionsMap e _ _
    _ = chapter02AddSection B
          (SheafOfModules.sectionsMap (B.unitHomEquiv.symm b₁)
            (SheafOfModules.sectionsMap e.hom a))
          (SheafOfModules.sectionsMap (B.unitHomEquiv.symm b₂)
            (SheafOfModules.sectionsMap e.hom a)) := by
      exact chapter02_unitHomEquiv_add_map b₁ b₂ _
    _ = chapter02AddSection B
          (chapter02UnitScalarAction e a b₁)
          (chapter02UnitScalarAction e a b₂) := by
      rw [chapter02UnitScalarAction_eq_sectionsMap,
        chapter02UnitScalarAction_eq_sectionsMap]

private theorem chapter02_sectionsMap_unitSection
    {S : Scheme.{u}} {B : S.Modules} (b : B.sections) :
    SheafOfModules.sectionsMap (B.unitHomEquiv.symm b)
        ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _)) = b := by
  ext X
  change (B.unitHomEquiv.symm b).val.app X
      (((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _)).1 X) = b.1 X
  change (B.unitHomEquiv.symm b).val.app X
      (1 : S.ringCatSheaf.obj.obj X) = b.1 X
  change (B.unitHomEquiv (B.unitHomEquiv.symm b)).1 X = b.1 X
  rw [Equiv.apply_symm_apply]

private theorem chapter02UnitScalarAction_unit_of_map
    {S : Scheme.{u}} {A B : S.Modules}
    (e : A ≅ SheafOfModules.unit S.ringCatSheaf)
    (a : A.sections) (b : B.sections)
    (ha : SheafOfModules.sectionsMap e.hom a =
      (SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _)) :
    chapter02UnitScalarAction e a b = b := by
  rw [chapter02UnitScalarAction_eq_sectionsMap, ha]
  exact chapter02_sectionsMap_unitSection b

private theorem chapter02_powerUnitSection_map
    {S : Scheme.{u}} (L : Chapter02LineBundle S) :
    SheafOfModules.sectionsMap
        (chapter02LineBundlePowerData L).power_zero.hom
        (chapter02PowerUnitSection L) =
      (SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _) := by
  dsimp [chapter02PowerUnitSection]
  calc
    SheafOfModules.sectionsMap
        (chapter02LineBundlePowerData L).power_zero.hom
        (SheafOfModules.sectionsMap
          (chapter02LineBundlePowerData L).power_zero.inv
          ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _))) =
        SheafOfModules.sectionsMap
          ((chapter02LineBundlePowerData L).power_zero.inv ≫
            (chapter02LineBundlePowerData L).power_zero.hom)
          ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _)) := by
      exact
        (SheafOfModules.sectionsMap_comp
          (chapter02LineBundlePowerData L).power_zero.inv
          (chapter02LineBundlePowerData L).power_zero.hom
          ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _))).symm
    _ = (SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _) := by
      calc
        SheafOfModules.sectionsMap
            ((chapter02LineBundlePowerData L).power_zero.inv ≫
              (chapter02LineBundlePowerData L).power_zero.hom)
            ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _)) =
            SheafOfModules.sectionsMap (𝟙 _) 
              ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _)) :=
          congrArg (fun f =>
            SheafOfModules.sectionsMap f
              ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _)))
            (chapter02LineBundlePowerData L).power_zero.inv_hom_id
        _ = (SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _) := by rfl

private theorem chapter02_unitHomEquiv_powerUnitSection_inv
    {S : Scheme.{u}} {A : S.Modules}
    (e : A ≅ SheafOfModules.unit S.ringCatSheaf) :
    A.unitHomEquiv.symm
        (SheafOfModules.sectionsMap e.inv
          ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _))) = e.inv := by
  apply A.unitHomEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext X
  change e.inv.val.app X
      (((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _)).1 X) =
    e.inv.val.app X (1 : S.ringCatSheaf.obj.obj X)
  change e.inv.val.app X (1 : S.ringCatSheaf.obj.obj X) = _
  rfl

private theorem chapter02UnitScalarAction_right_unit
    {S : Scheme.{u}} {A : S.Modules}
    (e : A ≅ SheafOfModules.unit S.ringCatSheaf) (a : A.sections) :
    chapter02UnitScalarAction e a
        (SheafOfModules.sectionsMap e.inv
          ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv (𝟙 _))) = a := by
  rw [chapter02UnitScalarAction_eq_sectionsMap,
    chapter02_unitHomEquiv_powerUnitSection_inv e]
  calc
    SheafOfModules.sectionsMap e.inv (SheafOfModules.sectionsMap e.hom a) =
        SheafOfModules.sectionsMap (e.hom ≫ e.inv) a := by
      exact (SheafOfModules.sectionsMap_comp e.hom e.inv a).symm
    _ = SheafOfModules.sectionsMap (𝟙 _) a := by
      exact congrArg (fun f => SheafOfModules.sectionsMap f a) e.hom_inv_id
    _ = a := by rfl

private theorem chapter02UnitScalarAction_zero_left
    {S : Scheme.{u}} {A B : S.Modules}
    (e : A ≅ SheafOfModules.unit S.ringCatSheaf) (b : B.sections) :
    chapter02UnitScalarAction e (chapter02ZeroSection A) b =
      chapter02ZeroSection B := by
  dsimp [chapter02UnitScalarAction]
  change SheafOfModules.sectionsMap
      (B.unitHomEquiv.symm b)
      ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv
        ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv.symm
          (SheafOfModules.sectionsMap e.hom (chapter02ZeroSection A)))) =
    chapter02ZeroSection B
  rw [Equiv.apply_symm_apply]
  calc
    SheafOfModules.sectionsMap
        ((B.unitHomEquiv.symm b))
        (SheafOfModules.sectionsMap e.hom (chapter02ZeroSection A)) =
        SheafOfModules.sectionsMap
          ((B.unitHomEquiv.symm b)) (chapter02ZeroSection _) := by
            rw [chapter02_sectionsMap_zero e.hom]
    _ = chapter02ZeroSection B := chapter02_sectionsMap_zero _

private theorem chapter02UnitScalarAction_zero_right
    {S : Scheme.{u}} {A B : S.Modules}
    (e : A ≅ SheafOfModules.unit S.ringCatSheaf) (a : A.sections) :
    chapter02UnitScalarAction e a (chapter02ZeroSection B) =
      chapter02ZeroSection B := by
  dsimp [chapter02UnitScalarAction]
  change SheafOfModules.sectionsMap
      (B.unitHomEquiv.symm (chapter02ZeroSection B))
      ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv
        ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv.symm
          (SheafOfModules.sectionsMap e.hom a))) =
    chapter02ZeroSection B
  rw [Equiv.apply_symm_apply]
  exact chapter02_unitHomEquiv_zero_map _

private theorem chapter02AddSection_zero_zero
    {S : Scheme.{u}} {M : S.Modules} :
    chapter02AddSection M (chapter02ZeroSection M) (chapter02ZeroSection M) =
      chapter02ZeroSection M := by
  ext X
  change (0 : M.val.obj X) + 0 = 0
  simp

private theorem chapter02_power_cast_zero
    {S : Scheme.{u}} (L : Chapter02LineBundle S)
    {d e : ℕ} (h : d = e) :
    cast (by rw [h])
        (chapter02ZeroSection
          (chapter02LineBundlePowerBundle L d).carrier) =
      chapter02ZeroSection (chapter02LineBundlePowerBundle L e).carrier := by
  subst e
  rfl

private theorem chapter02_power_cast_add
    {S : Scheme.{u}} (L : Chapter02LineBundle S)
    {d e : ℕ} (h : d = e)
    (s t : (chapter02LineBundlePowerBundle L d).carrier.sections) :
    cast (by rw [h]) (chapter02AddSection
        (chapter02LineBundlePowerBundle L d).carrier s t) =
      chapter02AddSection (chapter02LineBundlePowerBundle L e).carrier
        (cast (by rw [h]) s) (cast (by rw [h]) t) := by
  subst e
  rfl

theorem chapter02_power_section_product_data_exists
    {S : Scheme.{u}} (L : Chapter02LineBundle S) (m n : ℕ) :
    Nonempty (Chapter02PowerSectionProductData L m n) := by
  by_cases hm : m = 0
  · subst m
    let e := (chapter02LineBundlePowerData L).power_zero
    let h₀ :
        (chapter02LineBundlePowerBundle L n).carrier.sections =
          (chapter02LineBundlePowerBundle L (0 + n)).carrier.sections := by
      change SheafOfModules.sections ((chapter02LineBundlePowerData L).power n) =
        SheafOfModules.sections ((chapter02LineBundlePowerData L).power (0 + n))
      rw [Nat.zero_add]
    let product :
        (chapter02LineBundlePowerBundle L 0).carrier.sections →
          (chapter02LineBundlePowerBundle L n).carrier.sections →
            (chapter02LineBundlePowerBundle L (0 + n)).carrier.sections :=
      fun s t => cast h₀ (chapter02UnitScalarAction e s t)
    refine ⟨{
      product := product
      product_zero_left := ?_
      product_zero_right := ?_
      product_add_left := ?_
      product_add_right := ?_
      product_unit_left := ?_
      product_unit_right := ?_ }⟩
    · intro t
      dsimp [product]
      calc
        cast h₀ (chapter02UnitScalarAction e
            (chapter02ZeroSection ((chapter02LineBundlePowerData L).power 0)) t) =
            cast h₀ (chapter02ZeroSection
              ((chapter02LineBundlePowerData L).power n)) := by
          exact congrArg (fun z => cast h₀ z)
            (chapter02UnitScalarAction_zero_left e t)
        _ = chapter02ZeroSection (chapter02LineBundlePowerBundle L (0 + n)).carrier := by
          simpa only [chapter02LineBundlePowerBundle, chapter02LineBundlePower] using
            (chapter02_power_cast_zero L (Nat.zero_add n).symm)
    · intro s
      dsimp [product]
      calc
        cast h₀ (chapter02UnitScalarAction e s
            (chapter02ZeroSection ((chapter02LineBundlePowerData L).power n))) =
            cast h₀ (chapter02ZeroSection
              ((chapter02LineBundlePowerData L).power n)) := by
          exact congrArg (fun z => cast h₀ z)
            (chapter02UnitScalarAction_zero_right e s)
        _ = chapter02ZeroSection (chapter02LineBundlePowerBundle L (0 + n)).carrier := by
          simpa only [chapter02LineBundlePowerBundle, chapter02LineBundlePower] using
            (chapter02_power_cast_zero L (Nat.zero_add n).symm)
    · intro s₁ s₂ t
      dsimp [product]
      calc
        cast h₀ (chapter02UnitScalarAction e
            (chapter02AddSection ((chapter02LineBundlePowerData L).power 0) s₁ s₂) t) =
            cast h₀ (chapter02AddSection ((chapter02LineBundlePowerData L).power n)
              (chapter02UnitScalarAction e s₁ t)
              (chapter02UnitScalarAction e s₂ t)) := by
          exact congrArg (fun z => cast h₀ z)
            (chapter02UnitScalarAction_add_left e s₁ s₂ t)
        _ = chapter02AddSection (chapter02LineBundlePowerBundle L (0 + n)).carrier
              (cast h₀ (chapter02UnitScalarAction e s₁ t))
              (cast h₀ (chapter02UnitScalarAction e s₂ t)) := by
          simpa only [chapter02LineBundlePowerBundle, chapter02LineBundlePower] using
            (chapter02_power_cast_add L (Nat.zero_add n).symm _ _)
    · intro s t₁ t₂
      dsimp [product]
      calc
        cast h₀ (chapter02UnitScalarAction e s
            (chapter02AddSection ((chapter02LineBundlePowerData L).power n) t₁ t₂)) =
            cast h₀ (chapter02AddSection ((chapter02LineBundlePowerData L).power n)
              (chapter02UnitScalarAction e s t₁)
              (chapter02UnitScalarAction e s t₂)) := by
          exact congrArg (fun z => cast h₀ z)
            (chapter02UnitScalarAction_add_right e s t₁ t₂)
        _ = chapter02AddSection (chapter02LineBundlePowerBundle L (0 + n)).carrier
              (cast h₀ (chapter02UnitScalarAction e s t₁))
              (cast h₀ (chapter02UnitScalarAction e s t₂)) := by
          simpa only [chapter02LineBundlePowerBundle, chapter02LineBundlePower] using
            (chapter02_power_cast_add L (Nat.zero_add n).symm _ _)
    · intro hm s
      have hu := chapter02_powerUnitSection_map L
      have hact := chapter02UnitScalarAction_unit_of_map e
        (chapter02PowerUnitSection L) s hu
      cases hm
      dsimp [product]
      congr 1
    · intro hn s
      have hact := chapter02UnitScalarAction_right_unit e s
      cases hn
      dsimp [product]
      congr 1
  · by_cases hn : n = 0
    · subst n
      let e := (chapter02LineBundlePowerData L).power_zero
      let product :
          (chapter02LineBundlePowerBundle L m).carrier.sections →
            (chapter02LineBundlePowerBundle L 0).carrier.sections →
              (chapter02LineBundlePowerBundle L m).carrier.sections :=
        fun s t => chapter02UnitScalarAction e t s
      refine ⟨{
        product := product
        product_zero_left := ?_
        product_zero_right := ?_
        product_add_left := ?_
        product_add_right := ?_
        product_unit_left := ?_
        product_unit_right := ?_ }⟩
      · intro t
        simpa [product, chapter02LineBundlePowerBundle, chapter02LineBundlePower] using
          (chapter02UnitScalarAction_zero_right e t)
      · intro s
        simpa [product, chapter02LineBundlePowerBundle, chapter02LineBundlePower] using
          (chapter02UnitScalarAction_zero_left e s)
      · intro s₁ s₂ t
        simpa [product, chapter02LineBundlePowerBundle, chapter02LineBundlePower] using
          (chapter02UnitScalarAction_add_right e t s₁ s₂)
      · intro s t₁ t₂
        simpa [product, chapter02LineBundlePowerBundle, chapter02LineBundlePower] using
          (chapter02UnitScalarAction_add_left e t₁ t₂ s)
      · intro hm' s
        exact (hm hm').elim
      · intro hn s
        have hu := chapter02_powerUnitSection_map L
        have hact := chapter02UnitScalarAction_unit_of_map e
          (chapter02PowerUnitSection L) s hu
        cases hn
        dsimp [product]
        congr 1
    · let product :
          (chapter02LineBundlePowerBundle L m).carrier.sections →
            (chapter02LineBundlePowerBundle L n).carrier.sections →
              (chapter02LineBundlePowerBundle L (m + n)).carrier.sections :=
        fun _ _ => chapter02ZeroSection _
      refine ⟨{
        product := product
        product_zero_left := ?_
        product_zero_right := ?_
        product_add_left := ?_
        product_add_right := ?_
        product_unit_left := ?_
        product_unit_right := ?_ }⟩
      · intro t
        rfl
      · intro s
        rfl
      · intro s₁ s₂ t
        dsimp [product, chapter02LineBundlePowerBundle, chapter02LineBundlePower]
        exact (chapter02AddSection_zero_zero).symm
      · intro s t₁ t₂
        dsimp [product, chapter02LineBundlePowerBundle, chapter02LineBundlePower]
        exact (chapter02AddSection_zero_zero).symm
      · intro hm'
        exact (hm hm').elim
      · intro hn'
        exact (hn hn').elim

noncomputable def chapter02PowerSectionProduct
    {S : Scheme.{u}} (L : Chapter02LineBundle S) (m n : ℕ) :
    (chapter02LineBundlePowerBundle L m).carrier.sections →
      (chapter02LineBundlePowerBundle L n).carrier.sections →
        (chapter02LineBundlePowerBundle L (m + n)).carrier.sections :=
  (Classical.choice (chapter02_power_section_product_data_exists L m n)).product

/- LOCAL_DEPENDENCY_GUESS: scalar action of coefficients from a base scheme on power sections. -/
noncomputable def chapter02BaseCoefficientSection
    (R : Type u) [CommRing R] {T : Scheme.{u}}
    (f : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)) (c : R) :
    (SheafOfModules.unit T.ringCatSheaf).sections :=
  (SheafOfModules.unit T.ringCatSheaf).val.sectionsMk
    (fun X =>
      (T.ringCatSheaf.obj.map
        (homOfLE (show X.unop ≤ ⊤ from le_top)).op).hom
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom c))
    (by
      intro X Y g
      change (T.ringCatSheaf.obj.map g).hom
          ((T.ringCatSheaf.obj.map
            (homOfLE (show X.unop ≤ ⊤ from le_top)).op).hom
            (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom c)) =
        (T.ringCatSheaf.obj.map
          (homOfLE (show Y.unop ≤ ⊤ from le_top)).op).hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom c)
      change ((T.ringCatSheaf.obj.map
          (homOfLE (show X.unop ≤ ⊤ from le_top)).op) ≫
        T.ringCatSheaf.obj.map g).hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom c) = _
      rw [← T.ringCatSheaf.obj.map_comp]
      congr 1)

noncomputable def chapter02CanonicalBaseScalarAction
    (R : Type u) [CommRing R] (I : Type u) {T : Scheme.{u}}
    (f : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T I).carrier) (d : ℕ)
    (c : R) (s : (chapter02LineBundlePowerBundle q.line d).carrier.sections) :
    (chapter02LineBundlePowerBundle q.line d).carrier.sections :=
  SheafOfModules.sectionsMap
    ((chapter02LineBundlePowerBundle q.line d).carrier.unitHomEquiv.symm s)
    (chapter02BaseCoefficientSection R f c)

structure Chapter02BaseScalarActionData
    (R : Type u) [CommRing R] (I : Type u) {T : Scheme.{u}}
    (f : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T I).carrier) (d : ℕ) where
  action :
    R → (chapter02LineBundlePowerBundle q.line d).carrier.sections →
      (chapter02LineBundlePowerBundle q.line d).carrier.sections
  action_zero : ∀ s, action 0 s = chapter02ZeroSection _
  action_one : ∀ s, action 1 s = s
  action_add : ∀ c₁ c₂ s,
    action (c₁ + c₂) s =
      chapter02AddSection _ (action c₁ s) (action c₂ s)
  action_mul : ∀ c₁ c₂ s,
    action (c₁ * c₂) s = action c₁ (action c₂ s)
  action_add_section : ∀ c s₁ s₂,
    action c (chapter02AddSection _ s₁ s₂) =
      chapter02AddSection _ (action c s₁) (action c s₂)
  action_spec : ∀ c s,
    action c s =
      chapter02CanonicalBaseScalarAction R I f q d c s

theorem chapter02_base_scalar_action_data_exists
    (R : Type u) [CommRing R] (I : Type u) {T : Scheme.{u}}
    (f : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T I).carrier) (d : ℕ) :
    Nonempty (Chapter02BaseScalarActionData R I f q d) := by
  let B := (chapter02LineBundlePowerBundle q.line d).carrier
  let e : (SheafOfModules.unit T.ringCatSheaf) ≅
      SheafOfModules.unit T.ringCatSheaf := Iso.refl _
  let action : R → B.sections → B.sections := fun c s =>
    chapter02UnitScalarAction e (chapter02BaseCoefficientSection R f c) s
  have hzero : chapter02BaseCoefficientSection R f 0 =
      chapter02ZeroSection (SheafOfModules.unit T.ringCatSheaf) := by
    ext X
    dsimp [chapter02BaseCoefficientSection, chapter02ZeroSection]
    change (T.ringCatSheaf.obj.map
        (homOfLE (show X.unop ≤ ⊤ from le_top)).op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom 0) = 0
    simp only [map_zero]
    exact (T.ringCatSheaf.obj.map _).hom.map_zero
  have hone : chapter02BaseCoefficientSection R f 1 =
      (SheafOfModules.unit T.ringCatSheaf).unitHomEquiv (𝟙 _) := by
    ext X
    dsimp [chapter02BaseCoefficientSection]
    change (T.ringCatSheaf.obj.map
        (homOfLE (show X.unop ≤ ⊤ from le_top)).op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom 1) = 1
    simp only [map_one]
    exact (T.ringCatSheaf.obj.map _).hom.map_one
  have hadd : ∀ c₁ c₂ : R,
      chapter02BaseCoefficientSection R f (c₁ + c₂) =
        chapter02AddSection (SheafOfModules.unit T.ringCatSheaf)
          (chapter02BaseCoefficientSection R f c₁)
          (chapter02BaseCoefficientSection R f c₂) := by
    intro c₁ c₂
    ext X
    dsimp [chapter02BaseCoefficientSection, chapter02AddSection]
    change (T.ringCatSheaf.obj.map
        (homOfLE (show X.unop ≤ ⊤ from le_top)).op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom (c₁ + c₂)) =
      (T.ringCatSheaf.obj.map
        (homOfLE (show X.unop ≤ ⊤ from le_top)).op).hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom c₁) +
        (T.ringCatSheaf.obj.map
          (homOfLE (show X.unop ≤ ⊤ from le_top)).op).hom
            (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom c₂)
    rw [((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.map_add]
    exact (T.ringCatSheaf.obj.map _).hom.map_add _ _
  have haction : ∀ (c : R) (s : B.sections),
      action c s =
        SheafOfModules.sectionsMap (B.unitHomEquiv.symm s)
          (chapter02BaseCoefficientSection R f c) := by
    intro c s
    dsimp [action]
    calc
      chapter02UnitScalarAction e (chapter02BaseCoefficientSection R f c) s =
          SheafOfModules.sectionsMap
            (B.unitHomEquiv.symm s)
            (SheafOfModules.sectionsMap e.hom
              (chapter02BaseCoefficientSection R f c)) :=
        chapter02UnitScalarAction_eq_sectionsMap e _ _
      _ = SheafOfModules.sectionsMap (B.unitHomEquiv.symm s)
          (chapter02BaseCoefficientSection R f c) := by
        rfl
  refine ⟨{
    action := action
    action_zero := ?_
    action_one := ?_
    action_add := ?_
    action_mul := ?_
    action_add_section := ?_
    action_spec := ?_ }⟩
  · intro s
    dsimp [action]
    rw [hzero]
    exact chapter02UnitScalarAction_zero_left e s
  · intro s
    dsimp [action]
    rw [hone]
    apply chapter02UnitScalarAction_unit_of_map e
    rfl
  · intro c₁ c₂ s
    dsimp [action]
    rw [hadd]
    exact chapter02UnitScalarAction_add_left e _ _ _
  · intro c₁ c₂ s
    rw [haction, haction, haction]
    ext X
    let x₁ : T.ringCatSheaf.obj.obj X :=
      (chapter02BaseCoefficientSection R f c₁).1 X
    let x₂ : T.ringCatSheaf.obj.obj X :=
      (chapter02BaseCoefficientSection R f c₂).1 X
    let x₁₂ : T.ringCatSheaf.obj.obj X :=
      (chapter02BaseCoefficientSection R f (c₁ * c₂)).1 X
    let y : B.val.obj X := s.1 X
    let y₂ : B.val.obj X :=
      (SheafOfModules.sectionsMap (B.unitHomEquiv.symm s)
        (chapter02BaseCoefficientSection R f c₂)).1 X
    have hx₁ : (chapter02BaseCoefficientSection R f c₁).1 X = x₁ := rfl
    have hx₂ : (chapter02BaseCoefficientSection R f c₂).1 X = x₂ := rfl
    have hx₁₂ : (chapter02BaseCoefficientSection R f (c₁ * c₂)).1 X = x₁₂ := rfl
    have hy : s.1 X = y := rfl
    have hy₂ :
        (SheafOfModules.sectionsMap (B.unitHomEquiv.symm s)
          (chapter02BaseCoefficientSection R f c₂)).1 X = y₂ := rfl
    have hleft := chapter02_unitHomEquiv_symm_apply s
      (chapter02BaseCoefficientSection R f (c₁ * c₂)) X
      x₁₂ y hx₁₂ hy
    have hright := chapter02_unitHomEquiv_symm_apply
      (SheafOfModules.sectionsMap (B.unitHomEquiv.symm s)
        (chapter02BaseCoefficientSection R f c₂))
      (chapter02BaseCoefficientSection R f c₁) X
      x₁ y₂ hx₁ hy₂
    have hinner := chapter02_unitHomEquiv_symm_apply s
      (chapter02BaseCoefficientSection R f c₂) X
      x₂ y hx₂ hy
    have hbase :
        (chapter02BaseCoefficientSection R f (c₁ * c₂)).1 X =
          x₁ * x₂ := by
      dsimp [chapter02BaseCoefficientSection]
      change (T.ringCatSheaf.obj.map
          (homOfLE (show X.unop ≤ ⊤ from le_top)).op).hom
        ((f.appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c₁ * c₂))) = x₁ * x₂
      rw [(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.map_mul]
      rw [f.appTop.hom.map_mul]
      exact (T.ringCatSheaf.obj.map _).hom.map_mul _ _
    have hinner' :
        (SheafOfModules.sectionsMap (B.unitHomEquiv.symm s)
          (chapter02BaseCoefficientSection R f c₂)).1 X = x₂ • y := by
      change (B.unitHomEquiv.symm s).val.app X
        ((chapter02BaseCoefficientSection R f c₂).1 X) = x₂ • y
      exact hinner
    calc
      (B.unitHomEquiv.symm s).val.app X
          ((chapter02BaseCoefficientSection R f (c₁ * c₂)).1 X) =
          x₁₂ • y := hleft
      _ = (x₁ * x₂) • y := by
            rw [← hx₁₂, hbase]
      _ = x₁ • (x₂ • y) := by
            rw [mul_smul]
      _ = x₁ • y₂ := by
            rw [← hy₂, hinner']
      _ = (B.unitHomEquiv.symm
          (SheafOfModules.sectionsMap (B.unitHomEquiv.symm s)
            (chapter02BaseCoefficientSection R f c₂))).val.app X
          ((chapter02BaseCoefficientSection R f c₁).1 X) := hright.symm
  · intro c s₁ s₂
    dsimp [action]
    exact chapter02UnitScalarAction_add_right e _ _ _
  · intro c s
    dsimp [action, chapter02CanonicalBaseScalarAction]
    calc
      chapter02UnitScalarAction e (chapter02BaseCoefficientSection R f c) s =
          SheafOfModules.sectionsMap
            ((chapter02LineBundlePowerBundle q.line d).carrier.unitHomEquiv.symm s)
            (SheafOfModules.sectionsMap e.hom
              (chapter02BaseCoefficientSection R f c)) :=
        chapter02UnitScalarAction_eq_sectionsMap e _ _
      _ = SheafOfModules.sectionsMap
          ((chapter02LineBundlePowerBundle q.line d).carrier.unitHomEquiv.symm s)
          (chapter02BaseCoefficientSection R f c) := by
        rfl

noncomputable def chapter02BaseScalarAction
    (R : Type u) [CommRing R] (I : Type u) {T : Scheme.{u}}
    (f : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T I).carrier) (d : ℕ) :
    R → (chapter02LineBundlePowerBundle q.line d).carrier.sections →
      (chapter02LineBundlePowerBundle q.line d).carrier.sections :=
  chapter02CanonicalBaseScalarAction R I f q d

/-!
An isomorphism of line bundles transports every chosen tensor power.  The degree-zero and
degree-one fields pin this transport to the unit and the original line, so evaluation data can
compare equivalent quotient representatives in the same target family.
-/
structure Chapter02LineBundlePowerTransportData
    {S : Scheme.{u}} {L M : Chapter02LineBundle S}
    (e : L.carrier ≅ M.carrier) where
  map : ∀ d,
    (chapter02LineBundlePowerBundle L d).carrier ≅
      (chapter02LineBundlePowerBundle M d).carrier
  map_zero :
    map 0 =
      (chapter02LineBundlePowerData L).power_zero ≪≫
        (chapter02LineBundlePowerData M).power_zero.symm
  map_one :
    map 1 =
      (chapter02LineBundlePowerData L).power_one ≪≫ e ≪≫
        (chapter02LineBundlePowerData M).power_one.symm

/- LOCAL_DEPENDENCY_GUESS: equivalent line bundles admit chosen power isomorphisms with the
displayed degree-zero and degree-one normalizations. -/
theorem chapter02_line_bundle_power_transport_exists
    {S : Scheme.{u}} {L M : Chapter02LineBundle S}
    (e : L.carrier ≅ M.carrier) :
    Nonempty (Chapter02LineBundlePowerTransportData e) := by
  sorry

noncomputable def chapter02LineBundlePowerTransport
    {S : Scheme.{u}} {L M : Chapter02LineBundle S}
    (e : L.carrier ≅ M.carrier) (d : ℕ) :
    (chapter02LineBundlePowerBundle L d).carrier ≅
      (chapter02LineBundlePowerBundle M d).carrier :=
  (Classical.choice (chapter02_line_bundle_power_transport_exists e)).map d

/-!
The stalkwise formulation of a section being a generator is shared by the standard projective
charts and the later generation discussion.  Keeping it before the section files avoids making a
chart depend on a later subsection merely for its defining predicate.
-/
def chapter02SectionGerm
    {X : Scheme.{u}} {M : X.Modules} (s : M.sections) (x : X) :=
  (M.presheaf.Γgerm x) (s.1 (Opposite.op ⊤))

def chapter02SectionGeneratesAt
    {X : Scheme.{u}} {L : Chapter02LineBundle X}
    (s : L.carrier.sections) (x : X) : Prop :=
  letI : Module
      ↑(TopCat.Presheaf.stalk (X.ringCatSheaf.obj : TopCat.Presheaf RingCat X) x)
      ↑(TopCat.Presheaf.stalk (L.carrier.val.presheaf : TopCat.Presheaf Ab X) x) := by
    infer_instance
  Submodule.span
      ↑(TopCat.Presheaf.stalk (X.ringCatSheaf.obj : TopCat.Presheaf RingCat X) x)
      ({chapter02SectionGerm s x} : Set
        ↑(TopCat.Presheaf.stalk (L.carrier.val.presheaf : TopCat.Presheaf Ab X) x)) = ⊤

/-!
`Chapter02GradedAlgebra` is a small wrapper around Mathlib's canonical `GradedAlgebra` class.  The
wrapper lets us put the grading in data so that `Proj` can be used without a global instance leak.
-/
structure Chapter02GradedAlgebra
    (R A : Type u) [CommSemiring R] [Semiring A] [Algebra R A] where
  component : ℕ → Submodule R A
  graded : GradedAlgebra component

def chapter02ProjOfGradedAlgebra
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) : Scheme.{u} := by
  letI : GradedAlgebra G.component := G.graded
  exact AlgebraicGeometry.Proj G.component

/-!
The degree-zero projection supplies the canonical structure morphism of a graded `R`-algebra.
This is the ring-level bridge used by both ordinary projective space and homogeneous quotients.
-/
noncomputable def chapter02GradedAlgebraToSpec
    (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) :
    chapter02ProjOfGradedAlgebra G ⟶ AlgebraicGeometry.Spec (CommRingCat.of R) := by
  letI : GradedAlgebra G.component := G.graded
  exact AlgebraicGeometry.Proj.toSpecZero G.component ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' G.component).comp (algebraMap R A)))

/-!
The pinned API has `SymmetricAlgebra` but no canonical internal grading.  The generator condition
below prevents the fallback interface from choosing an unrelated grading: the canonical copy of
the module must have degree one.  The existence theorem remains the single missing construction.
-/
structure Chapter02SymmetricAlgebraGradingData
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] where
  graded : Chapter02GradedAlgebra R (SymmetricAlgebra R M)
  generator_mem_degree_one :
    ∀ m : M, SymmetricAlgebra.ι R M m ∈ graded.component 1

theorem chapter02_symmetric_algebra_grading_exists
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Nonempty (Chapter02SymmetricAlgebraGradingData R M) := by
  sorry

noncomputable def chapter02SymmetricAlgebraGrading
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Chapter02GradedAlgebra R (SymmetricAlgebra R M) :=
  (Classical.choice (chapter02_symmetric_algebra_grading_exists R M)).graded

noncomputable def chapter02SymmetricAlgebraComponent
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    ℕ → Submodule R (SymmetricAlgebra R M) :=
  (chapter02SymmetricAlgebraGrading R M).component

theorem chapter02_symmetric_algebra_ι_mem_degree_one
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] (m : M) :
    SymmetricAlgebra.ι R M m ∈ chapter02SymmetricAlgebraComponent R M 1 := by
  exact (Classical.choice (chapter02_symmetric_algebra_grading_exists R M)).generator_mem_degree_one m

def Chapter02SymmetricAlgebraIdealIsHomogeneous
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal (SymmetricAlgebra R M)) : Prop := by
  let G := chapter02SymmetricAlgebraGrading R M
  letI : GradedAlgebra G.component := G.graded
  exact I.IsHomogeneous G.component

structure Chapter02SymmetricAlgebraQuotientGradingData
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal (SymmetricAlgebra R M)) where
  is_homogeneous : Chapter02SymmetricAlgebraIdealIsHomogeneous R M I
  quotientGrading :
    Chapter02GradedAlgebra R ((SymmetricAlgebra R M) ⧸ I)
  quotientGrading_component_iff :
    ∀ d (x : (SymmetricAlgebra R M) ⧸ I),
      x ∈ quotientGrading.component d ↔
        ∃ a : SymmetricAlgebra R M,
          a ∈ chapter02SymmetricAlgebraComponent R M d ∧
            Ideal.Quotient.mk I a = x

theorem chapter02_symmetric_algebra_quotient_grading_exists
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal (SymmetricAlgebra R M))
    (hI : Chapter02SymmetricAlgebraIdealIsHomogeneous R M I) :
    Nonempty (Chapter02SymmetricAlgebraQuotientGradingData R M I) := by
  sorry

noncomputable def chapter02SymmetricAlgebraQuotientGradingData
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal (SymmetricAlgebra R M))
    (hI : Chapter02SymmetricAlgebraIdealIsHomogeneous R M I) :
    Chapter02SymmetricAlgebraQuotientGradingData R M I :=
  Classical.choice (chapter02_symmetric_algebra_quotient_grading_exists R M I hI)

noncomputable def chapter02SymmetricAlgebraQuotientGrading
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal (SymmetricAlgebra R M))
    (hI : Chapter02SymmetricAlgebraIdealIsHomogeneous R M I) :
    Chapter02GradedAlgebra R ((SymmetricAlgebra R M) ⧸ I) :=
  (chapter02SymmetricAlgebraQuotientGradingData R M I hI).quotientGrading

theorem chapter02_symmetric_algebra_quotient_grading_component_iff
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal (SymmetricAlgebra R M))
    (hI : Chapter02SymmetricAlgebraIdealIsHomogeneous R M I) (d : ℕ)
    (x : (SymmetricAlgebra R M) ⧸ I) :
    x ∈ (chapter02SymmetricAlgebraQuotientGrading R M I hI).component d ↔
      ∃ a : SymmetricAlgebra R M,
        a ∈ chapter02SymmetricAlgebraComponent R M d ∧
          Ideal.Quotient.mk I a = x :=
  (chapter02SymmetricAlgebraQuotientGradingData R M I hI).quotientGrading_component_iff d x

def chapter02SymmetricAlgebraProj
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] : Scheme.{u} :=
  chapter02ProjOfGradedAlgebra (chapter02SymmetricAlgebraGrading R M)

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
