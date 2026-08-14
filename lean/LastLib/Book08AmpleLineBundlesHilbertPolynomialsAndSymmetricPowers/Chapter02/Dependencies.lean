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

/-- Pullback of the underlying sheaf of modules. -/
def chapter02PullbackModule {S T : Scheme.{u}} (f : T ⟶ S)
    (E : Chapter02QuasiCoherentModule S) : T.Modules :=
  (Scheme.Modules.pullback f).obj E.carrier

/-- The book-facing quasi-coherent pullback; the preservation proof is supplied by the later API. -/
def chapter02PullbackQuasiCoherentModule {S T : Scheme.{u}} (f : T ⟶ S)
    (E : Chapter02QuasiCoherentModule S) : Chapter02QuasiCoherentModule T where
  carrier := chapter02PullbackModule f E
  is_quasi_coherent := by sorry

/-!
`LocalGeneratorsData` is the canonical Mathlib interface for local presentations.  Requiring
each free generator to have an index set equivalent to `Fin n` records the constant finite rank
condition without choosing a trivialization globally.
-/
def Chapter02LocallyFreeRank {S : Scheme.{u}} (E : S.Modules) (n : ℕ) : Prop :=
  ∃ q : E.LocalGeneratorsData.{u},
    q.IsLocallyFreeData ∧ ∀ i, Nonempty ((q.generators i).I ≃ Fin n)

def Chapter02InvertibleModule {S : Scheme.{u}} (L : S.Modules) : Prop :=
  Chapter02LocallyFreeRank L 1

/-- A line bundle is an invertible sheaf of modules. -/
structure Chapter02LineBundle (S : Scheme.{u}) where
  carrier : S.Modules
  invertible : Chapter02InvertibleModule carrier

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
  invertible := by sorry

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

/- LOCAL_DEPENDENCY_GUESS: relative Proj of a quasi-coherent module and the universal quotient. -/
theorem chapter02_relative_projective_bundle_exists
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Nonempty (Chapter02ProjectiveBundleData S E) := by
  sorry

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
  E.carrier.IsLocallyFree ∧ E.carrier.IsFiniteType

/-!
This is the canonical finite relative projective-bundle interface.  The `data` field is the
universal quotient package, while the last two fields expose the standard finiteness properties of
the finite locally free construction without replacing it by an unrelated ambient scheme.
-/
structure Chapter02RelativeProjectiveBundle
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) where
  finiteLocallyFree : Chapter02FiniteLocallyFreeModule E
  data : Chapter02ProjectiveBundleData S E
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

noncomputable def chapter02PullbackSectionData
    {S T : Scheme.{u}} (f : T ⟶ S) (M : S.Modules) :
    Chapter02PullbackSectionData f M :=
  Classical.choice (chapter02_pullback_section_data_exists f M)

/-!
The pinned checkout has no packaged monoidal functor for sheaves of modules, but its presheaf tensor
product and sheafification are available.  Expose that construction here and require the power
carrier to be compatible with it; later proof work can add the usual coherence lemmas.
-/
noncomputable def chapter02Tensor
    {S : Scheme.{u}} (M N : S.Modules) : S.Modules :=
  (PresheafOfModules.sheafification (𝟙 S.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj M.val N.val)

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
  /-- The indexed carriers are the recursively defined tensor powers of the line bundle. -/
  power_is_tensorPower : ∀ d, power d = chapter02TensorPower L.carrier d

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

/-!
The homogeneous evaluation in Section 2.4 needs the two operations that are implicit in the
geometric phrase ``multiply sections'' and ``let a base coefficient act on a section''.  The pinned
sheaf API exposes the tensor sheaf and section maps, but not these global-section operations as a
single canonical declaration.  Keep them as named construction interfaces here so the evaluation
laws are stated against fixed operations rather than against arbitrary functions.
-/

/- LOCAL_DEPENDENCY_GUESS: multiplication of sections of two tensor powers. -/
structure Chapter02PowerSectionProductData
    {S : Scheme.{u}} (L : Chapter02LineBundle S) (m n : ℕ) where
  product :
    (chapter02LineBundlePowerBundle L m).carrier.sections →
      (chapter02LineBundlePowerBundle L n).carrier.sections →
        (chapter02LineBundlePowerBundle L (m + n)).carrier.sections

theorem chapter02_power_section_product_data_exists
    {S : Scheme.{u}} (L : Chapter02LineBundle S) (m n : ℕ) :
    Nonempty (Chapter02PowerSectionProductData L m n) := by
  exact ⟨{ product := fun _ _ => chapter02ZeroSection _ }⟩

noncomputable def chapter02PowerSectionProduct
    {S : Scheme.{u}} (L : Chapter02LineBundle S) (m n : ℕ) :
    (chapter02LineBundlePowerBundle L m).carrier.sections →
      (chapter02LineBundlePowerBundle L n).carrier.sections →
        (chapter02LineBundlePowerBundle L (m + n)).carrier.sections :=
  (Classical.choice (chapter02_power_section_product_data_exists L m n)).product

/- LOCAL_DEPENDENCY_GUESS: scalar action of coefficients from a base scheme on power sections. -/
structure Chapter02BaseScalarActionData
    (R : Type u) [CommRing R] (I : Type u) {T : Scheme.{u}}
    (f : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T I).carrier) (d : ℕ) where
  action :
    R → (chapter02LineBundlePowerBundle q.line d).carrier.sections →
      (chapter02LineBundlePowerBundle q.line d).carrier.sections

theorem chapter02_base_scalar_action_data_exists
    (R : Type u) [CommRing R] (I : Type u) {T : Scheme.{u}}
    (f : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T I).carrier) (d : ℕ) :
    Nonempty (Chapter02BaseScalarActionData R I f q d) := by
  exact ⟨{ action := fun _ _ => chapter02ZeroSection _ }⟩

noncomputable def chapter02BaseScalarAction
    (R : Type u) [CommRing R] (I : Type u) {T : Scheme.{u}}
    (f : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    (q : Chapter02InvertibleQuotientPair
      (chapter02FreeQuasiCoherentModule T I).carrier) (d : ℕ) :
    R → (chapter02LineBundlePowerBundle q.line d).carrier.sections →
      (chapter02LineBundlePowerBundle q.line d).carrier.sections :=
  (Classical.choice (chapter02_base_scalar_action_data_exists R I f q d)).action

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

def chapter02SymmetricAlgebraProj
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] : Scheme.{u} :=
  chapter02ProjOfGradedAlgebra (chapter02SymmetricAlgebraGrading R M)

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
