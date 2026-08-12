import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Sheaves.LocallySurjective

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

/-!
The preceding chapters of Book 8 are not populated in this checkout.  This file
therefore keeps the chapter-facing interfaces small and canonical: evaluation is
the counit of the pullback/pushforward adjunction, generation is local
surjectivity of the corresponding sheaf map, and tensor products are obtained
from Mathlib's presheaf tensor product followed by sheafification.
-/

/- DEPENDENCY_GUESS: pinned Mathlib does not yet expose relative projective
bundles, their tautological `O(1)`, or the associated section-map API.  The
`Chapter04ProjectiveBundle` and witness structures below are the smallest
book-facing replacement; a later pass should identify them with the canonical
relative Proj construction from the preceding chapters. -/

/- DEPENDENCY_GUESS: Mathlib has pullback functors for module sheaves but no
canonical map on global sections of an arbitrary pulled-back module.  The
finite-section system below consequently records the restriction maps as data;
the later fixup pass should replace that field by the canonical map induced by
the pullback of `unitHomEquiv.symm`. -/

/- DEPENDENCY_GUESS: pinned Mathlib has no coherent cohomology object for
schemes.  `Chapter04CohomologyContext` is a deliberately neutral interface for
the two Serre-vanishing statements, not an assertion that an arbitrary family
of types is cohomology. -/

/- DEPENDENCY_GUESS: the additive and field-valued scalar structures on the
natural global-section type are not yet packaged through the scheme morphism
to `Spec K`; the finite section system therefore exposes both structures
explicitly. -/

/-! ### Evaluation and invertible sheaves -/

/-- A morphism of module sheaves is surjective in the sheaf-theoretic sense. -/
def chapter04SheafSurjective {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) : Prop :=
  TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf

theorem chapter04SheafSurjective_iff_stalkwise
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    chapter04SheafSurjective φ ↔
      ∀ x : X, Function.Surjective
        ((TopCat.Presheaf.stalkFunctor Ab x).map φ.mapPresheaf) := by
  sorry

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

/-- The underlying topological map of a constant morphism has one image point. -/
def chapter04UnderlyingConstant
    {X Y : Scheme.{u}} (g : Y ⟶ X) : Prop :=
  ∃ x : X, ∀ y : Y, g.base y = x

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
  projection_isProper : IsProper projection

/-- A relative projective-space witness for very ampleness. -/
structure Chapter04VeryAmpleWitness
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) where
  projectiveBundle : Chapter04ProjectiveBundle S
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
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ chapter04FiniteRelativeGenerationOn f L U

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
  chart_cover : ∀ x : X, ∃ i j, x ∈ (chart i j).locus

/-- Relative ampleness in the affine-open definition used in Chapter 4. -/
def chapter04Ample
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X) : Prop :=
  Nonempty (Chapter04AmpleWitness f L)

/-! ### Length-two subschemes and the field criterion -/

/-- The module-theoretic length of a scheme finite over a coefficient field. -/
noncomputable def chapter04SchemeLength
    (K : Type u) [Field K] (Z : Scheme.{u})
    (g : Z ⟶ AlgebraicGeometry.Spec (.of K)) : ℕ∞ :=
  letI := g.appTop.hom.toAlgebra
  letI : Module K Γ(Z, ⊤) :=
    Module.compHom _ (((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom)
  Module.length K Γ(Z, ⊤)

/-- A closed subscheme of length two in a scheme over a field. -/
structure Chapter04LengthTwoClosedSubscheme
    (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) where
  Z : Scheme.{u}
  inclusion : Z ⟶ X
  closed : IsClosedImmersion inclusion
  structureMap : Z ⟶ AlgebraicGeometry.Spec (.of K)
  over : inclusion ≫ f = structureMap
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
  finite : Module.Finite K I
  sectionMap : I →ₗ[K] L.sheaf.val.sections
  section_injective : Function.Injective sectionMap
  generates : Epi (L.sheaf.freeHomEquiv.symm (fun i => sectionMap i))
  restriction : ∀ Z : Chapter04LengthTwoClosedSubscheme K f,
    I → ((Scheme.Modules.pullback Z.inclusion).obj L.sheaf).val.sections

/-- The restriction-surjectivity form of separation of points and tangent directions. -/
def chapter04SeparatesLengthTwo
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of K)} {L : Chapter04LineBundle X}
    (V : Chapter04FiniteSectionSystem K f L) : Prop :=
  ∀ Z : Chapter04LengthTwoClosedSubscheme K f,
    Function.Surjective (V.restriction Z)

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

/-- A book-facing higher-cohomology interface, pending the project cohomology API. -/
structure Chapter04CohomologyContext (X : Scheme.{u}) where
  H : X.Modules → ℕ → Type u

def Chapter04CohomologyContext.Vanishes
    {X : Scheme.{u}} (C : Chapter04CohomologyContext X)
    (F : X.Modules) (i : ℕ) : Prop :=
  Subsingleton (C.H F i)

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
