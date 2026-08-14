import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Localization.Away.Basic
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section02SingleCoversAndAffineReduction

/-!
# Shared interfaces for Chapter 8

The chapter uses the canonical module-valued pseudofunctor on schemes and the
chosen-pullback form of categorical descent data.  The small wrappers below
keep the book vocabulary (fpqc, quasi-coherent, affine restriction, and
finite locally free) visible without duplicating Mathlib's constructions.
-/

namespace LastLib
namespace Book10FaithfullyFlatDescentInAlgebraicGeometry
namespace Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Bicategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/-- The fpqc hypotheses used in this chapter, inherited from the canonical
Chapter 2 definition. -/
abbrev Chapter08FpqcMorphism {T S : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Chapter02.IsFpqcMorphism p

/-- A family-level fpqc cover, retaining the canonical Chapter 2 family
interface and its finite-reduction condition. -/
structure Chapter08FpqcCoverFamily (S : Scheme.{u}) (ι : Type*) where
  family : Chapter02.SchemeFamily S ι
  fpqc : Chapter02.FpqcCoveringFamily family

abbrev Chapter08FpqcCoverFamily.source
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι) : ι → Scheme.{u} :=
  C.family.obj

abbrev Chapter08FpqcCoverFamily.map
    {S : Scheme.{u}} {ι : Type*} (C : Chapter08FpqcCoverFamily S ι) :
    ∀ i, C.source i ⟶ S :=
  C.family.map

/-- The base change of a cover map along a morphism `X ⟶ S`. -/
def chapter08BaseChange {X T S : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) : Scheme.{u} :=
  pullback f p

/-- The projection from the base-changed cover to `X`. -/
def chapter08BaseChangedCoverMap {X T S : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) :
    chapter08BaseChange f p ⟶ X :=
  pullback.fst f p

/-- The projection from the base-changed cover to `T`. -/
def chapter08BaseChangedCoverProjection {X T S : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) :
    chapter08BaseChange f p ⟶ T :=
  pullback.snd f p

/- LOCAL_DEPENDENCY_GUESS: the pinned morphism API has the individual
 permanence lemmas, but this book-facing bundled fpqc base-change bridge is
 not yet present in an earlier LastLib chapter. -/
theorem chapter08_baseChange_fpqc
    {X T S : Scheme.{u}} {f : X ⟶ S} {p : T ⟶ S}
    (hp : Chapter08FpqcMorphism p) :
    Chapter08FpqcMorphism (chapter08BaseChangedCoverMap f p) := by
  sorry

/-- A chosen pullback for two members of a covering family. -/
noncomputable def chapter08ChosenPullback
    {X₁ X₂ S : Scheme.{u}} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) :
    ChosenPullback f₁ f₂ where
  pullback := pullback f₁ f₂
  p₁ := pullback.fst f₁ f₂
  p₂ := pullback.snd f₁ f₂
  condition := pullback.condition
  isLimit := pullback.isLimit f₁ f₂

/-- Canonical threefold overlap choices built from nested pullbacks. -/
noncomputable def chapter08ChosenPullback₃
    {X₁ X₂ X₃ S : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) (f₃ : X₃ ⟶ S) :
    ChosenPullback₃ (chapter08ChosenPullback f₁ f₂)
      (chapter08ChosenPullback f₂ f₃) (chapter08ChosenPullback f₁ f₃) := by
  let h₁₂ := chapter08ChosenPullback f₁ f₂
  let h₂₃ := chapter08ChosenPullback f₂ f₃
  let h₁₃ := chapter08ChosenPullback f₁ f₃
  let h₂ := chapter08ChosenPullback h₁₂.p₂ h₂₃.p₁
  refine { chosenPullback := h₂
    p := h₂.p₁ ≫ h₁₂.p
    p₁ := h₂.p₁ ≫ h₁₂.p₁
    p₃ := h₂.p₂ ≫ h₂₃.p₂
    l := ?_ }
  refine ⟨h₁₃.isPullback.lift (h₂.p₁ ≫ h₁₂.p₁) (h₂.p₂ ≫ h₂₃.p₂) ?_, ?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
    · sorry

/-- The canonical pseudofunctor sending a scheme to its category of module
sheaves and a scheme map to pullback.  It is obtained from Mathlib's
adjunction-valued pseudofunctor by forgetting the right adjoints. -/
noncomputable def chapter08ModulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  (Bicategory.Adj.forget₁).comp AlgebraicGeometry.Scheme.Modules.pseudofunctor

/-- Choices of pairwise and triple overlaps for a family over a common base. -/
structure Chapter08PullbackChoices {S : Scheme.{u}} {ι : Type*}
    (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ S) where
  sq : ∀ i j, ChosenPullback (f i) (f j)
  sq₃ : ∀ (i j k : ι), ChosenPullback₃ (sq i j) (sq j k) (sq i k)

/-- The full category of module descent data for the chosen overlap system. -/
abbrev Chapter08ModuleDescentData {S : Scheme.{u}} {ι : Type*}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (choices : Chapter08PullbackChoices X f) :=
  (chapter08ModulesPseudofunctor).DescentData' choices.sq choices.sq₃

/-- The quasi-coherent modules on a scheme, as the canonical full subcategory. -/
abbrev Chapter08QuasiCoherentModules (S : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory

/-- The full subcategory of descent data whose local modules are
quasi-coherent. -/
abbrev Chapter08QuasiCoherentModuleDescentData
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f) :=
  (fun D : Chapter08ModuleDescentData choices =>
    ∀ i, (D.obj i).IsQuasicoherent).FullSubcategory

/-- The single-cover overlap choices used for the displayed `p₁^*` and
`p₂^*` comparison in the chapter. -/
noncomputable def chapter08SingleCoverChoices {T S : Scheme.{u}} (p : T ⟶ S) :
    Chapter08PullbackChoices (fun _ : Unit => T) (fun _ : Unit => p) where
  sq _ _ := chapter08ChosenPullback p p
  sq₃ _ _ _ := chapter08ChosenPullback₃ p p p

abbrev Chapter08SingleCoverDescentData {T S : Scheme.{u}} (p : T ⟶ S) :=
  Chapter08ModuleDescentData (chapter08SingleCoverChoices p)

abbrev Chapter08SingleCoverQuasiCoherentDescentData
    {T S : Scheme.{u}} (p : T ⟶ S) :=
  Chapter08QuasiCoherentModuleDescentData (chapter08SingleCoverChoices p)

/-- The overlap morphism `p₁^*F ⟶ p₂^*F` stored by a single-cover descent
datum.  The canonical `DescentData'` instance proves that it is invertible. -/
noncomputable def chapter08DescentTheta
    {T S : Scheme.{u}} {p : T ⟶ S} (D : Chapter08SingleCoverDescentData p) :=
  asIso (D.hom () ())

/-- The unit part of the descent condition. -/
def chapter08DescentUnitCondition
    {T S : Scheme.{u}} {p : T ⟶ S} (D : Chapter08SingleCoverDescentData p) :=
  D.pullHom'_hom_self ()

/-- The triple-overlap cocycle supplied by `DescentData'`. -/
def chapter08DescentCocycleCondition
    {T S : Scheme.{u}} {p : T ⟶ S} (D : Chapter08SingleCoverDescentData p) :=
  D.pullHom'_hom_comp () () ()

/-- Descent morphisms are determined by their component on every member of the
cover.  The single-member version is useful for full-faithfulness arguments. -/
theorem chapter08_descent_hom_ext
    {T S : Scheme.{u}} {p : T ⟶ S}
    {D E : Chapter08SingleCoverDescentData p} {φ ψ : D ⟶ E}
    (h : φ.hom () = ψ.hom ()) : φ = ψ := by
  sorry

/-!
## Affine interfaces

The following declarations make the affine-local construction explicit.  The
actual module descent theorem is represented by the canonical comonadic
extension-of-scalars result; the sheaf-level effectiveness bridge is stated in
the section that uses it.
-/

/-- A finite affine refinement of the base-changed cover over an affine open. -/
structure Chapter08FiniteAffineRefinement
    {T S : Scheme.{u}} (p : T ⟶ S) (U : S.Opens) where
  index : Type u
  finite : Finite index
  source : index → Scheme.{u}
  map : ∀ i, source i ⟶ pullback U.ι p
  affine : ∀ i, IsAffine (source i)
  flat : ∀ i, Flat (map i)
  quasiCompact : ∀ i, QuasiCompact (map i)
  coordinateRing : ∀ i, CommRingCat.{u}
  source_isSpec : ∀ i, Nonempty (source i ≅ Scheme.Spec (coordinateRing i))
  jointlySurjective : ∀ x : pullback U.ι p, ∃ (i : index) (y : source i), map i y = x

/-- The product ring used to combine a finite affine refinement. -/
def chapter08ProductRing {ι : Type*} (B : ι → CommRingCat.{u}) : CommRingCat.{u} :=
  CommRingCat.of (∀ i, B i)

/-- A faithfully flat product algebra `A ⟶ ∏ Bᵢ`. -/
structure Chapter08FaithfullyFlatProductAlgebra
    (A : CommRingCat.{u}) {ι : Type*} (B : ι → CommRingCat.{u}) where
  finite : Finite ι
  algebraMap : A ⟶ chapter08ProductRing B
  faithfullyFlat : algebraMap.hom.FaithfullyFlat

/-- The ring-level effectivity witness used on an affine open: the compatible
module descent datum produces an `A`-module whose product-base-change is the
module upstairs. -/
structure Chapter08AffineModuleDescentWitness
    (A : CommRingCat.{u}) {ι : Type*} (B : ι → CommRingCat.{u})
    (P : Chapter08FaithfullyFlatProductAlgebra A B) where
  descended : ModuleCat A
  upstairs : ModuleCat (chapter08ProductRing B)
  comparison :
    (ModuleCat.extendScalars P.algebraMap.hom).obj descended ≅ upstairs

/-- Pinned Mathlib's algebraic input for affine descent. -/
theorem chapter08_affine_extension_is_comonadic
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.FaithfullyFlat) :
    ComonadicLeftAdjoint (ModuleCat.extendScalars f) :=
  ModuleCat.comonadicExtendScalars hf

/-- The sheaf associated to an affine module by the canonical tilde
construction. -/
def chapter08AffineSheafOfModule {R : CommRingCat.{u}} (M : ModuleCat R) :
    (Scheme.Spec R).Modules :=
  Scheme.Modules.tilde M

/-- The affine tilde equivalence, used to identify the descended module on an
affine with its quasi-coherent sheaf. -/
noncomputable def chapter08AffineQuasiCoherentEquivalence (R : CommRingCat.{u}) :
    ModuleCat R ≌ Chapter08QuasiCoherentModules (Scheme.Spec R) :=
  Scheme.Modules.tildeEquiv R

/-- The basic open `D(f)` on an affine scheme. -/
def chapter08AffineBasicOpen {R : CommRingCat.{u}} (f : R) : (Scheme.Spec R).Opens :=
  PrimeSpectrum.basicOpen f

/-- The module-theoretic localization appearing as restriction to `D(f)`. -/
def chapter08LocalizedModule {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    ModuleCat (Localization.Away f) :=
  (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj M

/-- A named comparison interface for the affine restriction calculation. -/
structure Chapter08AffineRestrictionComparison
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) where
  restricted : ModuleCat (Localization.Away f)
  comparison : restricted ≅ chapter08LocalizedModule M f

/-- The restriction module is, by definition, extension of scalars to the
localization; this is the scalar-extension normalization used throughout the
chapter. -/
def chapter08AffineRestrictionComparison.canonical
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    Chapter08AffineRestrictionComparison M f where
  restricted := chapter08LocalizedModule M f
  comparison := Iso.refl _

/- A finite affine open cover written directly as maps from affine schemes. -/
structure Chapter08AffineOpenCover (S : Scheme.{u}) where
  index : Type u
  coordinateRing : index → CommRingCat.{u}
  map : ∀ i, Scheme.Spec (coordinateRing i) ⟶ S
  isOpenImmersion : ∀ i, IsOpenImmersion (map i)
  jointlySurjective : ∀ s : S, ∃ (i : index) (x : Scheme.Spec (coordinateRing i)), map i x = s

end
end Chapter08
end Book10FaithfullyFlatDescentInAlgebraicGeometry
end LastLib
