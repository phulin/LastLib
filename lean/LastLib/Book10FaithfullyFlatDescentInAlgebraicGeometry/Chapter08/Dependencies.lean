import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.ResidueField
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
  change Flat (pullback.fst f p) ∧ QuasiCompact (pullback.fst f p) ∧
    Surjective (pullback.fst f p)
  exact ⟨by let : Flat p := hp.1; infer_instance,
    by let : QuasiCompact p := hp.2.1; infer_instance,
    by let : Surjective p := hp.2.2; infer_instance⟩

/-- A chosen pullback for two members of a covering family. -/
noncomputable def chapter08ChosenPullback
    {X₁ X₂ S : Scheme.{u}} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) :
    ChosenPullback f₁ f₂ where
  pullback := pullback f₁ f₂
  p₁ := pullback.fst f₁ f₂
  p₂ := pullback.snd f₁ f₂
  condition := pullback.condition
  isLimit := PullbackCone.mkSelfIsLimit (pullback.isLimit f₁ f₂)

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
  refine { chosenPullback := h₂, p := h₂.p₁ ≫ h₁₂.p, p₁ := h₂.p₁ ≫ h₁₂.p₁, p₃ := h₂.p₂ ≫ h₂₃.p₂, l := { f := h₁₃.isPullback.lift (h₂.p₁ ≫ h₁₂.p₁) (h₂.p₂ ≫ h₂₃.p₂) (by rw [Category.assoc, Category.assoc, h₁₂.condition, h₂.condition_assoc, h₂₃.condition]), f_p₁ := by apply h₁₃.isPullback.lift_fst, f_p₂ := by apply h₁₃.isPullback.lift_snd, f_p := by rw [← h₁₃.hp₁, ← Category.assoc, h₁₃.isPullback.lift_fst, Category.assoc, h₁₂.hp₁] }, hp₁ := by rfl, hp₃ := by rfl }

/-- The canonical pseudofunctor sending a scheme to its category of module
sheaves and a scheme map to pullback.  It is obtained from Mathlib's
adjunction-valued pseudofunctor by forgetting the right adjoints. -/
noncomputable def chapter08ModulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  AlgebraicGeometry.Scheme.Modules.pseudofunctor.comp (Bicategory.Adj.forget₁)

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

/-- Pullback of a quasi-coherent module along an arbitrary scheme morphism is
quasi-coherent.  The pinned Mathlib snapshot exposes the affine and open
immersion cases, but not this general scheme-level bridge. -/
theorem chapter08_pullback_is_quasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Chapter08QuasiCoherentModules S) :
    ((Scheme.Modules.pullback f).obj M.obj).IsQuasicoherent := by
  sorry

/-- The direct image of the structure sheaf is quasi-coherent for a
quasi-compact, quasi-separated morphism.  This is the shared interface for
relative global functions and does not require the morphism to be flat. -/
theorem chapter08_pushforward_structure_sheaf_is_quasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent := by
  sorry

/-- The relative global-functions module attached to a quasi-compact,
quasi-separated morphism.  Naming this object here gives later chapters a
stable interface without having to repeat the pushforward expression. -/
abbrev chapter08StructureSheafPushforward
    {X S : Scheme.{u}} (f : X ⟶ S) : S.Modules :=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)

/-- The structure-sheaf pushforward after base change of its morphism. -/
abbrev chapter08StructureSheafPushforwardBaseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : T.Modules :=
  (Scheme.Modules.pushforward (pullback.snd f g)).obj
    (SheafOfModules.unit (pullback f g).ringCatSheaf)

/-- A sheaf-level flat base-change comparison for relative global functions.
The restriction field is part of the interface: an objectwise isomorphism is
not enough for later affine-envelope constructions. -/
structure Chapter08StructureSheafFlatBaseChangeData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] where
  comparison :
    (Scheme.Modules.pullback g).obj (chapter08StructureSheafPushforward f) ≅
      chapter08StructureSheafPushforwardBaseChange f g
  comparison_restriction :
    ∀ {U V : T.Opens} (i : U ⟶ V),
      ((Scheme.Modules.pullback g).obj (chapter08StructureSheafPushforward f)).val.map i.op ≫
        (ModuleCat.restrictScalars
          (RingCat.Hom.hom (T.ringCatSheaf.obj.map i.op))).map
          (comparison.hom.val.app (.op U)) =
      comparison.hom.val.app (.op V) ≫
        (chapter08StructureSheafPushforwardBaseChange f g).val.map i.op

/-- Flat base change for the pushforward of the structure sheaf, with its
restriction naturality.  The proof is supplied by the affine-section
base-change theorem in the eventual implementation; this declaration is the
shared book-facing interface. -/
theorem chapter08_pushforward_structure_sheaf_flat_base_change_exists
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] :
    Nonempty (Chapter08StructureSheafFlatBaseChangeData f g) := by
  sorry

/-- The chosen structure-sheaf flat-base-change comparison. -/
noncomputable def chapter08_pushforward_structure_sheaf_flat_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] :
    (Scheme.Modules.pullback g).obj (chapter08StructureSheafPushforward f) ≅
      chapter08StructureSheafPushforwardBaseChange f g :=
  (Classical.choice
    (chapter08_pushforward_structure_sheaf_flat_base_change_exists f g)).comparison

/-- The full subcategory of descent data whose local modules are
quasi-coherent. -/
abbrev Chapter08QuasiCoherentModuleDescentData
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f) :=
  ObjectProperty.FullSubcategory (fun D : Chapter08ModuleDescentData choices =>
    ∀ i, SheafOfModules.isQuasicoherent (X i).ringCatSheaf
      (show (X i).Modules from D.obj i))

/- The canonical module datum is obtained from Mathlib's unrestricted descent
   datum for the pullbacks and then transported to the chosen overlaps. -/
noncomputable def chapter08CanonicalModuleDescentData
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f)
    (M : Chapter08QuasiCoherentModules S) :
    Chapter08ModuleDescentData choices :=
  Pseudofunctor.DescentData'.ofDescentData choices.sq choices.sq₃
    (((chapter08ModulesPseudofunctor).toDescentData f).obj M.obj)

/- The local quasi-coherence proof is kept as the one affine/sheaf bridge
   required to place the canonical datum in the chapter's full subcategory. -/
noncomputable def chapter08CanonicalQuasiCoherentDescentDataBase
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f)
    (M : Chapter08QuasiCoherentModules S) :
    Chapter08QuasiCoherentModuleDescentData choices := by
  refine ⟨chapter08CanonicalModuleDescentData choices M, ?_⟩
  intro i
  exact chapter08_pullback_is_quasicoherent (f i) M

/- This package keeps the canonical pullback datum, its component comparisons,
   and its functorial maps in one interface.  The datum is fixed by the
   canonical construction above, rather than being an arbitrary descent
   object with only componentwise pullback isomorphisms. -/
structure Chapter08CanonicalQuasiCoherentDescentPackage
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f) where
  component : ∀ (M : Chapter08QuasiCoherentModules S) (i : ι),
    (chapter08CanonicalQuasiCoherentDescentDataBase choices M).obj.obj i ≅
      (Scheme.Modules.pullback (f i)).obj M.obj
  map : ∀ {M N : Chapter08QuasiCoherentModules S}, (M ⟶ N) →
    (chapter08CanonicalQuasiCoherentDescentDataBase choices M ⟶
      chapter08CanonicalQuasiCoherentDescentDataBase choices N)
  map_component : ∀ {M N : Chapter08QuasiCoherentModules S}
    (φ : M ⟶ N) (i : ι),
    (component M i).hom ≫ (Scheme.Modules.pullback (f i)).map φ.hom =
      (map φ).hom.hom i ≫ (component N i).hom
  map_id : ∀ (M : Chapter08QuasiCoherentModules S),
    map (𝟙 M) =
      𝟙 (chapter08CanonicalQuasiCoherentDescentDataBase choices M)
  map_comp : ∀ {M N P : Chapter08QuasiCoherentModules S}
    (φ : M ⟶ N) (ψ : N ⟶ P),
    map (φ ≫ ψ) = map φ ≫ map ψ

/- The existence of the package is the single construction interface used by
   the chapter.  Its fields are the effectivity comparison and the naturality
   data that the later categorical functor needs. -/
noncomputable def chapter08CanonicalQuasiCoherentDescentPackage
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f) :
    Chapter08CanonicalQuasiCoherentDescentPackage choices := by
  refine
    { component := ?_
      map := ?_
      map_component := ?_
      map_id := ?_
      map_comp := ?_ }
  · intro M i
    exact Iso.refl _
  · intro M N φ
    exact ObjectProperty.homMk
      ((Pseudofunctor.DescentData'.fromDescentDataFunctor chapter08ModulesPseudofunctor
          choices.sq choices.sq₃).map
        (((chapter08ModulesPseudofunctor).toDescentData f).map φ.hom))
  · intro M N φ i
    rfl
  · intro M
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.id_hom]
    dsimp [Pseudofunctor.DescentData'.fromDescentDataFunctor]
    apply Pseudofunctor.DescentData'.hom_ext
    intro i
    exact congrArg (fun q => q.hom i)
      ((chapter08ModulesPseudofunctor.toDescentData f).map_id M.obj)
  · intro M N P φ ψ
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom]
    dsimp [ObjectProperty.homMk,
      Pseudofunctor.DescentData'.fromDescentDataFunctor]
    apply Pseudofunctor.DescentData'.hom_ext
    intro i
    exact congrArg (fun q => q.hom i)
      ((chapter08ModulesPseudofunctor.toDescentData f).map_comp φ.hom ψ.hom)

/-- The canonical quasi-coherent descent datum obtained by pulling a global
module sheaf back to every member of a chosen cover.  Keeping this datum
explicit is useful when a gluing comparison must be compatible with the
overlap maps, rather than merely giving unrelated local isomorphisms. -/
noncomputable def chapter08CanonicalQuasiCoherentDescentData
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f)
    (M : Chapter08QuasiCoherentModules S) :
    Chapter08QuasiCoherentModuleDescentData choices := by
  exact chapter08CanonicalQuasiCoherentDescentDataBase choices M

/-- The local component of the canonical datum is the pullback module, up to
the canonical comparison supplied by its construction. -/
theorem chapter08_canonical_quasiCoherent_descent_component
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f)
    (M : Chapter08QuasiCoherentModules S) (i : ι) :
    Nonempty
      ((chapter08CanonicalQuasiCoherentDescentData choices M).obj.obj i ≅
        (Scheme.Modules.pullback (f i)).obj M.obj) := by
  exact ⟨(chapter08CanonicalQuasiCoherentDescentPackage choices).component M i⟩

/- The componentwise pullback maps form the canonical morphism between the
   corresponding descent data.  The overlap equation is the naturality of
   pullback, retained here as the one compatibility field required by the
   descent category. -/
noncomputable def chapter08CanonicalQuasiCoherentDescentMap
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f)
    {M N : Chapter08QuasiCoherentModules S} (φ : M ⟶ N) :
    chapter08CanonicalQuasiCoherentDescentData choices M ⟶
      chapter08CanonicalQuasiCoherentDescentData choices N := by
  exact (chapter08CanonicalQuasiCoherentDescentPackage choices).map φ

theorem chapter08CanonicalQuasiCoherentDescentMap_id
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f)
    (M : Chapter08QuasiCoherentModules S) :
    chapter08CanonicalQuasiCoherentDescentMap choices (𝟙 M) =
      𝟙 (chapter08CanonicalQuasiCoherentDescentData choices M) := by
  exact (chapter08CanonicalQuasiCoherentDescentPackage choices).map_id M

theorem chapter08CanonicalQuasiCoherentDescentMap_comp
    {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} (choices : Chapter08PullbackChoices X f)
    {M N P : Chapter08QuasiCoherentModules S}
    (φ : M ⟶ N) (ψ : N ⟶ P) :
    chapter08CanonicalQuasiCoherentDescentMap choices (φ ≫ ψ) =
      chapter08CanonicalQuasiCoherentDescentMap choices φ ≫
        chapter08CanonicalQuasiCoherentDescentMap choices ψ := by
  exact (chapter08CanonicalQuasiCoherentDescentPackage choices).map_comp φ ψ

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
abbrev chapter08DescentUnitCondition
    {T S : Scheme.{u}} {p : T ⟶ S} (D : Chapter08SingleCoverDescentData p) :=
  D.pullHom'_hom_self ()

/-- The triple-overlap cocycle supplied by `DescentData'`. -/
abbrev chapter08DescentCocycleCondition
    {T S : Scheme.{u}} {p : T ⟶ S} (D : Chapter08SingleCoverDescentData p) :=
  D.pullHom'_hom_comp () () ()

/-- Descent morphisms are determined by their component on every member of the
cover.  The single-member version is useful for full-faithfulness arguments. -/
theorem chapter08_descent_hom_ext
    {T S : Scheme.{u}} {p : T ⟶ S}
    {D E : Chapter08SingleCoverDescentData p} {φ ψ : D ⟶ E}
    (h : φ.hom () = ψ.hom ()) : φ = ψ := by
  apply Pseudofunctor.DescentData'.hom_ext
  exact fun i => by cases i; exact h

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
  isOpenImmersion : ∀ i, IsOpenImmersion (map i)
  coordinateRing : index → CommRingCat.{u}
  source_isSpec : ∀ i, Nonempty (source i ≅ Spec (coordinateRing i))
  /-- The selected affine pieces cover the affine base through the projection
  from the base-changed cover.  They need not cover all of the (possibly
  non-quasi-compact) base-changed source. -/
  jointlySurjective : ∀ x : U.toScheme,
    ∃ (i : index) (y : source i), pullback.fst U.ι p (map i y) = x

/-- The product ring used to combine a finite affine refinement. -/
def chapter08ProductRing {ι : Type u} (B : ι → CommRingCat.{u}) : CommRingCat.{u} :=
  CommRingCat.of (∀ i, B i)

/-- A faithfully flat product algebra `A ⟶ ∏ Bᵢ`. -/
structure Chapter08FaithfullyFlatProductAlgebra
    (A : CommRingCat.{u}) {ι : Type u} (B : ι → CommRingCat.{u}) where
  finite : Finite ι
  algebraMap : A ⟶ chapter08ProductRing B
  faithfullyFlat : algebraMap.hom.FaithfullyFlat

/-- The ring-level effectivity witness used on an affine open: the compatible
module descent datum produces an `A`-module whose product-base-change is the
module upstairs. -/
structure Chapter08AffineModuleDescentWitness
    (A : CommRingCat.{u}) {ι : Type u} (B : ι → CommRingCat.{u})
    (P : Chapter08FaithfullyFlatProductAlgebra A B) where
  descended : ModuleCat A
  upstairs : ModuleCat (chapter08ProductRing B)
  descent :
    Chapter08SingleCoverQuasiCoherentDescentData
      (Spec.map P.algebraMap)
  upstairsComparison :
    Nonempty (tilde upstairs ≅ (descent.obj).obj ())
  descendedComparison :
    Nonempty
      (chapter08CanonicalQuasiCoherentDescentData
          (chapter08SingleCoverChoices
            (Spec.map P.algebraMap))
          ⟨tilde descended, inferInstance⟩ ≅ descent)

/- The module comparison is a consequence of the two compatible affine tilde
   comparisons, rather than independent data.  Keeping it as a derived
   interface prevents an arbitrary isomorphism from being mistaken for the
   comparison supplied by descent. -/
theorem chapter08_affine_module_descent_comparison
    {A : CommRingCat.{u}} {ι : Type u} {B : ι → CommRingCat.{u}}
    {P : Chapter08FaithfullyFlatProductAlgebra A B}
    (W : Chapter08AffineModuleDescentWitness A B P) :
    Nonempty ((ModuleCat.extendScalars P.algebraMap.hom).obj W.descended ≅ W.upstairs) := by
  sorry

/-- Pinned Mathlib's algebraic input for affine descent. -/
@[instance_reducible]
noncomputable def chapter08_affine_extension_is_comonadic
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.FaithfullyFlat) :
    ComonadicLeftAdjoint (ModuleCat.extendScalars f) :=
  comonadicExtendScalars hf

/-- The sheaf associated to an affine module by the canonical tilde
construction. -/
def chapter08AffineSheafOfModule {R : CommRingCat.{u}} (M : ModuleCat R) :
    (Spec R).Modules :=
  tilde M

/-- The affine tilde equivalence, used to identify the descended module on an
affine with its quasi-coherent sheaf. -/
noncomputable def chapter08AffineQuasiCoherentEquivalence (R : CommRingCat.{u}) :
    ModuleCat R ≌ Chapter08QuasiCoherentModules (Spec R) :=
  tildeEquiv (R := R)

/-- Natural affine base change for the tilde construction.  This is the
functorial form of the usual statement that pullback along `Spec.map φ`
corresponds to extension of scalars along `φ`. -/
noncomputable def chapter08AffineTildeBaseChangeIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S := by
  sorry

/-- The objectwise affine tilde base-change comparison. -/
noncomputable def chapter08AffineTildeBaseChangeIsoAt
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  (chapter08AffineTildeBaseChangeIso φ).app M

/-- The basic open `D(f)` on an affine scheme. -/
def chapter08AffineBasicOpen {R : CommRingCat.{u}} (f : R) : (Spec R).Opens :=
  PrimeSpectrum.basicOpen f

/-- The module-theoretic localization appearing as restriction to `D(f)`. -/
def chapter08LocalizedModule {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    ModuleCat (Localization.Away f) :=
  (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj M

/-- Natural restriction of an affine tilde sheaf to a basic open.  The target
is written through the canonical affine identification of `D(f)` with the
spectrum of the localization, so the comparison is usable under further
pullback and restriction. -/
noncomputable def chapter08AffineTildeBasicOpenRestrictionIso
    {R : CommRingCat.{u}} (f : R) :
    tilde.functor R ⋙
        Scheme.Modules.pullback (chapter08AffineBasicOpen f).ι ≅
      ModuleCat.extendScalars (algebraMap R (Localization.Away f)) ⋙
        tilde.functor (CommRingCat.of (Localization.Away f)) ⋙
          Scheme.Modules.pullback (basicOpenIsoSpecAway f).hom := by
  sorry

/-- The objectwise basic-open restriction/localization comparison. -/
noncomputable def chapter08AffineTildeBasicOpenRestrictionIsoAt
    {R : CommRingCat.{u}} (f : R) (M : ModuleCat R) :
    (Scheme.Modules.pullback (chapter08AffineBasicOpen f).ι).obj (tilde M) ≅
      (Scheme.Modules.pullback (basicOpenIsoSpecAway f).hom).obj
        (tilde (chapter08LocalizedModule M f)) := by
  exact (chapter08AffineTildeBasicOpenRestrictionIso f).app M

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

/-- The actual sheaf restriction of an affine tilde module to `D(f)`, together
with the affine chart identifying it with the localized module.  The older
module-only comparison above is only a normalization; this interface records
the geometric restriction used in the affine-local construction. -/
structure Chapter08AffineRestrictionSheafComparison
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) where
  localizationIso : (chapter08AffineBasicOpen f).toScheme ≅
    Spec (CommRingCat.of (Localization.Away f))
  /-- The chosen isomorphism is the canonical localization chart, not merely
  an unrelated isomorphism of schemes. -/
  localizationIso_commutes :
    localizationIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) =
      (chapter08AffineBasicOpen f).ι
  comparison :
    (Scheme.Modules.pullback (chapter08AffineBasicOpen f).ι).obj
        (chapter08AffineSheafOfModule M) ≅
      (Scheme.Modules.pullback localizationIso.hom).obj
        (chapter08AffineSheafOfModule
          (chapter08LocalizedModule M f))

/-- The standard affine restriction/localization comparison. -/
theorem chapter08_affine_restriction_sheaf_comparison
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    Nonempty (Chapter08AffineRestrictionSheafComparison M f) := by
  exact ⟨{
    localizationIso := basicOpenIsoSpecAway f
    localizationIso_commutes := basicOpenIsoSpecAway_hom_SpecMap f
    comparison := chapter08AffineTildeBasicOpenRestrictionIsoAt f M
  }⟩

/- An affine open cover written directly as maps from affine schemes. -/
structure Chapter08AffineOpenCover (S : Scheme.{u}) where
  index : Type u
  finite : Finite index
  coordinateRing : index → CommRingCat.{u}
  map : ∀ i, Spec (coordinateRing i) ⟶ S
  isOpenImmersion : ∀ i, IsOpenImmersion (map i)
  jointlySurjective : ∀ s : S, ∃ (i : index) (x : Spec (coordinateRing i)), map i x = s

end
end Chapter08
end Book10FaithfullyFlatDescentInAlgebraicGeometry
end LastLib
