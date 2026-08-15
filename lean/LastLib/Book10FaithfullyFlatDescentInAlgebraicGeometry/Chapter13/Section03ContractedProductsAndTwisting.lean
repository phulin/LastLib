import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13.Section01TheTorsorIdentity
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13.Section02LocalTrivialityAndEffectivity

/-!
# 13.3 Contracted products and twisting

The quotient is represented by its effective descent presentation.  The local model and its
pullback comparison are fields of the resulting object, so the statement that the twist becomes
`X_P` is available independently of the existence proof.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry MonObj

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13

noncomputable section

/-- The right action on `P × X` given by `(p,x)·g = (pg,g⁻¹x)`. -/
noncomputable def chapter13ContractedProductRightAction
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    {P : Chapter13SchemeOver S} {X : Chapter13SchemeOver S}
    (Paction : Chapter13RightAction G P) (Xaction : Chapter13LeftAction G X) :
    Chapter13RightAction G (P ⊗ X) where
  act :=
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst (P ⊗ X) G.X ≫
            CartesianMonoidalCategory.fst P X)
          (CartesianMonoidalCategory.snd (P ⊗ X) G.X) ≫ Paction.act)
      (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.snd (P ⊗ X) G.X ≫ GrpObj.inv (X := G.X))
          (CartesianMonoidalCategory.fst (P ⊗ X) G.X ≫
            CartesianMonoidalCategory.snd P X) ≫ Xaction.act)
  one_act := by sorry
  mul_act := by sorry

def chapter13ContractedProductInvariantMap
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    {P : Chapter13FpqcTorsor G} {X : Chapter13SchemeOver S}
    (Xaction : Chapter13LeftAction G X)
    {Y : Chapter13SchemeOver S} (f : P.carrier ⊗ X ⟶ Y) : Prop :=
  (chapter13ContractedProductRightAction P.action Xaction).act ≫ f =
    CartesianMonoidalCategory.fst _ _ ≫ f

/-- An effective descent presentation of the contracted product. -/
structure Chapter13ContractedProductData
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X) where
  carrier : Chapter13SchemeOver S
  pullback_iso :
    (Over.pullback P.carrier.hom).obj carrier ≅
      (Over.pullback P.carrier.hom).obj X
  quotient_map : P.carrier ⊗ X ⟶ carrier
  quotient_invariant :
    chapter13ContractedProductInvariantMap Xaction quotient_map
  universal_property :
    ∀ {Y : Chapter13SchemeOver S} (f : P.carrier ⊗ X ⟶ Y),
      chapter13ContractedProductInvariantMap Xaction f →
        ∃! q : carrier ⟶ Y, quotient_map ≫ q = f

theorem chapter13_contractedProduct_exists
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X) :
    Nonempty (Chapter13ContractedProductData P X Xaction) := by
  sorry

noncomputable def chapter13ContractedProduct
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X) :
    Chapter13ContractedProductData P X Xaction :=
  Classical.choice (chapter13_contractedProduct_exists P X Xaction)

noncomputable def chapter13_contractedProduct_becomes_local_model
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X) :
    (Over.pullback P.carrier.hom).obj
        (chapter13ContractedProduct P X Xaction).carrier ≅
      (Over.pullback P.carrier.hom).obj X :=
  (chapter13ContractedProduct P X Xaction).pullback_iso

theorem chapter13_contractedProduct_is_universal_quotient
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X)
    {Y : Chapter13SchemeOver S} (f : P.carrier ⊗ X ⟶ Y)
    (hf : chapter13ContractedProductInvariantMap Xaction f) :
    ∃! q : (chapter13ContractedProduct P X Xaction).carrier ⟶ Y,
      (chapter13ContractedProduct P X Xaction).quotient_map ≫ q = f :=
  (chapter13ContractedProduct P X Xaction).universal_property f hf

theorem chapter13_contractedProduct_isAffine
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X)
    (hX : IsAffineHom X.hom) :
    IsAffineHom (chapter13ContractedProduct P X Xaction).carrier.hom := by
  sorry

theorem chapter13_contractedProduct_isFinite
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X)
    (hX : IsFinite X.hom) :
    IsFinite (chapter13ContractedProduct P X Xaction).carrier.hom := by
  sorry

theorem chapter13_contractedProduct_isSmooth
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X)
    (hX : Smooth X.hom) :
    Smooth (chapter13ContractedProduct P X Xaction).carrier.hom := by
  sorry

theorem chapter13_contractedProduct_isProper
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X)
    (hX : IsProper X.hom) :
    IsProper (chapter13ContractedProduct P X Xaction).carrier.hom := by
  sorry

theorem chapter13_contractedProduct_isFiniteLocallyFree
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X)
    (hX : Chapter13FiniteLocallyFree X.hom) :
    Chapter13FiniteLocallyFree
      (chapter13ContractedProduct P X Xaction).carrier.hom := by
  sorry

/-! ### Representations and associated bundles -/

/- Base change is part of a representation: the action on a pulled-back
module is identified with the action of the pulled-back group-valued point. -/
structure Chapter13SheafRepresentationBaseChange
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (sheaf : S.Modules)
    (action : ∀ {T : Scheme.{u}} (t : T ⟶ S) (_g : Over.mk t ⟶ G.X),
      (Scheme.Modules.pullback t).obj sheaf ≅
        (Scheme.Modules.pullback t).obj sheaf) where
  point : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T),
    (Over.mk t ⟶ G.X) → (Over.mk (u ≫ t) ⟶ G.X)
  /-- Base change acts on points by precomposition, not by an unrelated choice. -/
  point_is_pullback : ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T)
      (g : Over.mk t ⟶ G.X),
    point t u g = Over.homMk u ≫ g
  action_naturality :
    ∀ {T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T)
      (g : Over.mk t ⟶ G.X),
      (chapter04PullbackCompositionIso u t sheaf).hom ≫
          (Scheme.Modules.pullback u).map (action t g).hom =
        (action (u ≫ t) (point t u g)).hom ≫
          (chapter04PullbackCompositionIso u t sheaf).hom

/- A sheaf representation is expressed by its functor-of-points action.  This avoids inventing a
Hopf-algebra presentation for a non-affine group scheme while retaining the action, identity, and
multiplication interfaces needed by associated bundles. -/
structure Chapter13SheafRepresentation
    {S : Scheme.{u}} (G : Chapter13GroupScheme S) where
  sheaf : S.Modules
  finiteLocallyFree : Chapter13FiniteLocallyFreeSheaf S
  sheaf_eq : finiteLocallyFree.sheaf = sheaf
  action : ∀ {T : Scheme.{u}} (t : T ⟶ S) (_g : Over.mk t ⟶ G.X),
    (Scheme.Modules.pullback t).obj sheaf ≅
      (Scheme.Modules.pullback t).obj sheaf
  action_one : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    action t (chapter13GroupSectionOne G (Over.mk t)) = Iso.refl _
  action_mul : ∀ {T : Scheme.{u}} (t : T ⟶ S)
    (g h : Over.mk t ⟶ G.X),
    action t (chapter13GroupSectionMul G g h) = action t h ≪≫ action t g
  base_change : Chapter13SheafRepresentationBaseChange sheaf action

theorem chapter13_sheafTensor_pullback_nonempty
    {S T : Scheme.{u}} (t : T ⟶ S) (M N : S.Modules) :
    Nonempty
      (chapter01SheafTensor ((Scheme.Modules.pullback t).obj M)
        ((Scheme.Modules.pullback t).obj N) ≅
        (Scheme.Modules.pullback t).obj (chapter01SheafTensor M N)) := by
  sorry

/- Pullback of quasi-coherent tensor products is canonical only up to the
   usual comparison isomorphism.  The coherence field records the
   composition compatibility needed by the base-change part of a tensor
   representation; an unrelated choice of comparison at each morphism would
   not suffice. -/
structure Chapter13SheafTensorPullbackSystem (S : Scheme.{u}) where
  iso : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules),
    chapter01SheafTensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) ≅
      (Scheme.Modules.pullback f).obj (chapter01SheafTensor M N)
  composition : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (M N : Z.Modules),
      (iso (f ≫ g) M N).hom =
        chapter01SheafTensorMap
            (chapter04PullbackCompositionIso f g M).hom
            (chapter04PullbackCompositionIso f g N).hom ≫
          (iso f ((Scheme.Modules.pullback g).obj M)
            ((Scheme.Modules.pullback g).obj N)).hom ≫
          (Scheme.Modules.pullback f).map
            (iso g M N).hom ≫
          (chapter04PullbackCompositionIso f g
            (chapter01SheafTensor M N)).inv

theorem chapter13_sheafTensorPullbackSystem_nonempty :
    ∀ {S : Scheme.{u}}, Nonempty (Chapter13SheafTensorPullbackSystem S) := by
  sorry

noncomputable def chapter13SheafTensorPullbackSystem :
    ∀ {S : Scheme.{u}}, Chapter13SheafTensorPullbackSystem S := by
  intro S
  exact Classical.choice (chapter13_sheafTensorPullbackSystem_nonempty (S := S))

noncomputable def chapter13SheafTensorPullbackIso
    {S T : Scheme.{u}} (t : T ⟶ S) (M N : S.Modules) :
    chapter01SheafTensor ((Scheme.Modules.pullback t).obj M)
        ((Scheme.Modules.pullback t).obj N) ≅
      (Scheme.Modules.pullback t).obj (chapter01SheafTensor M N) :=
  (chapter13SheafTensorPullbackSystem (S := S)).iso t M N

/-! ### Coherent module descent on a cover -/

/- The representation descent comparison below is not merely an arbitrary isomorphism on the
   double overlap.  The following all-test formulation records the normalization, cocycle, and
   pullback coherence that make it a genuine module descent datum. -/
noncomputable def chapter13ModuleBaseChangeCompIso
    {S T U : Scheme.{u}} (t : T ⟶ S) (u : U ⟶ T) (M : S.Modules) :
    (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback t).obj M) ≅
      (Scheme.Modules.pullback (u ≫ t)).obj M :=
  (chapter04PullbackCompositionIso u t M).symm

structure Chapter13ModuleDescentDatum
    {S T : Scheme.{u}} (t : T ⟶ S) where
  upstairs : T.Modules
  compare {U : Scheme.{u}} (q₁ q₂ : U ⟶ T) (h : q₁ ≫ t = q₂ ≫ t) :
    (Scheme.Modules.pullback q₁).obj upstairs ≅
      (Scheme.Modules.pullback q₂).obj upstairs
  compare_self {U : Scheme.{u}} (q : U ⟶ T) (h : q ≫ t = q ≫ t) :
    compare q q h = Iso.refl _
  compare_comp {U : Scheme.{u}} (q₁ q₂ q₃ : U ⟶ T)
      (h₁₂ : q₁ ≫ t = q₂ ≫ t) (h₂₃ : q₂ ≫ t = q₃ ≫ t)
      (h₁₃ : q₁ ≫ t = q₃ ≫ t) :
      (compare q₁ q₂ h₁₂).hom ≫ (compare q₂ q₃ h₂₃).hom =
        (compare q₁ q₃ h₁₃).hom
  compare_pull {U V : Scheme.{u}} (r : V ⟶ U) (q₁ q₂ : U ⟶ T)
      (h : q₁ ≫ t = q₂ ≫ t)
      (h' : (r ≫ q₁) ≫ t = (r ≫ q₂) ≫ t) :
    (Scheme.Modules.pullback r).map (compare q₁ q₂ h).hom =
      (chapter13ModuleBaseChangeCompIso q₁ r upstairs).hom ≫
        (compare (r ≫ q₁) (r ≫ q₂) h').hom ≫
          (chapter13ModuleBaseChangeCompIso q₂ r upstairs).inv

noncomputable def chapter13ModuleBaseChangeComparison
    {S T U : Scheme.{u}} (t : T ⟶ S) (M : S.Modules)
    (q₁ q₂ : U ⟶ T) (h : q₁ ≫ t = q₂ ≫ t) :
    (Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback t).obj M) ≅
      (Scheme.Modules.pullback q₂).obj ((Scheme.Modules.pullback t).obj M) :=
  chapter13ModuleBaseChangeCompIso t q₁ M ≪≫
    eqToIso (congrArg (fun q : U ⟶ S => (Scheme.Modules.pullback q).obj M) h) ≪≫
      (chapter13ModuleBaseChangeCompIso t q₂ M).symm

/- The torsor identity supplies the group-valued point taking one map to the other.  This is the
   point at which the representation action enters the associated-bundle descent datum. -/
noncomputable def chapter13TorsorDivisionPoint
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) {U : Scheme.{u}}
    (q₁ q₂ : U ⟶ P.carrier.left)
    (h : q₁ ≫ P.carrier.hom = q₂ ≫ P.carrier.hom) :
    Over.mk (q₁ ≫ P.carrier.hom) ⟶ G.X := by
  let p₁ : Over.mk (q₁ ≫ P.carrier.hom) ⟶ P.carrier := Over.homMk q₁
  let p₂ : Over.mk (q₁ ≫ P.carrier.hom) ⟶ P.carrier :=
    Over.homMk q₂ (by simpa using h.symm)
  exact Classical.choose
    (((chapter13_torsorIdentity_iff_unique P.action).mp P.identity
      (Over.mk (q₁ ≫ P.carrier.hom)) p₁ p₂).exists)

theorem chapter13TorsorDivisionPoint_spec
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) {U : Scheme.{u}}
    (q₁ q₂ : U ⟶ P.carrier.left)
    (h : q₁ ≫ P.carrier.hom = q₂ ≫ P.carrier.hom) :
    let p₁ : Over.mk (q₁ ≫ P.carrier.hom) ⟶ P.carrier := Over.homMk q₁
    let p₂ : Over.mk (q₁ ≫ P.carrier.hom) ⟶ P.carrier :=
      Over.homMk q₂ (by simpa using h.symm)
    CartesianMonoidalCategory.lift p₁
        (chapter13TorsorDivisionPoint P q₁ q₂ h) ≫ P.action.act = p₂ := by
  sorry

theorem chapter13TorsorDivisionPoint_unique
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) {U : Scheme.{u}}
    (q₁ q₂ : U ⟶ P.carrier.left)
    (h : q₁ ≫ P.carrier.hom = q₂ ≫ P.carrier.hom)
    (g : Over.mk (q₁ ≫ P.carrier.hom) ⟶ G.X)
    (hg :
      let p₁ : Over.mk (q₁ ≫ P.carrier.hom) ⟶ P.carrier := Over.homMk q₁
      let p₂ : Over.mk (q₁ ≫ P.carrier.hom) ⟶ P.carrier :=
        Over.homMk q₂ (by simpa using h.symm)
      CartesianMonoidalCategory.lift p₁ g ≫ P.action.act = p₂) :
    g = chapter13TorsorDivisionPoint P q₁ q₂ h := by
  sorry

noncomputable def chapter13RepresentationActionComparison
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (V : Chapter13SheafRepresentation G)
    {U : Scheme.{u}} (q₁ q₂ : U ⟶ P.carrier.left)
    (h : q₁ ≫ P.carrier.hom = q₂ ≫ P.carrier.hom) :
    (Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback P.carrier.hom).obj V.sheaf) ≅
      (Scheme.Modules.pullback q₂).obj ((Scheme.Modules.pullback P.carrier.hom).obj V.sheaf) :=
    (chapter04PullbackCompositionIso q₁ P.carrier.hom V.sheaf).symm ≪≫
    (V.action (q₁ ≫ P.carrier.hom)
      (chapter13TorsorDivisionPoint P q₁ q₂ h)).symm ≪≫
      eqToIso (congrArg (fun q : U ⟶ S =>
        (Scheme.Modules.pullback q).obj V.sheaf) h) ≪≫
        chapter04PullbackCompositionIso q₂ P.carrier.hom V.sheaf

/- The action laws and the canonical point pullback supply the C̆ech datum for the associated
   representation.  Keeping this as a named coherent object prevents later descent statements
   from silently using an unrelated double-overlap isomorphism. -/
noncomputable def chapter13RepresentationDescentDatum
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (V : Chapter13SheafRepresentation G) :
    Chapter13ModuleDescentDatum P.carrier.hom := by
  exact
    { upstairs := (Scheme.Modules.pullback P.carrier.hom).obj V.sheaf
      compare := fun {U} q₁ q₂ h =>
        chapter13RepresentationActionComparison P V q₁ q₂ h
      compare_self := by sorry
      compare_comp := by sorry
      compare_pull := by sorry }

noncomputable def chapter13TensorRepresentation
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (V W : Chapter13SheafRepresentation G) : Chapter13SheafRepresentation G where
  sheaf := chapter01SheafTensor V.sheaf W.sheaf
  finiteLocallyFree :=
    { sheaf := chapter01SheafTensor V.sheaf W.sheaf
      finiteLocallyFree := by sorry }
  sheaf_eq := rfl
  action := fun {T} t g =>
    let e := chapter13SheafTensorPullbackIso t V.sheaf W.sheaf
    { hom := e.inv ≫
          chapter01SheafTensorMap (V.action t g).hom (W.action t g).hom ≫ e.hom
      inv := e.inv ≫
          chapter01SheafTensorMap (V.action t g).inv (W.action t g).inv ≫ e.hom
      hom_inv_id := by sorry
      inv_hom_id := by sorry }
  action_one := by sorry
  action_mul := by sorry
  base_change := by sorry

noncomputable def chapter13AssociatedBundlePullbackDescentIso
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (M : S.Modules) :
    (Scheme.Modules.pullback (pullback.fst P.carrier.hom P.carrier.hom)).obj
        ((Scheme.Modules.pullback P.carrier.hom).obj M) ≅
    (Scheme.Modules.pullback (pullback.snd P.carrier.hom P.carrier.hom)).obj
        ((Scheme.Modules.pullback P.carrier.hom).obj M) := by
  exact chapter13ModuleBaseChangeComparison P.carrier.hom M
    (pullback.fst P.carrier.hom P.carrier.hom)
    (pullback.snd P.carrier.hom P.carrier.hom) pullback.condition

noncomputable def chapter13RepresentationDescentIso
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (V : Chapter13SheafRepresentation G) :
    (Scheme.Modules.pullback (pullback.fst P.carrier.hom P.carrier.hom)).obj
        ((Scheme.Modules.pullback P.carrier.hom).obj V.sheaf) ≅
    (Scheme.Modules.pullback (pullback.snd P.carrier.hom P.carrier.hom)).obj
        ((Scheme.Modules.pullback P.carrier.hom).obj V.sheaf) := by
  exact (chapter13RepresentationDescentDatum P V).compare
    (pullback.fst P.carrier.hom P.carrier.hom)
    (pullback.snd P.carrier.hom P.carrier.hom) pullback.condition

structure Chapter13AssociatedVectorBundleData
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (V : Chapter13SheafRepresentation G) where
  sheaf : S.Modules
  finiteLocallyFree : Chapter13FiniteLocallyFreeSheaf S
  sheaf_eq : finiteLocallyFree.sheaf = sheaf
  pullback_iso :
    (Scheme.Modules.pullback P.carrier.hom).obj sheaf ≅
      (Scheme.Modules.pullback P.carrier.hom).obj V.sheaf
  descent_compatibility :
    (Scheme.Modules.pullback (pullback.fst P.carrier.hom P.carrier.hom)).map
          pullback_iso.hom ≫
        (chapter13RepresentationDescentIso P V).hom =
      (chapter13AssociatedBundlePullbackDescentIso P sheaf).hom ≫
        (Scheme.Modules.pullback (pullback.snd P.carrier.hom P.carrier.hom)).map
          pullback_iso.hom

theorem chapter13_associatedVectorBundle_exists
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (V : Chapter13SheafRepresentation G) :
    Nonempty (Chapter13AssociatedVectorBundleData P V) := by
  sorry

noncomputable def chapter13AssociatedVectorBundle
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (V : Chapter13SheafRepresentation G) :
    Chapter13AssociatedVectorBundleData P V :=
  Classical.choice (chapter13_associatedVectorBundle_exists P V)

noncomputable def chapter13_associatedVectorBundle_is_finiteLocallyFree
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (V : Chapter13SheafRepresentation G) :
    Chapter13FiniteLocallyFreeSheaf S :=
  (chapter13AssociatedVectorBundle P V).finiteLocallyFree

/- The tensor operation on representations has a corresponding tensor operation on
   associated bundles.  The compatibility field is the descent comparison: after
   pulling back to the torsor, the tensor of the two descended sheaves is identified
   with the tensor representation's local model. -/
structure Chapter13AssociatedVectorBundleTensorData
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    {V W : Chapter13SheafRepresentation G}
    (P : Chapter13FpqcTorsor G)
    (A : Chapter13AssociatedVectorBundleData P V)
    (C : Chapter13AssociatedVectorBundleData P W) where
  associated :
    Chapter13AssociatedVectorBundleData P (chapter13TensorRepresentation V W)
  tensor_iso : chapter01SheafTensor A.sheaf C.sheaf ≅ associated.sheaf
  compatibility :
    (chapter13SheafTensorPullbackIso P.carrier.hom A.sheaf C.sheaf).hom ≫
        (Scheme.Modules.pullback P.carrier.hom).map tensor_iso.hom ≫
        associated.pullback_iso.hom =
      chapter01SheafTensorMap A.pullback_iso.hom C.pullback_iso.hom ≫
        (chapter13SheafTensorPullbackIso P.carrier.hom V.sheaf W.sheaf).hom

theorem chapter13_associatedVectorBundle_tensor
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G)
    {V W : Chapter13SheafRepresentation G}
    (A : Chapter13AssociatedVectorBundleData P V)
    (C : Chapter13AssociatedVectorBundleData P W) :
    Nonempty (Chapter13AssociatedVectorBundleTensorData P A C) := by
  sorry

/-- A bilinear pairing on the representation sheaves whose pullbacks are invariant. -/
structure Chapter13InvariantPairing
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (V W : Chapter13SheafRepresentation G) where
  pairing : chapter01SheafTensor V.sheaf W.sheaf ⟶
    SheafOfModules.unit S.ringCatSheaf
  invariant : ∀ {T : Scheme.{u}} (t : T ⟶ S)
    (g : Over.mk t ⟶ G.X),
    chapter01SheafTensorMap (V.action t g).hom (W.action t g).hom ≫
        (chapter13SheafTensorPullbackIso t V.sheaf W.sheaf).hom ≫
        (Scheme.Modules.pullback t).map pairing =
      (chapter13SheafTensorPullbackIso t V.sheaf W.sheaf).hom ≫
        (Scheme.Modules.pullback t).map pairing

structure Chapter13DescendedPairingData
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G)
    (V W : Chapter13SheafRepresentation G)
    (B : Chapter13InvariantPairing V W)
    (A : Chapter13AssociatedVectorBundleData P V)
    (C : Chapter13AssociatedVectorBundleData P W) where
  pairing : chapter01SheafTensor A.sheaf C.sheaf ⟶
    SheafOfModules.unit S.ringCatSheaf
  tensor_comparison :
    (Scheme.Modules.pullback P.carrier.hom).obj (chapter01SheafTensor A.sheaf C.sheaf) ≅
      chapter01SheafTensor
        ((Scheme.Modules.pullback P.carrier.hom).obj A.sheaf)
        ((Scheme.Modules.pullback P.carrier.hom).obj C.sheaf)
  unit_comparison :
    (Scheme.Modules.pullback P.carrier.hom).obj
        (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit P.carrier.left.ringCatSheaf
  compatibility :
    (Scheme.Modules.pullback P.carrier.hom).map pairing ≫ unit_comparison.hom =
      tensor_comparison.hom ≫
          chapter01SheafTensorMap A.pullback_iso.hom C.pullback_iso.hom ≫
          (chapter13SheafTensorPullbackIso P.carrier.hom V.sheaf W.sheaf).hom ≫
          (Scheme.Modules.pullback P.carrier.hom).map B.pairing ≫
          unit_comparison.hom

theorem chapter13_invariant_pairing_descends
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G)
    {V W : Chapter13SheafRepresentation G}
    (B : Chapter13InvariantPairing V W) :
    ∃ (A : Chapter13AssociatedVectorBundleData P V)
      (C : Chapter13AssociatedVectorBundleData P W),
      Nonempty (Chapter13DescendedPairingData P V W B A C) := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13
