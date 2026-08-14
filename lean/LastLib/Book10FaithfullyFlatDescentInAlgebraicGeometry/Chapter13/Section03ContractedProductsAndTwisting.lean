import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter13.Section02LocalTrivialityAndEffectivity

/-!
# 13.3 Contracted products and twisting

The quotient is represented by its effective descent presentation.  The local model and its
pullback comparison are fields of the resulting object, so the statement that the twist becomes
`X_P` is available independently of the existence proof.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
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
    (α_ P X G.X).hom ≫
      (𝟙 P ⊗ₘ (β_ X G.X).hom) ≫
      (𝟙 P ⊗ₘ (GrpObj.inv (X := G.X) ⊗ₘ 𝟙 X)) ≫
      (α_ P G.X X).inv ≫
      (Paction.act ⊗ₘ 𝟙 X)
  one_act := by sorry
  mul_act := by sorry

/-- An effective descent presentation of the contracted product. -/
structure Chapter13ContractedProductData
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X) where
  carrier : Chapter13SchemeOver S
  pullback_iso :
    (Over.pullback P.carrier.hom).obj carrier ≅
      (Over.pullback P.carrier.hom).obj X

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

theorem chapter13_contractedProduct_becomes_local_model
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (X : Chapter13SchemeOver S)
    (Xaction : Chapter13LeftAction G X) :
    (Over.pullback P.carrier.hom).obj
        (chapter13ContractedProduct P X Xaction).carrier ≅
      (Over.pullback P.carrier.hom).obj X :=
  (chapter13ContractedProduct P X Xaction).pullback_iso

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

/- A sheaf representation is expressed by its functor-of-points action.  This avoids inventing a
Hopf-algebra presentation for a non-affine group scheme while retaining the action, identity, and
multiplication interfaces needed by associated bundles. -/
structure Chapter13SheafRepresentation
    {S : Scheme.{u}} (G : Chapter13GroupScheme S) where
  sheaf : S.Modules
  finiteLocallyFree : Chapter13FiniteLocallyFreeSheaf S
  sheaf_eq : finiteLocallyFree.sheaf = sheaf
  action : ∀ {T : Scheme.{u}} (t : T ⟶ S) (g : Over.mk t ⟶ G.X),
    (Scheme.Modules.pullback t).obj sheaf ≅
      (Scheme.Modules.pullback t).obj sheaf
  action_one : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    action t (chapter13GroupSectionOne G (Over.mk t)) = Iso.refl _
  action_mul : ∀ {T : Scheme.{u}} (t : T ⟶ S)
    (g h : Over.mk t ⟶ G.X),
    action t (chapter13GroupSectionMul G g h) = action t g ≪≫ action t h

noncomputable def chapter13TensorRepresentation
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (V W : Chapter13SheafRepresentation G) : Chapter13SheafRepresentation G where
  sheaf := chapter01SheafTensor V.sheaf W.sheaf
  finiteLocallyFree :=
    { sheaf := chapter01SheafTensor V.sheaf W.sheaf
      finiteLocallyFree := by sorry }
  sheaf_eq := rfl
  action := fun {T} t g =>
    { hom := chapter01SheafTensorMap (V.action t g).hom (W.action t g).hom
      inv := chapter01SheafTensorMap (V.action t g).inv (W.action t g).inv
      hom_inv_id := by sorry
      inv_hom_id := by sorry }
  action_one := by sorry
  action_mul := by sorry

structure Chapter13AssociatedVectorBundleData
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (V : Chapter13SheafRepresentation G) where
  sheaf : S.Modules
  finiteLocallyFree : Chapter13FiniteLocallyFreeSheaf S
  sheaf_eq : finiteLocallyFree.sheaf = sheaf
  pullback_iso :
    (Scheme.Modules.pullback P.carrier.hom).obj sheaf ≅
      (Scheme.Modules.pullback P.carrier.hom).obj V.sheaf

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

theorem chapter13_associatedVectorBundle_is_finiteLocallyFree
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (V : Chapter13SheafRepresentation G) :
    Chapter13FiniteLocallyFreeSheaf S :=
  (chapter13AssociatedVectorBundle P V).finiteLocallyFree

theorem chapter13_associatedVectorBundle_tensor
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (P : Chapter13FpqcTorsor G) (V W : Chapter13SheafRepresentation G) :
    Nonempty
      (Chapter13AssociatedVectorBundleData P (chapter13TensorRepresentation V W)) := by
  sorry

/-- A family of bilinear pairings whose invariance is tested on every base change. -/
structure Chapter13InvariantPairing
    {S : Scheme.{u}} {G : Chapter13GroupScheme S}
    (V W : Chapter13SheafRepresentation G) where
  pairing : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    chapter01SheafTensor
        ((Scheme.Modules.pullback t).obj V.sheaf)
        ((Scheme.Modules.pullback t).obj W.sheaf) ⟶
      SheafOfModules.unit T.ringCatSheaf
  invariant : ∀ {T : Scheme.{u}} (t : T ⟶ S)
    (g : Over.mk t ⟶ G.X),
    chapter01SheafTensorMap (V.action t g).hom (W.action t g).hom ≫ pairing t =
      pairing t

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
          B.pairing P.carrier.hom

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
