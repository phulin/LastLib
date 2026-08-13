import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13.Dependencies

/-!
## 13.1 Graphs and spaces of morphisms

The graph construction is made relative to a test scheme.  The fixed
Hilbert-polynomial datum is kept visible in every parameter-space interface.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

/-- A morphism between the two base changes over a test scheme. -/
structure Chapter13RelativeMorphism {S X Y : Scheme}
    (xS : X ⟶ S) (yS : Y ⟶ S) (T : Chapter13RelativeScheme S) where
  map : chapter13BaseChange xS T.toBase ⟶ chapter13BaseChange yS T.toBase
  over : map ≫ chapter13BaseChangeToTest yS T.toBase =
    chapter13BaseChangeToTest xS T.toBase

/-- The graph of a relative morphism is a map into the relative product over the test scheme. -/
def chapter13RelativeMorphismGraph {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {T : Chapter13RelativeScheme S}
    (u : Chapter13RelativeMorphism xS yS T) :
    chapter13BaseChange xS T.toBase ⟶
      chapter13RelativeProduct
        (chapter13BaseChangeToTest xS T.toBase)
        (chapter13BaseChangeToTest yS T.toBase) :=
  chapter13Graph _ _ u.map u.over

@[simp, reassoc]
theorem chapter13RelativeMorphismGraph_fst {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {T : Chapter13RelativeScheme S}
    (u : Chapter13RelativeMorphism xS yS T) :
    chapter13RelativeMorphismGraph u ≫
        chapter13RelativeProduct_fst
          (chapter13BaseChangeToTest xS T.toBase)
          (chapter13BaseChangeToTest yS T.toBase) = 𝟙 _ := by
  exact chapter13Graph_fst _ _ u.map u.over

@[simp, reassoc]
theorem chapter13RelativeMorphismGraph_snd {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {T : Chapter13RelativeScheme S}
    (u : Chapter13RelativeMorphism xS yS T) :
    chapter13RelativeMorphismGraph u ≫
        chapter13RelativeProduct_snd
          (chapter13BaseChangeToTest xS T.toBase)
          (chapter13BaseChangeToTest yS T.toBase) = u.map := by
  exact chapter13Graph_snd _ _ u.map u.over

theorem chapter13RelativeMorphismGraph_isClosedImmersion
    {S X Y : Scheme} {xS : X ⟶ S} {yS : Y ⟶ S}
    [IsSeparated yS] {T : Chapter13RelativeScheme S}
    (u : Chapter13RelativeMorphism xS yS T) :
    IsClosedImmersion (chapter13RelativeMorphismGraph u) := by
  sorry

/-! ### Changing the graph ambient to the chosen product over `S` -/

/-- The map from a test-base-changed `X` to the fixed product `X ×ₛ Y`. -/
def chapter13GraphToFixedProduct {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {T : Chapter13RelativeScheme S}
    (u : Chapter13RelativeMorphism xS yS T) :
    chapter13BaseChange xS T.toBase ⟶ chapter13RelativeProduct xS yS :=
  pullback.lift
    (chapter13BaseChangeToSource xS T.toBase)
    (u.map ≫ chapter13BaseChangeToSource yS T.toBase)
    (by sorry)

/-- The graph embedded in the base change of the fixed product over `S`. -/
def chapter13GraphInBaseChangedProduct {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {T : Chapter13RelativeScheme S}
    (u : Chapter13RelativeMorphism xS yS T) :
    chapter13BaseChange xS T.toBase ⟶
      chapter13BaseChange (chapter13RelativeProductToBase xS yS) T.toBase :=
  pullback.lift
    (chapter13GraphToFixedProduct u)
    (chapter13BaseChangeToTest xS T.toBase)
    (by sorry)

theorem chapter13GraphInBaseChangedProduct_isClosedImmersion
    {S X Y : Scheme} {xS : X ⟶ S} {yS : Y ⟶ S}
    [IsSeparated yS] {T : Chapter13RelativeScheme S}
    (u : Chapter13RelativeMorphism xS yS T) :
    IsClosedImmersion (chapter13GraphInBaseChangedProduct u) := by
  sorry

/-- The projection from the base change of the fixed product to the base-changed source. -/
def chapter13FixedProductBaseChangeToSource {S X Y : Scheme}
    (xS : X ⟶ S) (yS : Y ⟶ S) (T : Chapter13RelativeScheme S) :
    chapter13BaseChange (chapter13RelativeProductToBase xS yS) T.toBase ⟶
      chapter13BaseChange xS T.toBase :=
  pullback.lift
    (pullback.fst (chapter13RelativeProductToBase xS yS) T.toBase ≫
      chapter13RelativeProduct_fst xS yS)
    (chapter13BaseChangeToTest (chapter13RelativeProductToBase xS yS) T.toBase)
    (by sorry)

/-- The graph projection whose being an isomorphism is the open graph condition. -/
def chapter13RelativeGraphProjection {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {T : Chapter13RelativeScheme S}
    (u : Chapter13RelativeMorphism xS yS T) :
    chapter13BaseChange xS T.toBase ⟶ chapter13BaseChange xS T.toBase :=
  chapter13GraphInBaseChangedProduct u ≫
    chapter13FixedProductBaseChangeToSource xS yS T

def chapter13GraphProjectionCondition {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {T : Chapter13RelativeScheme S}
    (u : Chapter13RelativeMorphism xS yS T) : Prop :=
  IsIso (chapter13RelativeGraphProjection u)

/-- Base change of a map of schemes over a common base. -/
def chapter13BaseChangedMap {Z X H T : Scheme}
    (p : Z ⟶ H) (q : X ⟶ H) (u : Z ⟶ X)
    (hu : u ≫ q = p) (t : T ⟶ H) :
    pullback p t ⟶ pullback q t :=
  pullback.lift (pullback.fst p t ≫ u) (pullback.snd p t) (by sorry)

def chapter13IsomorphismConditionOnTest {Z X H : Scheme}
    (p : Z ⟶ H) (q : X ⟶ H) (u : Z ⟶ X)
    (hu : u ≫ q = p) (T : Scheme) (t : T ⟶ H) : Prop :=
  IsIso (chapter13BaseChangedMap p q u hu t)

/-- The corresponding geometric-fiber test for the isomorphism condition. -/
def chapter13IsomorphismConditionOnFiber {Z X H : Scheme}
    (p : Z ⟶ H) (q : X ⟶ H) (u : Z ⟶ X)
    (hu : u ≫ q = p) (y : H) : Prop :=
  IsIso (chapter13BaseChangedMap p q u hu (H.fromSpecResidueField y))

theorem chapter13_proper_finite_presentation_isomorphism_locus_is_open
    {Z X H : Scheme} (p : Z ⟶ H) (q : X ⟶ H) (u : Z ⟶ X)
    (hu : u ≫ q = p) (hproper : IsProper u)
    (hfinitePresentation : LocallyOfFinitePresentation u)
    (hflatP : Flat p) (hflatQ : Flat q) :
    Nonempty (Chapter13OpenLocusData H
      (chapter13IsomorphismConditionOnTest p q u hu)) := by
  sorry

/-! ### Fixed Hilbert polynomial -/

/-- A certificate that the graph has the selected polynomial in the chosen relative-product embedding. -/
structure Chapter13GraphPolynomialData {S X Y : Scheme}
    (xS : X ⟶ S) (yS : Y ⟶ S)
    (L : Chapter13Polarization (chapter13RelativeProductToBase xS yS))
    (P : Chapter13NumericalPolynomial) (T : Chapter13RelativeScheme S)
    (u : Chapter13RelativeMorphism xS yS T) where
  /-- The graph is closed in the relative product over the test scheme. -/
  graph_closed : IsClosedImmersion (chapter13GraphInBaseChangedProduct u)
  /-- The polarization used for the graph family after base change. -/
  baseChangedPolarization : Chapter13Polarization
    (chapter13BaseChangeToTest (chapter13RelativeProductToBase xS yS) T.toBase)
  certificate : Chapter13HilbertPolynomialCertificate
    (chapter13BaseChange xS T.toBase)
    (chapter13BaseChange (chapter13RelativeProductToBase xS yS) T.toBase)
    (chapter13GraphInBaseChangedProduct u)
    (chapter13BaseChangeToTest (chapter13RelativeProductToBase xS yS) T.toBase)
    baseChangedPolarization
  /-- The test-scheme polarization is the pullback of the fixed one. -/
  polarization_compatibility : Nonempty
    ((chapter04PullbackLineBundle
        (chapter13BaseChangeToSource (chapter13RelativeProductToBase xS yS) T.toBase)
        L.lineBundle).sheaf ≅ baseChangedPolarization.lineBundle.sheaf)
  polynomial_eq : certificate.polynomial = P

def chapter13GraphHasPolynomial {S X Y : Scheme}
    (xS : X ⟶ S) (yS : Y ⟶ S)
    (L : Chapter13Polarization (chapter13RelativeProductToBase xS yS))
    (P : Chapter13NumericalPolynomial) (T : Chapter13RelativeScheme S)
    (u : Chapter13RelativeMorphism xS yS T) : Prop :=
  Nonempty (Chapter13GraphPolynomialData xS yS L P T u)

/-- Relative morphisms whose graph belongs to the fixed polynomial-bounded problem. -/
def chapter13GraphMorphismAtPolynomial {S X Y : Scheme}
    (xS : X ⟶ S) (yS : Y ⟶ S)
    (L : Chapter13Polarization (chapter13RelativeProductToBase xS yS))
    (P : Chapter13NumericalPolynomial) (T : Chapter13RelativeScheme S) : Type :=
  {u : Chapter13RelativeMorphism xS yS T // chapter13GraphHasPolynomial xS yS L P T u}

/-! ### The graph condition on the Hilbert family -/

def chapter13HilbertFamilyAt {S A : Scheme}
    {aS : A ⟶ S} {L : Chapter13Polarization aS} {P : Chapter13NumericalPolynomial}
    (H : Chapter13HilbertSchemeData aS L P)
    (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative) :
    Chapter13FlatClosedFamily aS L P T :=
  H.classifies T ((H.represented.equiv T).symm t)

/-- A Hilbert-family point is a graph when its family is isomorphic to the source
base change and its closed embedding is the graph embedding. -/
def chapter13HilbertFamilyIsGraph {S X Y : Scheme}
    (xS : X ⟶ S) (yS : Y ⟶ S)
    (L : Chapter13Polarization (chapter13RelativeProductToBase xS yS))
    (P : Chapter13NumericalPolynomial)
    (H : Chapter13HilbertSchemeData (chapter13RelativeProductToBase xS yS) L P)
    (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative) : Prop :=
  ∃ (u : Chapter13RelativeMorphism xS yS T),
    ∃ (_ : chapter13GraphHasPolynomial xS yS L P T u),
      ∃ e : (chapter13HilbertFamilyAt H T t).scheme ≅ chapter13BaseChange xS T.toBase,
        e.hom ≫ chapter13GraphInBaseChangedProduct u =
            (chapter13HilbertFamilyAt H T t).inclusion ∧
        e.hom ≫ chapter13BaseChangeToTest xS T.toBase =
            (chapter13HilbertFamilyAt H T t).projection

/-- The open graph locus inside a fixed-polynomial Hilbert scheme. -/
structure Chapter13GraphParameterSpaceData {S X Y : Scheme}
    (xS : X ⟶ S) (yS : Y ⟶ S)
    (L : Chapter13Polarization (chapter13RelativeProductToBase xS yS))
    (P : Chapter13NumericalPolynomial)
    (H : Chapter13HilbertSchemeData (chapter13RelativeProductToBase xS yS) L P) where
  graphLocus : (chapter13HilbertScheme H).Opens
  graphLocus_represents : ∀ (T : Chapter13RelativeScheme S)
    (t : Chapter13RelativeMap T H.represented.representative),
    chapter13HilbertFamilyIsGraph xS yS L P H T t ↔
      ∃ q : Chapter13RelativeMap T
          (chapter13OpenRelativeScheme H.represented.representative graphLocus),
        q.map ≫ graphLocus.ι = t.map
  /-- The open graph locus represents the fixed-polynomial morphism functor. -/
  graph_morphisms : ∀ (T : Chapter13RelativeScheme S),
    Chapter13RelativeMap T
        (chapter13OpenRelativeScheme H.represented.representative graphLocus) ≃
      chapter13GraphMorphismAtPolynomial xS yS L P T
  locallyFiniteType : LocallyOfFiniteType graphLocus.ι
  locallyFiniteTypeOverBase :
    LocallyOfFiniteType (graphLocus.ι ≫ H.represented.representative.toBase)

def chapter13GraphParameterSpace {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {L : Chapter13Polarization (chapter13RelativeProductToBase xS yS)}
    {P : Chapter13NumericalPolynomial}
    {H : Chapter13HilbertSchemeData (chapter13RelativeProductToBase xS yS) L P}
    (G : Chapter13GraphParameterSpaceData xS yS L P H) :
    Chapter13RelativeScheme S :=
  chapter13OpenRelativeScheme H.represented.representative G.graphLocus

def chapter13GraphParameterSpaceToHilbert {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {L : Chapter13Polarization (chapter13RelativeProductToBase xS yS)}
    {P : Chapter13NumericalPolynomial}
    {H : Chapter13HilbertSchemeData (chapter13RelativeProductToBase xS yS) L P}
    (G : Chapter13GraphParameterSpaceData xS yS L P H) :
    Chapter13RelativeMap (chapter13GraphParameterSpace G)
      H.represented.representative where
  map := G.graphLocus.ι
  over := by rfl

theorem chapter13GraphParameterSpace_isOpen {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {L : Chapter13Polarization (chapter13RelativeProductToBase xS yS)}
    {P : Chapter13NumericalPolynomial}
    {H : Chapter13HilbertSchemeData (chapter13RelativeProductToBase xS yS) L P}
    (G : Chapter13GraphParameterSpaceData xS yS L P H) :
    IsOpenImmersion (chapter13GraphParameterSpaceToHilbert G).map := by
  change IsOpenImmersion G.graphLocus.ι
  infer_instance

theorem chapter13GraphParameterSpace_isLocallyFiniteType {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {L : Chapter13Polarization (chapter13RelativeProductToBase xS yS)}
    {P : Chapter13NumericalPolynomial}
    {H : Chapter13HilbertSchemeData (chapter13RelativeProductToBase xS yS) L P}
    (G : Chapter13GraphParameterSpaceData xS yS L P H) :
    LocallyOfFiniteType (chapter13GraphParameterSpaceToHilbert G).map := by
  change LocallyOfFiniteType G.graphLocus.ι
  exact G.locallyFiniteType

theorem chapter13GraphParameterSpace_isLocallyFiniteTypeOverBase {S X Y : Scheme}
    {xS : X ⟶ S} {yS : Y ⟶ S}
    {L : Chapter13Polarization (chapter13RelativeProductToBase xS yS)}
    {P : Chapter13NumericalPolynomial}
    {H : Chapter13HilbertSchemeData (chapter13RelativeProductToBase xS yS) L P}
    (G : Chapter13GraphParameterSpaceData xS yS L P H) :
    LocallyOfFiniteType
      ((chapter13GraphParameterSpaceToHilbert G).map ≫ H.represented.representative.toBase) := by
  change LocallyOfFiniteType
    (G.graphLocus.ι ≫ H.represented.representative.toBase)
  exact G.locallyFiniteTypeOverBase

/-
SOURCE_NOTE: the chapter's sentence that there is no single finite-type
scheme of all morphisms of arbitrary degree is a finiteness warning rather
than a theorem with hypotheses.  The formal API below records the fixed
polynomial parameter space and does not assert a universal negative theorem.
-/

theorem chapter13_graph_condition_is_open
    {S X Y : Scheme} (xS : X ⟶ S) (yS : Y ⟶ S)
    (L : Chapter13Polarization (chapter13RelativeProductToBase xS yS))
    (P : Chapter13NumericalPolynomial)
    (H : Chapter13HilbertSchemeData (chapter13RelativeProductToBase xS yS) L P)
    (hXprojective : Chapter13ProjectiveMorphism xS)
    (hXflat : Flat xS)
    (hXfinitePresentation : LocallyOfFinitePresentation xS)
    (hYprojective : Chapter13ProjectiveMorphism yS)
    [IsSeparated yS] :
    Nonempty (Chapter13GraphParameterSpaceData xS yS L P H) := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter13
