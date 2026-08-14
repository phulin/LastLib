import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Data.Fintype.Card
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section02DimensionOneAsAMeetingPoint
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Dependencies
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01.Section01FromACurveOverAFieldToASurface
import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry

universe u v

/-! The pinned interfaces do not yet package contractions, normal bundles of
vertical curves, intersection numbers, or stable-model constructions.  The
records below keep those objects attached to their canonical schemes and
morphisms, so later proofs can replace individual fields without changing the
chapter-facing statements. -/

/-! ### Arithmetic bases, generic curves, and regular proper models -/

abbrev chapter11BaseScheme (R : Type u) [CommRing R] : Scheme.{u} :=
  Spec (CommRingCat.of R)

abbrev chapter11GenericBaseMap
    (R K : Type u) [CommRing R] [Field K] [Algebra R K] :
    Spec (CommRingCat.of K) ⟶ chapter11BaseScheme R :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K))

/- The theorem in §11.1 needs the excellence used to algebraize the formal
contraction.  It is kept as an explicit hypothesis rather than inferred from
the DVR class alone. -/
structure Chapter11ExcellentDiscreteValuationRing (R : Type u) [CommRing R] : Prop where
  domain : IsDomain R
  noetherian : IsNoetherianRing R
  local : IsLocalRing R
  discreteValuation : IsDiscreteValuationRing R
  excellent : Chapter01ExcellentRing R

theorem chapter11_excellent_discrete_valuation_ring_is_domain
    {R : Type u} [CommRing R]
    (hR : Chapter11ExcellentDiscreteValuationRing R) : IsDomain R :=
  hR.domain

structure Chapter11SmoothProjectiveCurve (K : Type u) [Field K] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (CommRingCat.of K)
  projective : Chapter07IsProjectiveMorphism structureMap
  proper : IsProper structureMap
  finitePresentation : LocallyOfFinitePresentation structureMap
  smooth : Smooth structureMap
  geometricallyConnected : GeometricallyConnected structureMap
  integral : IsIntegral carrier
  pureDimensionOne : Chapter01PureDimensionOne carrier
  genus : ℕ

instance (C : Chapter11SmoothProjectiveCurve K) : IsIntegral C.carrier := C.integral
instance (C : Chapter11SmoothProjectiveCurve K) : IsProper C.structureMap := C.proper
instance (C : Chapter11SmoothProjectiveCurve K) :
    LocallyOfFinitePresentation C.structureMap := C.finitePresentation
instance (C : Chapter11SmoothProjectiveCurve K) : Smooth C.structureMap := C.smooth
instance (C : Chapter11SmoothProjectiveCurve K) :
    GeometricallyConnected C.structureMap := C.geometricallyConnected

structure Chapter11GenericFiberIdentification
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (C : Chapter11SmoothProjectiveCurve K)
    {X : Scheme.{u}} (f : X ⟶ chapter11BaseScheme R) where
  iso : pullback f (chapter11GenericBaseMap R K) ≅ C.carrier
  over : iso.hom ≫ C.structureMap = pullback.snd f (chapter11GenericBaseMap R K)

structure Chapter11RegularProperModel
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (C : Chapter11SmoothProjectiveCurve K) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ chapter11BaseScheme R
  proper : IsProper structureMap
  finitePresentation : LocallyOfFinitePresentation structureMap
  flat : Flat structureMap
  relativeCurve :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Chapter01RelativeCurve
      structureMap
  integral : IsIntegral carrier
  dimensionTwo : Chapter01PureDimensionTwo carrier
  regular : Chapter01RegularScheme carrier
  fiberComponentsFinite : ∀ s : chapter11BaseScheme R,
    Finite (irreducibleComponents (structureMap.fiberToSpecResidueField s))
  genericFiber : Chapter11GenericFiberIdentification R K C structureMap

instance (M : Chapter11RegularProperModel R K C) : IsProper M.structureMap := M.proper
instance (M : Chapter11RegularProperModel R K C) :
    LocallyOfFinitePresentation M.structureMap := M.finitePresentation
instance (M : Chapter11RegularProperModel R K C) : Flat M.structureMap := M.flat
instance (M : Chapter11RegularProperModel R K C) : IsIntegral M.carrier := M.integral

abbrev chapter11ModelRestriction
    (M : Chapter11RegularProperModel R K C)
    (U : (chapter11BaseScheme R).Opens) :
    (M.carrier ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  M.structureMap ∣_ U

structure Chapter11ContractionCapability
    (M : Chapter11RegularProperModel R K C) : Prop where
  projective : Chapter07IsProjectiveMorphism M.structureMap
  base_excellent : Chapter01ExcellentScheme (chapter11BaseScheme R)
  total_excellent : Chapter01ExcellentScheme M.carrier

/- LOCAL_DEPENDENCY_GUESS: the earlier blowup API is presented through coherent
ideal sheaves, while this chapter needs the resulting point blowup as a model
over the arithmetic base.  The wrapper records that missing comparison. -/
structure Chapter11PointBlowupRegularModel
    (M : Chapter11RegularProperModel R K C)
    (x : M.carrier) (hx : IsClosed ({x} : Set M.carrier)) where
  blowup : Scheme.{u}
  projection : blowup ⟶ M.carrier
  isPointBlowup : Prop
  regularModel : Chapter11RegularProperModel R K C
  identification : regularModel.carrier ≅ blowup
  identification_over : identification.hom ≫ projection ≫ M.structureMap =
    regularModel.structureMap

/-! ### Vertical curves and the first-kind signature -/

structure Chapter11VerticalIntegralCurve
    (M : Chapter11RegularProperModel R K C) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ M.carrier
  closedImmersion : IsClosedImmersion inclusion
  integral : IsIntegral carrier
  locallyNoetherian : IsLocallyNoetherian carrier
  pureDimensionOne : Chapter01PureDimensionOne carrier
  basePoint : chapter11BaseScheme R
  basePoint_closed : IsClosed ({basePoint} : Set (chapter11BaseScheme R))
  vertical : ∀ x : carrier,
    (inclusion ≫ M.structureMap) x = basePoint

abbrev chapter11VerticalMap
    (E : Chapter11VerticalIntegralCurve M) :
    E.carrier ⟶ chapter11BaseScheme R :=
  E.inclusion ≫ M.structureMap

structure Chapter11ProjectiveLineOverResidueField
    (E : Chapter11VerticalIntegralCurve M) where
  factor : E.carrier ⟶
    Spec (CommRingCat.of ((chapter11BaseScheme R).residueField E.basePoint))
  factor_over : factor ≫ (chapter11BaseScheme R).fromSpecResidueField E.basePoint =
    chapter11VerticalMap E
  iso : E.carrier ≅
    chapter04ProjectiveLine ((chapter11BaseScheme R).residueField E.basePoint)
  iso_over : iso.hom ≫ chapter04ProjectiveLineStructureMap
      ((chapter11BaseScheme R).residueField E.basePoint) = factor

/- LOCAL_DEPENDENCY_GUESS: the normal line bundle and its numerical degree are
represented by a Book 8 line bundle plus an explicit degree bridge until the
intersection-theory package is available chronologically. -/
structure Chapter11NormalBundleProfile
    (E : Chapter11VerticalIntegralCurve M) where
  normalBundle : Chapter04LineBundle E.carrier
  isNormalBundle : Prop
  degree : ℤ
  degree_specification : Prop

def chapter11SelfIntersection
    (E : Chapter11VerticalIntegralCurve M)
    (N : Chapter11NormalBundleProfile E) : ℤ :=
  N.degree

def chapter11NormalBundleDegreeMinusOne
    (E : Chapter11VerticalIntegralCurve M) : Prop :=
  ∃ N : Chapter11NormalBundleProfile E,
    N.isNormalBundle ∧ N.degree = -1

structure Chapter11ExceptionalCurveOfFirstKind
    (M : Chapter11RegularProperModel R K C) where
  curve : Chapter11VerticalIntegralCurve M
  projectiveLine : Chapter11ProjectiveLineOverResidueField curve
  normalBundle : Chapter11NormalBundleProfile curve
  normalBundle_is_normal : normalBundle.isNormalBundle
  normalBundle_degree_minus_one : normalBundle.degree = -1
  selfIntersection : ℤ
  selfIntersection_eq_normalBundle_degree :
    selfIntersection = chapter11SelfIntersection curve normalBundle

def chapter11FirstKindCurveCondition
    (E : Chapter11VerticalIntegralCurve M) : Prop :=
  Nonempty (Chapter11ProjectiveLineOverResidueField E) ∧
    ∃ N : Chapter11NormalBundleProfile E,
      N.isNormalBundle ∧ N.degree = -1

def chapter11AlgebraicallyClosedExceptionalSignature
    (E : Chapter11VerticalIntegralCurve M) : Prop :=
  ∃ N : Chapter11NormalBundleProfile E,
    Nonempty (E.carrier ≅
      chapter04ProjectiveLine ((chapter11BaseScheme R).residueField E.basePoint)) ∧
    N.isNormalBundle ∧ chapter11SelfIntersection E N = -1

/-! ### The exact sequence and vanishing used by the formal contraction proof -/

structure Chapter11InfinitesimalNeighborhoodExactSequence
    (E : Chapter11VerticalIntegralCurve M) (n : ℤ) where
  left middle right : E.carrier.Modules
  inclusion : left ⟶ middle
  projection : middle ⟶ right
  zero : inclusion ≫ projection = 0
  exactness : (ShortComplex.mk inclusion projection zero).Exact
  left_is_twist : Prop
  middle_is_thickening_n_plus_one : Prop
  right_is_thickening_n : Prop

/- LOCAL_DEPENDENCY_GUESS: the pinned sheaf API does not expose the closed
immersion filtrations as named modules, so the exact sequence is packaged with
its three sheaf-identification capabilities rather than replacing them by
unrelated modules. -/

structure Chapter11ProjectiveLineTwistData (k : Type u) [Field k] (n : ℤ) where
  module : (chapter04ProjectiveLine k).Modules
  coherent : chapter04FiniteTypeQuasiCoherent module
  is_twist_of_structure_sheaf : Prop

/- LOCAL_DEPENDENCY_GUESS: the pinned cohomology API exposes finite-dimensional
realizations but not the canonical twisting-sheaf constructor for every integer
degree, so the twist is carried as a labeled module datum. -/

/-! ### Contraction data -/

def chapter11IsomorphismAwayFromCurve
    {Y X : Scheme.{u}} {E : Scheme.{u}}
    (f : Y ⟶ X) (i : E ⟶ Y) : Prop :=
  ∃ U : X.Opens, IsIso (f ∣_ U) ∧
    ∀ z : E, f (i z) ∉ (U : Set X)

/- LOCAL_DEPENDENCY_GUESS: the pinned ideal-sheaf interface does not yet
identify a contraction's maximal-ideal blowup with the divisor line bundle
O(-E), so the recovery diagram keeps those comparisons as named capabilities. -/
structure Chapter11PointBlowupRecovery
    (E : Chapter11ExceptionalCurveOfFirstKind M)
    (target : Chapter11RegularProperModel R K C)
    (contraction : M.carrier ⟶ target.carrier)
    (point : target.carrier) where
  local_maximal_ideal : Prop
  blowup : Scheme.{u}
  projection : blowup ⟶ target.carrier
  is_blowup_of_maximal_ideal : Prop
  identification : M.carrier ≅ blowup
  identification_over : identification.hom ≫ projection = contraction
  pullback_maximal_ideal_is_O_neg_E : Prop
  exceptional_divisor_identification : Prop

structure Chapter11ExceptionalContraction
    (M : Chapter11RegularProperModel R K C)
    (E : Chapter11ExceptionalCurveOfFirstKind M) where
  target : Chapter11RegularProperModel R K C
  contraction : M.carrier ⟶ target.carrier
  proper : IsProper contraction
  birational : Chapter07Birational contraction
  over_base : contraction ≫ target.structureMap = M.structureMap
  isIso_away_from_E : chapter11IsomorphismAwayFromCurve
    contraction E.curve.inclusion
  point : target.carrier
  contracts_E : ∀ z : E.curve.carrier,
    contraction (E.curve.inclusion z) = point
  point_closed : IsClosed ({point} : Set target.carrier)
  point_regular : IsRegularLocalRing (target.carrier.presheaf.stalk point)
  recovery : Nonempty (Chapter11PointBlowupRecovery E target contraction point)

def chapter11ContractionDecreasesFiberComponents
    (E : Chapter11ExceptionalCurveOfFirstKind M)
    (H : Chapter11ExceptionalContraction M E) : Prop :=
  Nat.card (irreducibleComponents
      (H.target.structureMap.fiberToSpecResidueField E.curve.basePoint)) <
    Nat.card (irreducibleComponents
      (M.structureMap.fiberToSpecResidueField E.curve.basePoint))

/-! ### Minimality, generic identifications, and finite extensions -/

def chapter11RelativelyMinimal
    (M : Chapter11RegularProperModel R K C) : Prop :=
  ¬ Nonempty (Chapter11ExceptionalCurveOfFirstKind M)

def chapter11InducesIdentityOnGenericFiber
    (M N : Chapter11RegularProperModel R K C)
    (u : M.carrier ⟶ N.carrier) : Prop :=
  ∃ hu : u ≫ N.structureMap = M.structureMap,
    M.genericFiber.iso.inv ≫
        pullback.lift
          (pullback.fst M.structureMap (chapter11GenericBaseMap R K) ≫ u)
          (pullback.snd M.structureMap (chapter11GenericBaseMap R K))
          (by rw [Category.assoc, hu]; simp) ≫
        N.genericFiber.iso.hom = 𝟙 C.carrier

structure Chapter11MinimalRegularModel
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (C : Chapter11SmoothProjectiveCurve K) where
  model : Chapter11RegularProperModel R K C
  positive_genus : 0 < C.genus
  relatively_minimal : chapter11RelativelyMinimal model

def chapter11ContractsAllVerticalExceptionalCurves
    (M target : Chapter11RegularProperModel R K C)
    (f : M.carrier ⟶ target.carrier) : Prop :=
  ∀ E : Chapter11ExceptionalCurveOfFirstKind M, ∃ p : target.carrier,
    ∀ z : E.curve.carrier, f (E.curve.inclusion z) = p

structure Chapter11ContractionToMinimal
    (M : Chapter11RegularProperModel R K C) where
  target : Chapter11MinimalRegularModel R K C
  contraction : M.carrier ⟶ target.model.carrier
  proper : IsProper contraction
  birational : Chapter07Birational contraction
  over_base : contraction ≫ target.model.structureMap = M.structureMap
  contracts_all : chapter11ContractsAllVerticalExceptionalCurves
    M target.model contraction

structure Chapter11FiniteSeparableExtension (K : Type u) [Field K] where
  extension : Type u
  [field_extension : Field extension]
  [algebra_extension : Algebra K extension]
  [finite_extension : FiniteDimensional K extension]
  [separable_extension : Algebra.IsSeparable K extension]

def chapter11RamifiedNodeEquation
    {K : Type u} [Field K]
    (E : Chapter11FiniteSeparableExtension K)
    (π' unit : E.extension) (e : ℕ)
    (x y : MvPolynomial (Fin 2) E.extension) : Prop :=
  x * y = MvPolynomial.C (unit * π' ^ e)

def chapter11RamifiedNodeEquationProfile
    {K : Type u} [Field K]
    (E : Chapter11FiniteSeparableExtension K)
    (π' unit : E.extension) (e : ℕ) : Prop :=
  IsUnit unit ∧ 1 < e ∧
    chapter11RamifiedNodeEquation E π' unit e
      (MvPolynomial.X 0) (MvPolynomial.X 1)

/- LOCAL_DEPENDENCY_GUESS: the pinned base-change API does not package the
normalization of a ramified DVR base change together with its resolved
exceptional curves, so the profile exposes the comparison maps explicitly. -/
structure Chapter11RamifiedBaseChangeProfile
    (M : Chapter11RegularProperModel R K C) where
  extension : Chapter11FiniteSeparableExtension K
  ramified : Prop
  ramified_node_equation : ∃ π' unit : extension.extension, ∃ e : ℕ,
    chapter11RamifiedNodeEquationProfile extension π' unit e
  baseChanged : Scheme.{u}
  baseChangeMap : baseChanged ⟶ M.carrier
  normalized : Scheme.{u}
  normalizationMap : normalized ⟶ baseChanged
  normalizationFinite : IsFinite normalizationMap
  normalizedNormal : Chapter01NormalScheme normalized
  resolved : Scheme.{u}
  resolutionMap : resolved ⟶ normalized
  resolvedRegular : Chapter01RegularScheme resolved
  resolvedOverOriginal : resolved ⟶ M.carrier
  resolution_factorization :
    resolutionMap ≫ normalizationMap ≫ baseChangeMap = resolvedOverOriginal
  newExceptionalCurve : Prop
  recontracted : Prop

/-! ### Global excellent Dedekind bases and models -/

structure Chapter11ExcellentDedekindBase
    (S : Scheme.{u}) (K : Type u) [Field K] where
  base : Chapter01DedekindBase S K
  excellent : Chapter01ExcellentScheme S
  quasiCompact : QuasiCompact (𝟙 S)

structure Chapter11GlobalRegularProperModelData
    (B : Chapter11ExcellentDedekindBase S K)
    (C : Chapter11SmoothProjectiveCurve K) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  proper : IsProper structureMap
  finitePresentation : LocallyOfFinitePresentation structureMap
  flat : Flat structureMap
  relativeCurve :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Chapter01RelativeCurve
      structureMap
  integral : IsIntegral carrier
  dimensionTwo : Chapter01PureDimensionTwo carrier
  regular : Chapter01RegularScheme carrier
  fiberComponentsFinite : ∀ s : S,
    Finite (irreducibleComponents (structureMap.fiberToSpecResidueField s))
  genericFiber : pullback structureMap B.base.genericPointMap ≅ C.carrier
  genericFiber_over : genericFiber.hom ≫ C.structureMap =
    pullback.snd structureMap B.base.genericPointMap

instance (M : Chapter11GlobalRegularProperModelData B C) :
    IsProper M.structureMap := M.proper
instance (M : Chapter11GlobalRegularProperModelData B C) :
    LocallyOfFinitePresentation M.structureMap := M.finitePresentation
instance (M : Chapter11GlobalRegularProperModelData B C) : Flat M.structureMap := M.flat
instance (M : Chapter11GlobalRegularProperModelData B C) : IsIntegral M.carrier := M.integral

def chapter11NonSmoothFiberSet
    (M : Chapter11GlobalRegularProperModelData B C) : Set S :=
  {s | ¬ Smooth (M.structureMap.fiberToSpecResidueField s)}

/- LOCAL_DEPENDENCY_GUESS: the global version of the residue-field normal-bundle
degree interface is not exposed by the earlier chapters, so its numerical
degree and projective-line comparison remain explicit fields here. -/
structure Chapter11GlobalVerticalExceptionalCurve
    (M : Chapter11GlobalRegularProperModelData B C) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ M.carrier
  closedImmersion : IsClosedImmersion inclusion
  integral : IsIntegral carrier
  locallyNoetherian : IsLocallyNoetherian carrier
  pureDimensionOne : Chapter01PureDimensionOne carrier
  basePoint : S
  basePoint_closed : IsClosed ({basePoint} : Set S)
  vertical : ∀ x : carrier, (inclusion ≫ M.structureMap) x = basePoint
  factor : carrier ⟶ Spec (CommRingCat.of (S.residueField basePoint))
  factor_over : factor ≫ S.fromSpecResidueField basePoint = inclusion ≫ M.structureMap
  projectiveLineIso : carrier ≅ chapter04ProjectiveLine (S.residueField basePoint)
  projectiveLineIso_over :
    projectiveLineIso.hom ≫ chapter04ProjectiveLineStructureMap
      (S.residueField basePoint) = factor
  normalBundleDegree : ℤ
  normalBundleDegree_eq_minus_one : normalBundleDegree = -1

def chapter11GlobalRelativelyMinimal
    (M : Chapter11GlobalRegularProperModelData B C) : Prop :=
  ¬ Nonempty (Chapter11GlobalVerticalExceptionalCurve M)

structure Chapter11GlobalMinimalRegularModel
    (B : Chapter11ExcellentDedekindBase S K)
    (C : Chapter11SmoothProjectiveCurve K) where
  model : Chapter11GlobalRegularProperModelData B C
  positive_genus : 0 < C.genus
  relatively_minimal : chapter11GlobalRelativelyMinimal model

/-! ### Marked curves and the boundary invariant -/

structure Chapter11MarkedCurve
    (C : Chapter11SmoothProjectiveCurve K) (n : ℕ) where
  section_ : Fin n → (Spec (CommRingCat.of K) ⟶ C.carrier)
  over : ∀ i, section_ i ≫ C.structureMap = 𝟙 _
  disjoint : ∀ i j, i ≠ j → ∀ z : Spec (CommRingCat.of K),
    section_ i z ≠ section_ j z

noncomputable def chapter11ModelSmoothLocus
    (M : Chapter11RegularProperModel R K C) : M.carrier.Opens := by
  letI := M.finitePresentation
  exact M.structureMap.smoothLocus

abbrev chapter11ModelSmoothLocusInclusion
    (M : Chapter11RegularProperModel R K C) :
    (chapter11ModelSmoothLocus M).toScheme ⟶ M.carrier :=
  Scheme.Opens.ι _

structure Chapter11MarkedModel
    (P : Chapter11MarkedCurve C n)
    (M : Chapter11RegularProperModel R K C) where
  lift : Fin n → (Spec (CommRingCat.of K) ⟶ M.carrier)
  over : ∀ i, lift i ≫ M.structureMap = chapter11GenericBaseMap R K
  transverse : Prop
  boundaryClosure : Prop
  defects_supported_at_closed_points : Prop
  surfaceInvariant : ℕ
  surfaceInvariant_specification : Prop
  boundaryTangencies : ℕ
  boundaryTangency_specification : Prop

noncomputable def chapter11MarkedLiftToGenericFiber
    (D : Chapter11MarkedModel P M) (i : Fin n) :
    Spec (CommRingCat.of K) ⟶
      pullback M.structureMap (chapter11GenericBaseMap R K) :=
  pullback.lift (D.lift i) (𝟙 _) (by simpa using D.over i)

def chapter11MarkedModelGenericCompatibility
    (D : Chapter11MarkedModel P M) : Prop :=
  ∀ i, chapter11MarkedLiftToGenericFiber D i ≫ M.genericFiber.iso.hom = P.section_ i

structure Chapter11MarkedResolutionFrom
    (D : Chapter11MarkedModel P M)
    (E : Chapter11MarkedModel P N) where
  map : N.carrier ⟶ M.carrier
  proper : IsProper map
  birational : Chapter07Birational map
  over_base : map ≫ M.structureMap = N.structureMap
  generic_identity : chapter11InducesIdentityOnGenericFiber N M map
  preserves_marks : ∀ i, map ≫ D.lift i = E.lift i

/- LOCAL_DEPENDENCY_GUESS: the pinned scheme API has no packaged closure of a
marked section in a special fiber or transverse-intersection predicate for the
boundary, so these are retained as named capabilities on the marked model. -/

def chapter11MarkedSectionsInSmoothLocus
    (D : Chapter11MarkedModel P M) : Prop :=
  ∀ i, ∃ q : Spec (CommRingCat.of K) ⟶
      (chapter11ModelSmoothLocus M).toScheme,
    q ≫ chapter11ModelSmoothLocusInclusion M = D.lift i

def chapter11MarkedSectionsDisjoint
    (D : Chapter11MarkedModel P M) : Prop :=
  ∀ i j, i ≠ j → ∀ z : Spec (CommRingCat.of K),
    D.lift i z ≠ D.lift j z

def chapter11MarkedSectionsMeetReducedSpecialFiberTransversely
    (D : Chapter11MarkedModel P M) : Prop :=
  D.transverse

def chapter11MarkedBoundaryResolved
    (D : Chapter11MarkedModel P M) : Prop :=
  D.boundaryClosure ∧
    D.defects_supported_at_closed_points ∧
    chapter11MarkedSectionsInSmoothLocus D ∧
    chapter11MarkedSectionsDisjoint D ∧
    chapter11MarkedSectionsMeetReducedSpecialFiberTransversely D

structure Chapter11MarkedResolutionInvariant where
  surface : ℕ
  boundaryTangencies : ℕ

def chapter11MarkedComplexity
    (D : Chapter11MarkedResolutionInvariant) : ℕ × ℕ :=
  (D.surface, D.boundaryTangencies)

def chapter11MarkedComplexityLt
    (a b : ℕ × ℕ) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

/-! ### Semistable and stable interfaces -/

def chapter11Uniformizer
    (R : Type u) [CommRing R] [IsLocalRing R] (π : R) : Prop :=
  π ≠ 0 ∧ Ideal.span ({π} : Set R) = IsLocalRing.maximalIdeal R

abbrev chapter11NodeEquationIdeal
    (R : Type u) [CommRing R] (π : R) :
    Ideal (MvPolynomial (Fin 2) R) :=
  chapter01NodalSurfaceRelation R π

abbrev chapter11NodeRing
    (R : Type u) [CommRing R] (π : R) :=
  chapter01NodalSurfaceRing R π

abbrev chapter11NodeSurface
    (R : Type u) [CommRing R] (π : R) : Scheme.{u} :=
  chapter01NodalSurfaceScheme R π

def chapter11NodeSurfaceStructureMap
    (R : Type u) [CommRing R] (π : R) :
    chapter11NodeSurface R π ⟶ chapter11BaseScheme R :=
  Scheme.Spec.map
    (CommRingCat.ofHom
      ((Ideal.Quotient.mk (chapter11NodeEquationIdeal R π)).comp MvPolynomial.C)).op

/- The ordinary-double-point predicate is inherited from the canonical
completed-local-ring interface; the remaining relative transversality field
is the book-facing bridge not bundled by that interface. -/
structure Chapter11OrdinaryDoublePoint
    (M : Chapter11RegularProperModel R K C) (x : M.carrier) : Prop where
  basePoint : chapter11BaseScheme R
  fiberPoint : M.structureMap.fiberToSpecResidueField basePoint
  point_eq : M.structureMap.fiberι basePoint fiberPoint = x
  ordinary :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.chapter01OrdinaryDoublePointAt
      (M.structureMap.fiberToSpecResidueField basePoint) fiberPoint
  intersection_multiplicity_one : Prop

structure Chapter11NodeEtaleChart
    (R : Type u) [CommRing R]
    (M : Chapter11RegularProperModel R K C)
    (x : M.carrier) (π : R) where
  chart : Scheme.{u}
  map : chart ⟶ M.carrier
  etale : Etale map
  point : chart
  point_maps_to : map point = x
  baseMap : chart ⟶ chapter11BaseScheme R
  baseMap_over : baseMap = map ≫ M.structureMap
  equation : Nonempty
    { e : chart ≅ chapter11NodeSurface R π //
      e.hom ≫ chapter11NodeSurfaceStructureMap R π = baseMap }

def chapter11NodeLocalEquation
    (M : Chapter11RegularProperModel R K C) (π : R) : Prop :=
  ∀ (x : M.carrier), Chapter11OrdinaryDoublePoint M x →
    Nonempty (Chapter11NodeEtaleChart R M x π)

def chapter11ReducedSpecialFibers
    (M : Chapter11RegularProperModel R K C) : Prop :=
  ∀ s : chapter11BaseScheme R,
    IsReduced (M.structureMap.fiberToSpecResidueField s)

def chapter11ComponentsMeetTransversely
    (M : Chapter11RegularProperModel R K C) : Prop :=
  ∀ (x : M.carrier) (h : Chapter11OrdinaryDoublePoint M x),
    h.intersection_multiplicity_one

structure Chapter11RegularSemistableModel
    (M : Chapter11RegularProperModel R K C) (π : R) where
  uniformizer : chapter11Uniformizer R π
  reducedSpecialFibers : chapter11ReducedSpecialFibers M
  ordinaryDoublePoints : ∀ x : M.carrier,
    Nonempty (Chapter11OrdinaryDoublePoint M x) ∨
      IsRegularLocalRing (M.carrier.presheaf.stalk x)
  transverseComponents : chapter11ComponentsMeetTransversely M
  nodeLocalEquation : chapter11NodeLocalEquation M π

/- LOCAL_DEPENDENCY_GUESS: stable curves and the stability inequality are not
bundled in the pinned scheme API, so this record retains the nodal, stability,
contraction, and ramified-base-change capabilities separately. -/
structure Chapter11StableModel (S : Scheme.{u}) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  proper : IsProper structureMap
  nodalSpecialFibers : Prop
  stable : Prop
  contractsUnstableRationalComponents : Prop
  obtained_after_ramified_base_change : Prop
  totalSpaceRegular : Chapter01RegularScheme carrier

def chapter11StableModelMayHaveNonregularTotalSpace
    (M : Chapter11StableModel S) : Prop :=
  M.obtained_after_ramified_base_change ∧ ¬ M.totalSpaceRegular

/-! ### Base-change repairs and normal proper candidates -/

/- LOCAL_DEPENDENCY_GUESS: preserving a prescribed nodal open through
normalization, resolution, and contraction has no single earlier API; the
candidate and repair records keep that compatibility named. -/
structure Chapter11NormalProperCandidate (S : Scheme.{u}) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  proper : IsProper structureMap
  integral : IsIntegral carrier
  normal : Chapter01NormalScheme carrier
  genericAgreement : Prop

structure Chapter11SemistableRepairInput (S : Scheme.{u}) where
  candidate : Chapter11NormalProperCandidate S
  nodalOpen : candidate.carrier.Opens
  nodalOpen_preserved_by_candidate : Prop

structure Chapter11SemistableRepairOutput (I : Chapter11SemistableRepairInput S) where
  normalization : Chapter01NormalizationData I.candidate.carrier
  resolution : Chapter01ResolutionData normalization.normalized
  finalModel : Scheme.{u}
  finalMap : finalModel ⟶ resolution.regularModel
  removedExceptionalComponents : Prop
  nodalOpenPreserved : Prop

structure Chapter11SemistableReductionOutput
    (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (C : Chapter11SmoothProjectiveCurve K) where
  base : Chapter11ExcellentDiscreteValuationRing R
  extension : Chapter11FiniteSeparableExtension K
  normalizedBase : Scheme.{u}
  normalizedBaseDedekind : Chapter01DedekindScheme normalizedBase
  normalizedBaseExcellent : Chapter01ExcellentScheme normalizedBase
  candidate : Chapter11NormalProperCandidate normalizedBase
  semistableModel : Scheme.{u}
  semistableModelMap : semistableModel ⟶ normalizedBase
  semistable : Prop
  genericFiberAfterExtension : Prop

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter11
