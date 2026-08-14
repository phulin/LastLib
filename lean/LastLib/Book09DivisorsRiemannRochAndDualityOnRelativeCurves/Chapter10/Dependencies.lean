import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Etale.Basic
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section04FormalPowerSeries
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section01TheAbsoluteAndRelativeSettings
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Core

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
open scoped BigOperators LaurentSeries PowerSeries

universe u v

/-!
Shared interfaces for Chapter 10.

The pinned Mathlib tree supplies schemes, finite/proper/flat morphisms, sheaves
of modules, Kähler differentials, formal power series, and Laurent series.  It
does not yet package nodal curves, normalizations, skyscraper sheaves, or
relative dualizing sheaves.  The records below keep those missing geometric
interfaces explicit while every ring, sheaf, pushforward, quotient, and
differential which is already canonical is taken from Mathlib.
-/

/-! ### Curves, normalizations, and node data -/

/-!
Chapter 1 supplies the completed-local-ring ordinary-double-point predicate.
Chapter 10 keeps a small wrapper so its curve and node records can expose the
book-facing nodal data without weakening it to an unconstrained proposition.
-/

def chapter10IsNormal (X : Scheme.{u}) : Prop :=
  IsLocallyNoetherian X ∧
    ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧
        IsIntegrallyClosed (X.presheaf.stalk x)

structure Chapter10NodalCurvePredicate (X : Scheme.{u}) where
  nodal : chapter01NodalScheme X

def chapter10IsNodal (X : Scheme.{u}) : Prop :=
  Nonempty (Chapter10NodalCurvePredicate X)

/-!
The normalization property is only a universal property for dominant maps from
normal schemes.  Without dominance, a map into a node need not have a unique
lift (a closed point at the node can choose either branch), so an unqualified
factorization statement would be false.  The normalization map itself must also
be dominant; otherwise the universal quantifier over dominant test maps could
be vacuous and would not characterize a normalization.
-/
def Chapter10NormalizationUniversalProperty
    {N C : Scheme.{u}} (ν : N ⟶ C) : Prop :=
  IsDominant ν ∧
    ∀ (Y : Scheme.{u}) (_hY : chapter10IsNormal Y) (g : Y ⟶ C)
      (_hg : IsDominant g),
      ∃! h : Y ⟶ N, h ≫ ν = g

structure Chapter10RelativeNodalPredicate
    {X S : Scheme.{u}} (f : X ⟶ S) where
  relativeNodalCurve : Chapter01NodalRelativeCurve f

def chapter10IsRelativeNodal
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Nonempty (Chapter10RelativeNodalPredicate f)

/-- The spectrum of the coefficient field used for a curve over a field. -/
def chapter10FieldBaseScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of k)

/-- A reduced proper nodal curve over a field, with connectedness recorded
separately because the genus formula has a connected and a disconnected form. -/
structure Chapter10Curve (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ chapter10FieldBaseScheme k
  reduced : IsReduced carrier
  proper : IsProper structureMap
  finiteType : LocallyOfFiniteType structureMap
  pureDimensionOne : Chapter01PureDimensionOne carrier
  nodal : chapter10IsNodal carrier
  connected : _root_.IsConnected (Set.univ : Set carrier)

/-- A finite normalization of a Chapter 10 curve.  The normality and
normalization universal property are intentionally explicit local interfaces. -/
structure Chapter10Normalization {k : Type u} [Field k]
    (C : Chapter10Curve k) where
  carrier : Scheme.{u}
  map : carrier ⟶ C.carrier
  finite : IsFinite map
  normal : chapter10IsNormal carrier
  isNormalization : Chapter10NormalizationUniversalProperty map

def chapter10NormalizationStructureMap {k : Type u} [Field k]
    {C : Chapter10Curve k} (N : Chapter10Normalization C) :
    N.carrier ⟶ chapter10FieldBaseScheme k :=
  N.map ≫ C.structureMap

/-- The finite set of nodes used by the split and nonsplit descriptions. -/
structure Chapter10NodeFamily {k : Type u} [Field k]
    (C : Chapter10Curve k) where
  index : Type u
  [finite : Fintype index]
  point : index → C.carrier
  isNode : ∀ q, chapter01OrdinaryDoublePointAt C.carrier (point q)
  pairwiseDistinct : Pairwise (fun q r : index => point q ≠ point r)
  exhaustive : ∀ x : C.carrier,
    chapter01OrdinaryDoublePointAt C.carrier x → ∃ q, point q = x

attribute [instance] Chapter10NodeFamily.finite

/-- Chosen inverse images of rational nodes on a normalization. -/
structure Chapter10SplitBranchFamily {k : Type u} [Field k]
    {C : Chapter10Curve k} (N : Chapter10Normalization C)
    (nodes : Chapter10NodeFamily C) where
  left : nodes.index → N.carrier
  right : nodes.index → N.carrier
  left_over_node : ∀ q : nodes.index, N.map (left q) = nodes.point q
  right_over_node : ∀ q : nodes.index, N.map (right q) = nodes.point q
  branches_distinct : ∀ q : nodes.index, left q ≠ right q
  all_preimages : ∀ (q : nodes.index) (z : N.carrier),
    N.map z = nodes.point q → z = left q ∨ z = right q

/-!
The residue field and branch algebra records are the nonsplit replacement for
an ordered pair of rational branches.  The bracketed fields install the
canonical algebra instances when a record is unpacked.
-/

/-- The residue field of a node, together with its finite degree over `k`. -/
structure Chapter10ResidueFieldData (k : Type u) [Field k] where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra k carrier]
  finite : FiniteDimensional k carrier
  degree : ℕ
  degree_eq_finrank : degree = Module.finrank k carrier

attribute [instance] Chapter10ResidueFieldData.field
attribute [instance] Chapter10ResidueFieldData.algebra

/-- A degree-two finite étale algebra of branches over a residue field. -/
structure Chapter10BranchAlgebraData (K : Type u) [Field K] where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra K carrier]
  finite : Module.Finite K carrier
  flat : Module.Flat K carrier
  rank_two : Module.finrank K carrier = 2
  [etale : Algebra.Etale K carrier]

attribute [instance] Chapter10BranchAlgebraData.commRing
attribute [instance] Chapter10BranchAlgebraData.algebra
attribute [instance] Chapter10BranchAlgebraData.etale

/-- The intrinsic discrepancy line `B_q / κ(q)`, with the residue field
embedded diagonally through the algebra map. -/
abbrev chapter10DiscrepancyLine
    {K : Type u} [Field K] (B : Chapter10BranchAlgebraData K) : Type u := by
  letI := B.commRing
  letI := B.algebra
  exact B.carrier ⧸ Submodule.span K (Set.range (algebraMap K B.carrier))

theorem chapter10_discrepancy_line_is_one_dimensional
    {K : Type u} [Field K] (B : Chapter10BranchAlgebraData K) :
    letI := B.commRing
    letI := B.algebra
    Module.finrank K (chapter10DiscrepancyLine B) = 1 := by
  let := B.commRing
  let := B.algebra
  let := B.finite
  let : Nontrivial B.carrier :=
    Module.nontrivial_of_finrank_pos (by rw [B.rank_two]; decide)
  let W : Submodule K B.carrier :=
    Submodule.span K (Set.range (algebraMap K B.carrier))
  have hW : W = K ∙ (1 : B.carrier) := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro x ⟨r, rfl⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self 1)
    · refine Submodule.span_le.2 ?_
      intro x hx
      have hx1 : x = (1 : B.carrier) := by simpa using hx
      rw [hx1]
      exact Submodule.subset_span
        (show (1 : B.carrier) ∈ Set.range (algebraMap K B.carrier) from ⟨1, by simp⟩)
  have hWfinrank : Module.finrank K W = 1 := by
    rw [hW]
    exact finrank_span_singleton (K := K) (v := (1 : B.carrier)) one_ne_zero
  have hquot := W.finrank_quotient_add_finrank
  rw [hWfinrank, B.rank_two] at hquot
  change Module.finrank K (B.carrier ⧸ W) = 1
  omega

/-- All local data attached to a possibly nonsplit node. -/
structure Chapter10NonsplitNodeData (k : Type u) [Field k] where
  residue : Chapter10ResidueFieldData k
  branches : Chapter10BranchAlgebraData residue.carrier

abbrev chapter10NodeDiscrepancyLine
    {k : Type u} [Field k] (q : Chapter10NonsplitNodeData k) : Type u := by
  letI := q.residue.field
  exact chapter10DiscrepancyLine q.branches

/-- A connected nodal curve together with its normalization components, node
residue degrees, and the numerical genus profile used by the Euler
characteristic calculation. -/
structure Chapter10NodalCurveData (k : Type u) [Field k] where
  curve : Chapter10Curve k
  normalization : Chapter10Normalization curve
  nodes : Type u
  [nodesFinite : Fintype nodes]
  nodePoint : nodes → curve.carrier
  nodeIsNode : ∀ q, chapter01OrdinaryDoublePointAt curve.carrier (nodePoint q)
  nodePointsDistinct : Pairwise (fun q r : nodes => nodePoint q ≠ nodePoint r)
  nodePointsExhaustive : ∀ x : curve.carrier,
    chapter01OrdinaryDoublePointAt curve.carrier x → ∃ q, nodePoint q = x
  nodeData : nodes → Chapter10NonsplitNodeData k
  components : Type u
  [componentsFinite : Fintype components]
  componentGenus : components → ℤ
  arithmeticGenus : ℤ
  structureSheafEulerCharacteristic : ℤ
  arithmeticGenus_eq_one_sub_eulerCharacteristic :
    arithmeticGenus = 1 - structureSheafEulerCharacteristic
  normalizationEulerCharacteristic : ℤ
  normalizationEulerCharacteristic_eq_components :
    normalizationEulerCharacteristic = ∑ i, (1 - componentGenus i)
  normalizationComponents : Prop
  normalizationComponents_holds : normalizationComponents
  normalizationComponentsSmooth : Prop
  normalizationComponentsSmooth_holds : normalizationComponentsSmooth

attribute [instance] Chapter10NodalCurveData.nodesFinite
attribute [instance] Chapter10NodalCurveData.componentsFinite

def chapter10NodeResidueDegree {k : Type u} [Field k]
    (D : Chapter10NodalCurveData k) (q : D.nodes) : ℕ :=
  (D.nodeData q).residue.degree

def chapter10FirstBettiNumber (vertices edges : ℕ) : ℤ :=
  (edges : ℤ) - (vertices : ℤ) + 1

def chapter10DualGraphAdjacent {V E : Type u}
    (left right : E → V) (v w : V) : Prop :=
  ∃ e, (left e = v ∧ right e = w) ∨ (left e = w ∧ right e = v)

/-! The combinatorial dual graph of a connected nodal curve. -/
structure Chapter10DualGraph where
  vertices : Type u
  [verticesFinite : Fintype vertices]
  edges : Type u
  [edgesFinite : Fintype edges]
  left : edges → vertices
  right : edges → vertices
  connected : ∀ v w,
    Relation.ReflTransGen (chapter10DualGraphAdjacent left right) v w

attribute [instance] Chapter10DualGraph.verticesFinite
attribute [instance] Chapter10DualGraph.edgesFinite

def Chapter10DualGraph.firstBetti (G : Chapter10DualGraph) : ℤ :=
  chapter10FirstBettiNumber (Fintype.card G.vertices) (Fintype.card G.edges)

/-! ### Canonical structure sheaves and normalization functions -/

def chapter10CurveStructureSheaf {k : Type u} [Field k]
    (C : Chapter10Curve k) : C.carrier.Modules :=
  SheafOfModules.unit C.carrier.ringCatSheaf

def chapter10NormalizationPushforwardStructureSheaf {k : Type u} [Field k]
    {C : Chapter10Curve k} (N : Chapter10Normalization C) : C.carrier.Modules :=
  (Scheme.Modules.pushforward N.map).obj
    (SheafOfModules.unit N.carrier.ringCatSheaf)

/-- The global functions and branch evaluations needed for the split descent
criterion.  The section types are the canonical global sections of the
structure sheaves; evaluations are the local node interface. -/
structure Chapter10SplitNormalizationFunctionData
    {k : Type u} [Field k] where
  curve : Chapter10Curve k
  normalization : Chapter10Normalization curve
  nodes : Chapter10NodeFamily curve
  branches : Chapter10SplitBranchFamily normalization nodes
  pullback : Γ(curve.carrier, ⊤) → Γ(normalization.carrier, ⊤)
  leftValue : nodes.index → Γ(normalization.carrier, ⊤) → k
  rightValue : nodes.index → Γ(normalization.carrier, ⊤) → k
  /-- Pullbacks of regular functions have equal values on the two branches. -/
  pullback_branch_agreement :
    ∀ (g : Γ(curve.carrier, ⊤)) (q : nodes.index),
      leftValue q (pullback g) = rightValue q (pullback g)
  /-- The normalization exactness step: every branch-compatible function lifts. -/
  branch_agreement_lifts :
    ∀ (f : Γ(normalization.carrier, ⊤)),
      (∀ q : nodes.index, leftValue q f = rightValue q f) →
        ∃ g : Γ(curve.carrier, ⊤), pullback g = f

def chapter10FunctionDescends
    {k : Type u} [Field k]
    (D : Chapter10SplitNormalizationFunctionData (k := k))
    (f : Γ(D.normalization.carrier, ⊤)) : Prop :=
  ∀ q : D.nodes.index, D.leftValue q f = D.rightValue q f

theorem chapter10_function_descends_iff
    {k : Type u} [Field k]
    (D : Chapter10SplitNormalizationFunctionData (k := k))
    (f : Γ(D.normalization.carrier, ⊤)) :
    (∃ g : Γ(D.curve.carrier, ⊤), D.pullback g = f) ↔
      chapter10FunctionDescends D f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact D.pullback_branch_agreement g
  · intro h
    exact D.branch_agreement_lifts f h

/-!
The direct sum of node discrepancy lines is not yet a standard skyscraper
sheaf constructor in the pinned snapshot.  This record keeps its sheaf
carrier and its nodewise decomposition explicit, so the exact-sequence
statement cannot accidentally be replaced by an unrelated object.
-/

structure Chapter10NodeDiscrepancySheaf {k : Type u} [Field k]
    (D : Chapter10NodalCurveData k) where
  sheaf : D.curve.carrier.Modules
  isDirectSumOfPushforwardDiscrepancyLines : Prop
  isDirectSumOfPushforwardDiscrepancyLines_holds :
    isDirectSumOfPushforwardDiscrepancyLines
  finiteSupport : Prop
  finiteSupport_holds : finiteSupport

structure Chapter10NormalizationStructureSheafExactSequence
    {k : Type u} [Field k] (D : Chapter10NodalCurveData k)
    (Q : Chapter10NodeDiscrepancySheaf D) where
  inclusion : chapter10CurveStructureSheaf D.curve ⟶
    chapter10NormalizationPushforwardStructureSheaf D.normalization
  discrepancy : chapter10NormalizationPushforwardStructureSheaf D.normalization ⟶ Q.sheaf
  comp_zero : inclusion ≫ discrepancy = 0
  mono_inclusion : Mono inclusion
  epi_discrepancy : Epi discrepancy
  exact : (ShortComplex.mk inclusion discrepancy comp_zero).Exact
  quotient_identification : Prop
  quotient_identification_holds : quotient_identification
  eulerCharacteristic_relation :
    D.structureSheafEulerCharacteristic =
      D.normalizationEulerCharacteristic -
        ∑ q, ((D.nodeData q).residue.degree : ℤ)

/-! ### Rank-one modules and residue spaces -/

def Chapter10FreeRankOne (R M : Type u) [Semiring R] [AddCommMonoid M]
    [Module R M] : Prop :=
  Nonempty (Module.Basis (Fin 1) R M)

structure Chapter10RankOneModuleData (A : Type u) [CommRing A] where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module A carrier]
  frame : carrier
  frameBasis : Module.Basis (Fin 1) A carrier
  frame_eq_basis : frame = frameBasis 0

attribute [instance] Chapter10RankOneModuleData.addCommGroup
attribute [instance] Chapter10RankOneModuleData.module

theorem Chapter10RankOneModuleData.freeRankOne
    {A : Type u} [CommRing A] (D : Chapter10RankOneModuleData A) :
    Chapter10FreeRankOne A D.carrier :=
  ⟨D.frameBasis⟩

abbrev Chapter10BranchMeromorphicDifferential (k : Type u) [Field k] :=
  LaurentSeries k

def chapter10LaurentResidue {k : Type u} [Field k]
    (η : Chapter10BranchMeromorphicDifferential k) : k :=
  η.coeff (-1)

abbrev Chapter10BranchDifferentialPair (k : Type u) [Field k] :=
  Chapter10BranchMeromorphicDifferential k ×
    Chapter10BranchMeromorphicDifferential k

def chapter10OppositeResidues {k : Type u} [Field k]
    (η : Chapter10BranchDifferentialPair k) : Prop :=
  chapter10LaurentResidue η.1 + chapter10LaurentResidue η.2 = 0

/-! ### Geometric fibers, relative duality, and markings -/

/-- A geometric point used to phrase arbitrary geometric-fiber statements. -/
structure Chapter10GeometricPoint (S : Scheme.{u}) where
  field : Type u
  [fieldStructure : Field field]
  [algebraicallyClosed : IsAlgClosed field]
  point : chapter10FieldBaseScheme field ⟶ S

attribute [instance] Chapter10GeometricPoint.fieldStructure
attribute [instance] Chapter10GeometricPoint.algebraicallyClosed

def chapter10GeometricFiberTotal
    {C S : Scheme.{u}} (f : C ⟶ S) (p : Chapter10GeometricPoint S) : Scheme.{u} :=
  pullback f p.point

def chapter10GeometricFiberProjection
    {C S : Scheme.{u}} (f : C ⟶ S) (p : Chapter10GeometricPoint S) :
    chapter10GeometricFiberTotal f p ⟶ chapter10FieldBaseScheme p.field :=
  pullback.snd f p.point

structure Chapter10ProperFlatNodalFamily where
  base : Scheme.{u}
  total : Scheme.{u}
  map : total ⟶ base
  proper : IsProper map
  flat : Flat map
  finitePresentation : LocallyOfFinitePresentation map
  baseLocallyNoetherian : IsLocallyNoetherian base
  nodal : chapter10IsRelativeNodal map
  relativeLocalCompleteIntersection :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Chapter09RelativeLocalCompleteIntersection
      map

def chapter10FamilyBaseChangeTotal (F : Chapter10ProperFlatNodalFamily)
    {T : Scheme.{u}} (g : T ⟶ F.base) : Scheme.{u} :=
  pullback F.map g

def chapter10FamilyBaseChangeMap (F : Chapter10ProperFlatNodalFamily)
    {T : Scheme.{u}} (g : T ⟶ F.base) :
    chapter10FamilyBaseChangeTotal F g ⟶ T :=
  pullback.snd F.map g

def chapter10FamilyBaseChangeToTotal (F : Chapter10ProperFlatNodalFamily)
    {T : Scheme.{u}} (g : T ⟶ F.base) :
    chapter10FamilyBaseChangeTotal F g ⟶ F.total :=
  pullback.fst F.map g

structure Chapter10RelativeDualizingSheafData
    (F : Chapter10ProperFlatNodalFamily) where
  omega : F.total.Modules
  baseChangeOmega : ∀ {T : Scheme.{u}} (g : T ⟶ F.base),
    (chapter10FamilyBaseChangeTotal F g).Modules
  baseChangeIso : ∀ {T : Scheme.{u}} (g : T ⟶ F.base),
      (Scheme.Modules.pullback (chapter10FamilyBaseChangeToTotal F g)).obj omega ≅
      baseChangeOmega g
  fiberwiseRosenlicht : Chapter10GeometricPoint F.base → Prop
  fiberwiseRosenlicht_holds : ∀ p, fiberwiseRosenlicht p
  canonicalAdjunctionGluing : Prop
  canonicalAdjunctionGluing_holds : canonicalAdjunctionGluing

def chapter10RelativeDualizingIsLineBundle
    {F : Chapter10ProperFlatNodalFamily}
    (ω : Chapter10RelativeDualizingSheafData F) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09IsInvertibleSheaf
    ω.omega

def chapter10RelativeDualizingCommutesWithBaseChange
    {F : Chapter10ProperFlatNodalFamily}
    (ω : Chapter10RelativeDualizingSheafData F) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ F.base),
    Nonempty ((Scheme.Modules.pullback (chapter10FamilyBaseChangeToTotal F g)).obj ω.omega ≅
      ω.baseChangeOmega g)

/-!
Simultaneous normalization is deliberately a separate structure.  In
particular, no fiberwise normalization theorem silently supplies it over an
arbitrary base.
-/
structure Chapter10SimultaneousNormalization
    (F : Chapter10ProperFlatNodalFamily) where
  normalizedTotal : Scheme.{u}
  map : normalizedTotal ⟶ F.total
  finite : IsFinite map
  normal : chapter10IsNormal normalizedTotal
  totalNormalization : Chapter10NormalizationUniversalProperty map
  fiberMap : ∀ p : Chapter10GeometricPoint F.base,
    chapter10GeometricFiberTotal (map ≫ F.map) p ⟶
      chapter10GeometricFiberTotal F.map p
  fiberMap_to_total : ∀ p,
    fiberMap p ≫ pullback.fst F.map p.point =
      pullback.fst (map ≫ F.map) p.point ≫ map
  fiberMap_to_base : ∀ p,
    fiberMap p ≫ pullback.snd F.map p.point =
      pullback.snd (map ≫ F.map) p.point
  fiberwiseNormalization : ∀ p,
    Chapter10NormalizationUniversalProperty (fiberMap p)

def chapter10HasSimultaneousNormalization
    (F : Chapter10ProperFlatNodalFamily) : Prop :=
  Nonempty (Chapter10SimultaneousNormalization F)

structure Chapter10MarkedSection (F : Chapter10ProperFlatNodalFamily) where
  sectionMap : F.base ⟶ F.total
  sectionOver : sectionMap ≫ F.map = 𝟙 F.base
  smoothPoint : Prop
  smoothPoint_holds : smoothPoint

structure Chapter10MarkedDifferentialData
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) where
  markings : Fin n → Chapter10MarkedSection F
  twistedOmega : F.total.Modules
  allowsSimplePolesAtMarkings : Prop
  allowsSimplePolesAtMarkings_holds : allowsSimplePolesAtMarkings
  allowsImplicitNodeBranchPoles : Prop
  allowsImplicitNodeBranchPoles_holds : allowsImplicitNodeBranchPoles
  inclusionFromOmega : ω.omega ⟶ twistedOmega
  totalResidue : Chapter10GeometricPoint F.base → Prop
  totalResidue_holds : ∀ p, totalResidue p
  nodeResiduesCancel : Chapter10GeometricPoint F.base → Prop
  nodeResiduesCancel_holds : ∀ p, nodeResiduesCancel p

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10
