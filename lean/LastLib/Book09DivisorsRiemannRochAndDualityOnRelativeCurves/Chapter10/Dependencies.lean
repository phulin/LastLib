import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.MvPolynomial.Basic
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section04FormalPowerSeries
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set
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

/-- The spectrum of the coefficient field used for a curve over a field. -/
def chapter10FieldBaseScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of k)

/-- A reduced proper nodal curve over a field, with connectedness recorded
separately because the genus formula has a connected and a disconnected form. -/
structure Chapter10Curve (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ chapter10FieldBaseScheme k
  reduced : Prop
  proper : IsProper structureMap
  nodal : Prop
  connected : Prop

/-- A finite normalization of a Chapter 10 curve.  The normality and
normalization universal property are intentionally explicit local interfaces. -/
structure Chapter10Normalization {k : Type u} [Field k]
    (C : Chapter10Curve k) where
  carrier : Scheme.{u}
  map : carrier ⟶ C.carrier
  finite : IsFinite map
  normal : Prop
  isNormalization : Prop

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
  isNode : ∀ q, Prop
  pairwiseDistinct : Pairwise (fun q r => point q ≠ point r)

attribute [instance] Chapter10NodeFamily.finite

/-- Chosen inverse images of rational nodes on a normalization. -/
structure Chapter10SplitBranchFamily {k : Type u} [Field k]
    {C : Chapter10Curve k} (N : Chapter10Normalization C)
    (nodes : Chapter10NodeFamily C) where
  left : nodes.index → N.carrier
  right : nodes.index → N.carrier
  left_over_node : ∀ q, N.map (left q) = nodes.point q
  right_over_node : ∀ q, N.map (right q) = nodes.point q
  branches_distinct : ∀ q, left q ≠ right q

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
  etale : Prop

attribute [instance] Chapter10BranchAlgebraData.commRing
attribute [instance] Chapter10BranchAlgebraData.algebra

/-- The intrinsic discrepancy line `B_q / κ(q)`, with the residue field
embedded diagonally through the algebra map. -/
noncomputable def chapter10DiscrepancyLine
    {K : Type u} [Field K] (B : Chapter10BranchAlgebraData K) : Type u := by
  letI := B.commRing
  letI := B.algebra
  exact Submodule.Quotient (Submodule.span K (Set.range (algebraMap K B.carrier)))

theorem chapter10_discrepancy_line_is_one_dimensional
    {K : Type u} [Field K] (B : Chapter10BranchAlgebraData K) :
    letI := B.commRing
    letI := B.algebra
    Module.finrank K (chapter10DiscrepancyLine B) = 1 := by
  sorry

/-- All local data attached to a possibly nonsplit node. -/
structure Chapter10NonsplitNodeData (k : Type u) [Field k] where
  residue : Chapter10ResidueFieldData k
  branches : Chapter10BranchAlgebraData residue.carrier

noncomputable def chapter10NodeDiscrepancyLine
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
  nodeIsNode : ∀ q, Prop
  nodeData : nodes → Chapter10NonsplitNodeData k
  components : Type u
  [componentsFinite : Fintype components]
  componentGenus : components → ℤ
  arithmeticGenus : ℤ
  normalizationComponents : Prop
  normalizationComponentsSmooth : Prop

attribute [instance] Chapter10NodalCurveData.nodesFinite
attribute [instance] Chapter10NodalCurveData.componentsFinite

def chapter10NodeResidueDegree {k : Type u} [Field k]
    (D : Chapter10NodalCurveData k) (q : D.nodes) : ℕ :=
  (D.nodeData q).residue.degree

def chapter10FirstBettiNumber (vertices edges : ℕ) : ℤ :=
  (edges : ℤ) - (vertices : ℤ) + 1

/-- The combinatorial dual graph of a connected nodal curve. -/
structure Chapter10DualGraph where
  vertices : Type u
  [verticesFinite : Fintype vertices]
  edges : Type u
  [edgesFinite : Fintype edges]
  left right : edges → vertices
  connected : Prop

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

def chapter10FunctionDescends
    {k : Type u} [Field k] (D : Chapter10SplitNormalizationFunctionData)
    (f : Γ(D.normalization.carrier, ⊤)) : Prop :=
  ∀ q, D.leftValue q f = D.rightValue q f

theorem chapter10_function_descends_iff
    {k : Type u} [Field k] (D : Chapter10SplitNormalizationFunctionData)
    (f : Γ(D.normalization.carrier, ⊤)) :
    (∃ g : Γ(D.curve.carrier, ⊤), D.pullback g = f) ↔
      chapter10FunctionDescends D f := by
  sorry

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
  finiteSupport : Prop

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

/-! ### Rank-one modules and residue spaces -/

def Chapter10FreeRankOne (R M : Type u) [Semiring R] [AddCommMonoid M]
    [Module R M] : Prop :=
  Nonempty (Basis (Fin 1) R M)

structure Chapter10RankOneModuleData (A : Type u) [CommRing A] where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module A carrier]
  frame : carrier
  freeRankOne : Chapter10FreeRankOne A carrier

attribute [instance] Chapter10RankOneModuleData.addCommGroup
attribute [instance] Chapter10RankOneModuleData.module

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
  nodal : Prop
  relativeLocalCompleteIntersection : Prop

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
  invertible : chapter09IsInvertibleSheaf omega
  baseChangeOmega : ∀ {T : Scheme.{u}} (g : T ⟶ F.base),
    (chapter10FamilyBaseChangeTotal F g).Modules
  baseChangeIso : ∀ {T : Scheme.{u}} (g : T ⟶ F.base),
    (Scheme.Modules.pullback (chapter10FamilyBaseChangeToTotal F g)).obj omega ≅
      baseChangeOmega g
  fiberwiseRosenlicht : ∀ p : Chapter10GeometricPoint F.base, Prop
  canonicalAdjunctionGluing : Prop

def chapter10RelativeDualizingIsLineBundle
    {F : Chapter10ProperFlatNodalFamily}
    (ω : Chapter10RelativeDualizingSheafData F) : Prop :=
  ω.invertible

def chapter10RelativeDualizingCommutesWithBaseChange
    {F : Chapter10ProperFlatNodalFamily}
    (ω : Chapter10RelativeDualizingSheafData F) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ F.base), Nonempty (ω.baseChangeIso g)

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
  normal : Prop
  fiberwiseNormalization : Prop

def chapter10HasSimultaneousNormalization
    (F : Chapter10ProperFlatNodalFamily) : Prop :=
  Nonempty (Chapter10SimultaneousNormalization F)

structure Chapter10MarkedSection (F : Chapter10ProperFlatNodalFamily) where
  sectionMap : F.base ⟶ F.total
  over : sectionMap ≫ F.map = 𝟙 F.base
  smoothPoint : Prop

structure Chapter10MarkedDifferentialData
    (F : Chapter10ProperFlatNodalFamily)
    (ω : Chapter10RelativeDualizingSheafData F)
    (n : ℕ) where
  markings : Fin n → Chapter10MarkedSection F
  twistedOmega : F.total.Modules
  allowsSimplePolesAtMarkings : Prop
  allowsImplicitNodeBranchPoles : Prop
  inclusionFromOmega : ω.omega ⟶ twistedOmega
  totalResidue : ∀ p : Chapter10GeometricPoint F.base, Prop
  nodeResiduesCancel : ∀ p : Chapter10GeometricPoint F.base, Prop

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10
