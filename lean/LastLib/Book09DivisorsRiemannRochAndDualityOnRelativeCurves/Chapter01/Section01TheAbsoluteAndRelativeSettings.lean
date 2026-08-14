import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.KrullDimension
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry

universe u v

/-! ### The absolute and relative settings -/

/- The definition is deliberately expressed using the topological Krull dimension of
  every irreducible component.  This keeps ``pure dimension one`` independent of a
  choice of generic points and makes it usable for geometric fibers. -/
def Chapter01PureDimensionOne : ObjectProperty Scheme.{u} :=
  fun X => ∀ Z : irreducibleComponents X,
    topologicalKrullDim Z.1 = (1 : WithBot ℕ∞)

def Chapter01GeometricallyPureDimensionOne {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  geometrically Chapter01PureDimensionOne f

/-! A proper curve over a field is kept as a structured object so that the map to
  ``Spec k`` is never lost when passing to cohomology or residue fields. -/
structure Chapter01ProperCurveOverField (k : Type u) [Field k] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (CommRingCat.of k)
  proper : IsProper structureMap
  finiteType : LocallyOfFiniteType structureMap
  pureDimensionOne : Chapter01PureDimensionOne carrier

namespace Chapter01ProperCurveOverField

instance (C : Chapter01ProperCurveOverField k) : IsProper C.structureMap := C.proper

instance (C : Chapter01ProperCurveOverField k) : LocallyOfFiniteType C.structureMap := C.finiteType

end Chapter01ProperCurveOverField

/-! A relative curve uses the canonical scheme-morphism properties.  In particular,
  ``finitePresentation`` is not replaced by finite type, and geometric fibers are
  tested after arbitrary field-valued base change. -/
class Chapter01RelativeCurve {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  proper : IsProper f
  flat : Flat f
  finitePresentation : LocallyOfFinitePresentation f
  geometricFibersPureDimensionOne : Chapter01GeometricallyPureDimensionOne f

namespace Chapter01RelativeCurve

instance (f : X ⟶ S) [Chapter01RelativeCurve f] : IsProper f :=
  Chapter01RelativeCurve.proper f

instance (f : X ⟶ S) [Chapter01RelativeCurve f] : Flat f :=
  Chapter01RelativeCurve.flat f

instance (f : X ⟶ S) [Chapter01RelativeCurve f] : LocallyOfFinitePresentation f :=
  Chapter01RelativeCurve.finitePresentation f

end Chapter01RelativeCurve

class Chapter01SmoothRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S)
    extends Chapter01RelativeCurve f : Prop where
  smooth : Smooth f
  relativeDimensionOne : SmoothOfRelativeDimension 1 f

namespace Chapter01SmoothRelativeCurve

instance (f : X ⟶ S) [Chapter01SmoothRelativeCurve f] : Smooth f :=
  Chapter01SmoothRelativeCurve.smooth f

instance (f : X ⟶ S) [Chapter01SmoothRelativeCurve f] :
    SmoothOfRelativeDimension 1 f :=
  Chapter01SmoothRelativeCurve.relativeDimensionOne f

end Chapter01SmoothRelativeCurve

/-! The base-change operation used in the standing notation ``X_K``. -/
abbrev chapter01BaseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : Scheme.{u} :=
  pullback f g

def chapter01PointHasSectionExtension {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ (U : S.Opens) (hU : f x ∈ U)
    (σ : U ⟶ (f ⁻¹ᵁ U).toScheme),
    σ ≫ (f ∣_ U) = 𝟙 U ∧
      σ ⟨f x, hU⟩ = ⟨x, hU⟩

def chapter01PointNeedNotExtendToGlobalSection {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ x : X, ¬ chapter01PointHasSectionExtension f x

abbrev chapter01FieldBaseChange {k K : Type u} [Field k] [Field K]
    (X : Scheme.{u}) (structureMap : X ⟶ Spec (CommRingCat.of k)) (φ : k →+* K) : Scheme.{u} :=
  chapter01BaseChange structureMap (Spec.map (CommRingCat.ofHom φ))

theorem chapter01_relativeCurve_baseChange
    {X S T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    [Chapter01RelativeCurve f] : Chapter01RelativeCurve (pullback.snd f g) := by
  sorry

/-! The three central bookkeeping types of the chapter.  A Weil divisor is
  represented by Mathlib's locally finite algebraic cycle; later chapters add the
  Cartier and linear-equivalence structures. -/
abbrev Chapter01Divisor (X : Scheme.{u}) := AlgebraicCycle X ℤ

abbrev Chapter01LineBundle (X : Scheme.{u}) := Chapter04LineBundle X

def chapter01RiemannRochFormula (χ degree genus : ℤ) : Prop :=
  χ = degree + 1 - genus

structure Chapter01RiemannRochStatement where
  χ degree genus : ℤ
  formula : chapter01RiemannRochFormula χ degree genus

/-! ### Local orders, units, and residues -/

abbrev Chapter01RationalFunction (X : Scheme.{u}) := X.functionField

noncomputable def chapter01OrderAt
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) : Chapter01RationalFunction X → ℤ :=
  fun f => Scheme.ord f x

def chapter01ExceptionalPoints
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : Chapter01RationalFunction X) : Set X :=
    {x | chapter01OrderAt x f ≠ 0}

def chapter01ClosedPoint (X : Scheme.{u}) (x : X) : Prop :=
  IsClosed ({x} : Set X)

def chapter01OrderZeroAt
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : Chapter01RationalFunction X) (x : X) : Prop :=
  chapter01OrderAt x f = 0

def chapter01HasZeroAt
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : Chapter01RationalFunction X) (x : X) : Prop :=
  0 < chapter01OrderAt x f

def chapter01HasPoleAt
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : Chapter01RationalFunction X) (x : X) : Prop :=
  chapter01OrderAt x f < 0

theorem chapter01_order_add
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f g : Chapter01RationalFunction X) (hf : f ≠ 0) (hg : g ≠ 0) (x : X) :
    chapter01OrderAt x (f * g) = chapter01OrderAt x f + chapter01OrderAt x g := by
  exact Scheme.ord_mul hf hg

theorem chapter01_order_of_unit
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {U : X.Opens} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f)
    {x : X} (hx : x ∈ U) :
    chapter01OrderAt x (X.germToFunctionField U f) = 0 := by
  exact Scheme.ord_of_isUnit hf hx

theorem chapter01_exceptionalPoints_finite
    {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k)
    [IsIntegral C.carrier] [IsLocallyNoetherian C.carrier]
    (f : Chapter01RationalFunction C.carrier) (hf : f ≠ 0) :
    (chapter01ExceptionalPoints f).Finite := by
  sorry

/- A local parameter is a generator of the maximal ideal in a one-dimensional
  local domain.  The condition is explicit so that normalization of valuations is
  not hidden in a later theorem. -/
def chapter01LocalParameter {R : Type u} [CommRing R] [IsLocalRing R]
    (t : R) : Prop :=
  Irreducible t ∧ Ideal.span ({t} : Set R) = maximalIdeal R

structure Chapter01ResidueTheory (R K : Type u) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra R K] where
  Differential : Type u
  addCommGroup : AddCommGroup Differential
  module : Module R Differential
  residue : ∀ (t : R), chapter01LocalParameter t → Differential → K
  parameterInvariant :
    ∀ (t u : R) (ht : chapter01LocalParameter t) (hu : chapter01LocalParameter u)
      (ω : Differential),
      residue t ht ω = residue u hu ω

theorem chapter01_residue_parameter_invariant
    {R K : Type u} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    (T : Chapter01ResidueTheory R K) (t u : R)
    (ht : chapter01LocalParameter t) (hu : chapter01LocalParameter u)
    (ω : T.Differential) :
    T.residue t ht ω = T.residue u hu ω := by
  exact T.parameterInvariant t u ht hu ω

/-! ### Relative length, Euler characteristic, and nodal specialization -/

structure Chapter01FiniteFlatLengthFamily {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) where
  subscheme : Scheme.{u}
  inclusion : subscheme ⟶ X
  closedImmersion : IsClosedImmersion inclusion
  projection : subscheme ⟶ S
  over : inclusion ≫ f = projection
  finite : IsFinite projection
  flat : Flat projection
  finitePresentation : LocallyOfFinitePresentation projection
  constantLength : ∀ s : S, projection.finrank s = d

def chapter01FiniteFlatLengthCollision
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (Z : Chapter01FiniteFlatLengthFamily f d) : Prop :=
  ∃ z₁ z₂ : Z.subscheme, z₁ ≠ z₂ ∧ Z.inclusion z₁ = Z.inclusion z₂

def chapter01FiniteFlatLengthCanCollide {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ d : ℕ, ∃ Z : Chapter01FiniteFlatLengthFamily f d,
    chapter01FiniteFlatLengthCollision Z

def chapter01FiniteFlatLengthCanBeNonreduced {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ d : ℕ, ∃ Z : Chapter01FiniteFlatLengthFamily f d, ¬ IsReduced Z.subscheme

def chapter01DualNumberScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (DualNumber k))

def chapter01DualNumberIsNonreduced (k : Type u) [Field k] : Prop :=
  ¬ IsReduced (chapter01DualNumberScheme k)

def chapter01DualNumberLengthTwo (k : Type u) [Field k] : Prop :=
  Module.finrank k (DualNumber k) = 2

theorem chapter01_dualNumber_is_nonreduced
    (k : Type u) [Field k] : chapter01DualNumberIsNonreduced k := by
  sorry

theorem chapter01_dualNumber_has_length_two
    (k : Type u) [Field k] : chapter01DualNumberLengthTwo k := by
  sorry

namespace Chapter01FiniteFlatLengthFamily

instance (Z : Chapter01FiniteFlatLengthFamily f d) : IsFinite Z.projection := Z.finite

instance (Z : Chapter01FiniteFlatLengthFamily f d) : Flat Z.projection := Z.flat

instance (Z : Chapter01FiniteFlatLengthFamily f d) :
    LocallyOfFinitePresentation Z.projection := Z.finitePresentation

def degree (Z : Chapter01FiniteFlatLengthFamily f d) (s : S) : ℕ :=
  Z.projection.finrank s

theorem degree_eq_length (Z : Chapter01FiniteFlatLengthFamily f d) (s : S) :
    Z.degree s = d := by
  exact Z.constantLength s

theorem degree_isLocallyConstant (Z : Chapter01FiniteFlatLengthFamily f d) :
    IsLocallyConstant Z.degree := by
  sorry

theorem degree_constant_of_connected_base
    (Z : Chapter01FiniteFlatLengthFamily f d) [ConnectedSpace S] :
    ∀ s t : S, Z.degree s = Z.degree t := by
  sorry

end Chapter01FiniteFlatLengthFamily

def chapter01EulerCharacteristic (h₀ h₁ : ℕ) : ℤ :=
  (h₀ : ℤ) - h₁

def chapter01FiberEulerCharacteristic {S : Type u} (h₀ h₁ : S → ℕ) (s : S) : ℤ :=
  chapter01EulerCharacteristic (h₀ s) (h₁ s)

theorem chapter01EulerCharacteristic_eq_difference (h₀ h₁ : ℕ) :
    chapter01EulerCharacteristic h₀ h₁ = (h₀ : ℤ) - h₁ := by
  rfl

structure Chapter01EulerCharacteristicProfile (S : Type u) where
  h₀ : S → ℕ
  h₁ : S → ℕ
  χ : S → ℤ
  formula : ∀ s, χ s = chapter01FiberEulerCharacteristic h₀ h₁ s
  locallyConstant : IsLocallyConstant χ

def chapter01HasTorsion {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ m : M, m ≠ 0 ∧ ∃ r : R, r ≠ 0 ∧ r • m = 0

structure Chapter01DifferentialComparison (R : Type u) [CommRing R] where
  ordinary : Type u
  [ordinaryAddCommGroup : AddCommGroup ordinary]
  [ordinaryModule : Module R ordinary]
  duality : Type u
  [dualityAddCommGroup : AddCommGroup duality]
  [dualityModule : Module R duality]
  ordinaryHasTorsion : chapter01HasTorsion R ordinary
  dualityWellBehaved : Module.Invertible R duality

structure Chapter01ResidueDualityInterface (R K : Type u) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra R K] where
  residues : Chapter01ResidueTheory R K
  comparison : Chapter01DifferentialComparison R
  pairing : residues.Differential → comparison.duality → K
  leftNondegenerate :
    ∀ ω, (∀ η, pairing ω η = 0) → ω = 0
  rightNondegenerate :
    ∀ η, (∀ ω, pairing ω η = 0) → η = 0

def chapter01NodeRing (k : Type u) [Field k] : Type u :=
  MvPowerSeries (Fin 2) k ⧸
    Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) k))

def chapter01NodeDifferentials (k : Type u) [Field k] : Type u :=
  Ω[chapter01NodeRing k⁄k]

def chapter01NodeOrdinaryDifferentialsHaveTorsion (k : Type u) [Field k] : Prop :=
  chapter01HasTorsion k (chapter01NodeDifferentials k)

theorem chapter01_node_ordinary_differentials_have_torsion
    (k : Type u) [Field k] : chapter01NodeOrdinaryDifferentialsHaveTorsion k := by
  sorry

def chapter01NodalDifferentialComparison (k : Type u) [Field k] : Prop :=
  ∃ D : Chapter01DifferentialComparison (chapter01NodeRing k),
    Nonempty (D.ordinary ≃+ chapter01NodeDifferentials k)

theorem chapter01_nodal_differential_comparison
    (k : Type u) [Field k] : chapter01NodalDifferentialComparison k := by
  sorry

/-! The completed local model is the usual node ``k[[u,v]]/(uv)``.  This local
  definition is used only as the node predicate; the later duality chapters supply
  the canonical relative dualizing module. -/
def chapter01CompletedLocalRing (X : Scheme.{u}) (x : X) : Type u :=
  AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

def chapter01NodeRingAt (X : Scheme.{u}) (x : X) : Type u :=
  chapter01NodeRing (X.residueField x)

def chapter01OrdinaryDoublePointAt (X : Scheme.{u}) (x : X) : Prop :=
  Nonempty (chapter01CompletedLocalRing X x ≃+* chapter01NodeRingAt X x)

def chapter01RegularPoint (X : Scheme.{u}) (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x)

def chapter01NodalScheme (X : Scheme.{u}) : Prop :=
  IsReduced X ∧ ∀ x : X, chapter01RegularPoint X x ∨ chapter01OrdinaryDoublePointAt X x

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib snapshot has no named Gorenstein
  scheme-morphism property.  The injective-dimension characterization below is
  the standard noetherian-local replacement and is used only as a hypothesis. -/
def chapter01GorensteinLocalRing (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  injectiveDimension (ModuleCat.of R R) = ringKrullDim R

def chapter01GorensteinMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ x : X, chapter01GorensteinLocalRing (X.presheaf.stalk x)

class Chapter01NodalRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S)
    extends Chapter01RelativeCurve f : Prop where
  geometricFibersNodal :
    geometrically (fun Y : Scheme.{u} => chapter01NodalScheme Y) f

class Chapter01GorensteinNodalRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S)
    extends Chapter01NodalRelativeCurve f : Prop where
  gorenstein : chapter01GorensteinMorphism f

def chapter01LocallyCutOutByOneEquationInSmoothSurface
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (i : X ⟶ Y),
    SmoothOfRelativeDimension 2 g ∧ IsClosedImmersion i ∧ i ≫ g = f ∧
      ∀ x : X, ∃ a : Y.presheaf.stalk (i x),
        Nonempty (Y.presheaf.stalk (i x) ⧸ Ideal.span ({a} : Set _) ≃+*
          X.presheaf.stalk x)

structure Chapter01StandardNodalHypersurface {X S : Scheme.{u}} (f : X ⟶ S) where
  nodal : Chapter01NodalRelativeCurve f
  baseLocallyNoetherian : IsLocallyNoetherian S
  smoothSurfaceLocalModel : chapter01LocallyCutOutByOneEquationInSmoothSurface f

theorem chapter01_standard_nodal_hypersurface_is_gorenstein
    {X S : Scheme.{u}} {f : X ⟶ S}
    (H : Chapter01StandardNodalHypersurface f) : chapter01GorensteinMorphism f := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the assigned chapter precedes the full Cartier-divisor
  implementation, so this interface records the divisor-to-line-bundle map and
  principal-triviality compatibility without inventing a second Cartier API. -/
/-! The small dictionary announced in the introduction is intentionally a
  formula-level interface.  Divisor/line-bundle equivalences and residue pairings
  are constructed with their precise hypotheses in later chapters. -/
structure Chapter01DivisorLineBundleInterface (X : Scheme.{u}) where
  divisorToLineBundle : Chapter01Divisor X → Chapter01LineBundle X
  principalDivisor : Chapter01RationalFunction X → Chapter01Divisor X
  principalToTrivial :
    ∀ f, divisorToLineBundle (principalDivisor f) = chapter04TrivialLineBundle X

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
