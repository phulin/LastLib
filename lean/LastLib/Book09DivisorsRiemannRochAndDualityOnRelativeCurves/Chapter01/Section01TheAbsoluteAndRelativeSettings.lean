import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
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
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.KrullDimension
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry
attribute [local instance] DiscreteTopology.instContinuousSMul

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
  quasiCompact : QuasiCompact structureMap
  finiteType : LocallyOfFiniteType structureMap
  pureDimensionOne : Chapter01PureDimensionOne carrier

namespace Chapter01ProperCurveOverField

instance {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k) :
    IsProper C.structureMap := C.proper

instance {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k) :
    LocallyOfFiniteType C.structureMap := C.finiteType

instance {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k) :
    QuasiCompact C.structureMap := C.quasiCompact

end Chapter01ProperCurveOverField

/-! A relative curve uses the canonical scheme-morphism properties.  In particular,
  ``finitePresentation`` is not replaced by finite type, and geometric fibers are
  tested after arbitrary field-valued base change. -/
class Chapter01RelativeCurve {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  proper : IsProper f
  quasiCompact : QuasiCompact f
  flat : Flat f
  finitePresentation : LocallyOfFinitePresentation f
  geometricFibersPureDimensionOne : Chapter01GeometricallyPureDimensionOne f

namespace Chapter01RelativeCurve

instance (f : X ⟶ S) [Chapter01RelativeCurve f] : IsProper f :=
  Chapter01RelativeCurve.proper (f := f)

instance (f : X ⟶ S) [Chapter01RelativeCurve f] : Flat f :=
  Chapter01RelativeCurve.flat (f := f)

instance (f : X ⟶ S) [Chapter01RelativeCurve f] : QuasiCompact f :=
  Chapter01RelativeCurve.quasiCompact (f := f)

instance (f : X ⟶ S) [Chapter01RelativeCurve f] : LocallyOfFinitePresentation f :=
  Chapter01RelativeCurve.finitePresentation (f := f)

end Chapter01RelativeCurve

class Chapter01SmoothRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S)
    : Prop extends Chapter01RelativeCurve f where
  smooth : Smooth f
  relativeDimensionOne : SmoothOfRelativeDimension 1 f

namespace Chapter01SmoothRelativeCurve

instance (f : X ⟶ S) [Chapter01SmoothRelativeCurve f] : Smooth f :=
  Chapter01SmoothRelativeCurve.smooth (f := f)

instance (f : X ⟶ S) [Chapter01SmoothRelativeCurve f] :
    SmoothOfRelativeDimension 1 f :=
  Chapter01SmoothRelativeCurve.relativeDimensionOne (f := f)

end Chapter01SmoothRelativeCurve

/-! The base-change operation used in the standing notation ``X_K``. -/
abbrev chapter01BaseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : Scheme.{u} :=
  pullback f g

def chapter01PointHasSectionExtension {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ (U : S.Opens) (hU : f x ∈ U)
    (σ : U.toScheme ⟶ (f ⁻¹ᵁ U).toScheme),
    σ ≫ (f ∣_ U) = 𝟙 (U.toScheme) ∧
      σ ⟨f x, hU⟩ = ⟨x, hU⟩

def chapter01PointHasGlobalSectionExtension {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ (σ : S ⟶ X), σ ≫ f = 𝟙 S ∧ σ (f x) = x

def chapter01PointNeedNotExtendToGlobalSection {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ x : X, ¬ chapter01PointHasGlobalSectionExtension f x

abbrev chapter01FieldBaseChange {k K : Type u} [Field k] [Field K]
    (X : Scheme.{u}) (structureMap : X ⟶ Spec (CommRingCat.of k)) (φ : k →+* K) : Scheme.{u} :=
  chapter01BaseChange structureMap (Spec.map (CommRingCat.ofHom φ))

theorem chapter01_relativeCurve_baseChange
    {X S T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    [Chapter01RelativeCurve f] : Chapter01RelativeCurve (pullback.snd f g) := by
  refine { proper := by infer_instance, quasiCompact := by infer_instance, flat := by infer_instance, finitePresentation := by infer_instance, geometricFibersPureDimensionOne := ?_ }
  exact (geometrically Chapter01PureDimensionOne).pullback_snd f g
    (Chapter01RelativeCurve.geometricFibersPureDimensionOne (f := f))

/-! The three central bookkeeping types of the chapter.  A Weil divisor is a
  finite codimension-one cycle; later chapters add the Cartier and
  linear-equivalence structures. -/
structure Chapter01Divisor (X : Scheme.{u}) where
  coefficient : X → ℤ
  finiteSupport : Set.Finite {x | coefficient x ≠ 0}
  codimensionOne : ∀ x, coefficient x ≠ 0 → Order.coheight x = 1

instance (X : Scheme.{u}) : CoeFun (Chapter01Divisor X) (fun _ => X → ℤ) :=
  ⟨Chapter01Divisor.coefficient⟩

abbrev Chapter01LineBundle (X : Scheme.{u}) := Chapter04LineBundle X

def chapter01RiemannRochFormula (χ degree genus : ℤ) : Prop :=
  χ = degree + 1 - genus

structure Chapter01RiemannRochStatement where
  χ : ℤ
  degree : ℤ
  genus : ℤ
  formula : chapter01RiemannRochFormula χ degree genus

/-! ### Local orders, units, and residues -/

abbrev Chapter01RationalFunction (X : Scheme.{u}) [IsIntegral X] := X.functionField

abbrev Chapter01RationalFunctionUnit (X : Scheme.{u}) [IsIntegral X] :=
  (Chapter01RationalFunction X)ˣ

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

/-! A line bundle is used below only up to isomorphism.  Quotienting the
    book-facing representatives here avoids confusing equality of chosen
    sheaves with the Picard equivalence relation. -/
def chapter01LineBundleEquivalent {X : Scheme.{u}}
    (L M : Chapter01LineBundle X) : Prop :=
  Nonempty (L.sheaf ≅ M.sheaf)

instance chapter01LineBundleEquivalentSetoid (X : Scheme.{u}) :
    Setoid (Chapter01LineBundle X) where
  r := chapter01LineBundleEquivalent
  iseqv := by
    constructor
    · intro L
      exact ⟨Iso.refl L.sheaf⟩
    · intro L M h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    · intro L M N hLM hMN
      rcases hLM with ⟨e⟩
      rcases hMN with ⟨f⟩
      exact ⟨e ≪≫ f⟩

abbrev Chapter01LineBundleClass (X : Scheme.{u}) :=
  Quotient (chapter01LineBundleEquivalentSetoid X)

def chapter01LineBundleClassMk {X : Scheme.{u}} (L : Chapter01LineBundle X) :
    Chapter01LineBundleClass X :=
  Quotient.mk _ L

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
  classical
  let _ : CompactSpace C.carrier :=
    compactSpace_of_universallyClosed C.structureMap
  let _ : IsNoetherian C.carrier := ⟨⟩
  obtain ⟨U, hU, g, hNU, hgf, hg⟩ :=
    AlgebraicGeometry.exists_isUnit_germ_eq C.carrier f hf
  have hsubset : chapter01ExceptionalPoints f ⊆ (↑U : Set C.carrier)ᶜ := by
    intro x hx
    change chapter01OrderAt x f ≠ 0 at hx
    rw [Set.mem_compl_iff]
    intro hxU
    apply hx
    rw [← hgf]
    exact chapter01_order_of_unit hg hxU
  have hdim : topologicalKrullDim C.carrier = 1 := by
    have hZ := C.pureDimensionOne
      (⟨(Set.univ : Set C.carrier), by
        simp [irreducibleComponents_eq_singleton]⟩ :
        irreducibleComponents C.carrier)
    have heq : topologicalKrullDim (Set.univ : Set C.carrier) =
        topologicalKrullDim C.carrier :=
      IsHomeomorph.topologicalKrullDim_eq _
        (Homeomorph.Set.univ C.carrier).isHomeomorph
    rw [← heq]
    exact hZ
  have hfinite : (↑U : Set C.carrier)ᶜ.Finite := by
    obtain ⟨S, hSf, hSclosed, hSirred, hEq⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
        (α := C.carrier) (isClosed_compl_iff.mpr U.isOpen)
    have hdim_le :
        Order.krullDim (TopologicalSpace.IrreducibleCloseds C.carrier) ≤ 1 := by
      change topologicalKrullDim C.carrier ≤ 1
      rw [hdim]
    let _ : OrderTop (TopologicalSpace.IrreducibleCloseds C.carrier) :=
      { top :=
          ⟨Set.univ, IrreducibleSpace.isIrreducible_univ C.carrier, isClosed_univ⟩
        le_top := fun _ => Set.subset_univ _ }
    have hmin :=
      (Order.krullDim_le_one_iff_forall_isMin
        (α := TopologicalSpace.IrreducibleCloseds C.carrier)).mp hdim_le
    rw [hEq]
    apply hSf.sUnion
    intro T hT
    have hTsub : T ⊆ (↑U : Set C.carrier)ᶜ := by
      rw [hEq]
      exact Set.subset_sUnion_of_mem hT
    have hTne : T ≠ (Set.univ : Set C.carrier) := by
      intro hTuniv
      obtain ⟨u, hu⟩ := hNU
      have huT : (u : C.carrier) ∈ T := hTuniv ▸ Set.mem_univ _
      exact (hTsub huT) hu
    let t : TopologicalSpace.IrreducibleCloseds C.carrier :=
      ⟨T, hSirred T hT, hSclosed T hT⟩
    have htne : t ≠ ⊤ := by
      intro ht
      apply hTne
      exact congrArg (fun q : TopologicalSpace.IrreducibleCloseds C.carrier =>
        (q : Set C.carrier)) ht
    have htmin : IsMin t := hmin t htne
    let z : C.carrier := (hSirred T hT).genericPoint
    have hzT : IsGenericPoint z T :=
      (hSirred T hT).isGenericPoint_genericPoint (hSclosed T hT)
    have hTsingle : T = ({z} : Set C.carrier) := by
      ext y
      constructor
      · intro hy
        let c : TopologicalSpace.IrreducibleCloseds C.carrier :=
          ⟨closure ({y} : Set C.carrier), isIrreducible_singleton.closure,
            isClosed_closure⟩
        have hcy : c ≤ t := closure_minimal (Set.singleton_subset_iff.mpr hy)
          (hSclosed T hT)
        have htc : t = c := htmin.eq_of_ge hcy
        have hclosure : closure ({y} : Set C.carrier) = T := by
          exact (congrArg
            (fun q : TopologicalSpace.IrreducibleCloseds C.carrier =>
              (q : Set C.carrier)) htc).symm
        have hygen : IsGenericPoint y T := hclosure
        simpa using (hzT.eq hygen).symm
      · intro hy
        have : y = z := by simpa using hy
        subst y
        exact hzT.mem
    rw [hTsingle]
    exact Set.finite_singleton z
  exact hfinite.subset hsubset

/- A local parameter is a generator of the maximal ideal in a one-dimensional
  local domain.  The condition is explicit so that normalization of valuations is
  not hidden in a later theorem. -/
def chapter01LocalParameter {R : Type u} [CommRing R] [IsLocalRing R]
    (t : R) : Prop :=
  IsDomain R ∧ Irreducible t ∧
    Ideal.span ({t} : Set R) = IsLocalRing.maximalIdeal R

structure Chapter01ResidueTheory (R K : Type u) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra R K] where
  Differential : Type u
  [addCommGroup : AddCommGroup Differential]
  [module : Module R Differential]
  residue : ∀ (t : R), chapter01LocalParameter t → Differential → K
  parameterInvariant :
    ∀ (t u : R) (ht : chapter01LocalParameter t) (hu : chapter01LocalParameter u)
      (ω : Differential),
      residue t ht ω = residue u hu ω
  residue_zero : ∀ (t : R) (ht : chapter01LocalParameter t), residue t ht 0 = 0
  residue_add :
    ∀ (t : R) (ht : chapter01LocalParameter t) (ω η : Differential),
      residue t ht (ω + η) = residue t ht ω + residue t ht η

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
  projection_eq_inclusion_comp : inclusion ≫ f = projection
  finite : IsFinite projection
  flat : Flat projection
  finitePresentation : LocallyOfFinitePresentation projection
  constantLength : ∀ s : S, projection.finrank s = d

def chapter01FiniteFlatLengthCollision
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (Z : Chapter01FiniteFlatLengthFamily f d) : Prop :=
  ∃ s : S, ¬ IsReduced (Z.projection.fiber s)

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
  rw [chapter01DualNumberIsNonreduced, chapter01DualNumberScheme, affine_isReduced_iff]
  intro h
  have hz := h.eq_zero (DualNumber.eps : DualNumber k) (⟨2, DualNumber.eps_pow_two⟩)
  have hs := congrArg TrivSqZeroExt.snd hz
  simp only [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] at hs
  exact one_ne_zero hs

theorem chapter01_dualNumber_has_length_two
    (k : Type u) [Field k] : chapter01DualNumberLengthTwo k := by
  change Module.finrank k (k × k) = 2
  simp [Module.finrank_prod]

namespace Chapter01FiniteFlatLengthFamily

instance {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (Z : Chapter01FiniteFlatLengthFamily f d) : IsFinite Z.projection := Z.finite

instance {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (Z : Chapter01FiniteFlatLengthFamily f d) : Flat Z.projection := Z.flat

instance {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (Z : Chapter01FiniteFlatLengthFamily f d) :
    LocallyOfFinitePresentation Z.projection := Z.finitePresentation

def degree {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (Z : Chapter01FiniteFlatLengthFamily f d) (s : S) : ℕ :=
  Z.projection.finrank s

theorem degree_eq_length {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (Z : Chapter01FiniteFlatLengthFamily f d) (s : S) :
    Z.degree s = d := by
  exact Z.constantLength s

theorem degree_isLocallyConstant {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (Z : Chapter01FiniteFlatLengthFamily f d) :
    IsLocallyConstant Z.degree := by
  exact IsLocallyConstant.of_constant _
    (fun s t => (degree_eq_length Z s).trans (degree_eq_length Z t).symm)

theorem degree_constant_of_connected_base
    {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (Z : Chapter01FiniteFlatLengthFamily f d) [ConnectedSpace S] :
    ∀ s t : S, Z.degree s = Z.degree t := by
  intro s t
  rw [degree_eq_length, degree_eq_length]

end Chapter01FiniteFlatLengthFamily

def chapter01EulerCharacteristic (h₀ h₁ : ℕ) : ℤ :=
  (h₀ : ℤ) - h₁

def chapter01FiberEulerCharacteristic {S : Type u} (h₀ h₁ : S → ℕ) (s : S) : ℤ :=
  chapter01EulerCharacteristic (h₀ s) (h₁ s)

theorem chapter01EulerCharacteristic_eq_difference (h₀ h₁ : ℕ) :
    chapter01EulerCharacteristic h₀ h₁ = (h₀ : ℤ) - h₁ := by
  rfl

structure Chapter01EulerCharacteristicProfile (S : Type u) [TopologicalSpace S] where
  h₀ : S → ℕ
  h₁ : S → ℕ
  χ : S → ℤ
  formula : ∀ s, χ s = chapter01FiberEulerCharacteristic h₀ h₁ s
  locallyConstant : IsLocallyConstant χ

def chapter01HasTorsion {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ m : M, m ≠ 0 ∧ ∃ r : R, r ∈ nonZeroDivisors R ∧ r • m = 0

structure Chapter01DifferentialComparison (R : Type u) [CommRing R] where
  ordinary : Type u
  [ordinaryAddCommGroup : AddCommGroup ordinary]
  [ordinaryModule : Module R ordinary]
  duality : Type u
  [dualityAddCommGroup : AddCommGroup duality]
  [dualityModule : Module R duality]
  ordinaryHasTorsion : chapter01HasTorsion (R := R) (M := ordinary)
  dualityWellBehaved : Module.Invertible R duality

structure Chapter01ResidueDualityInterface (R K : Type u) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra R K] where
  residues : Chapter01ResidueTheory R K
  comparison : Chapter01DifferentialComparison R
  pairing : residues.Differential → comparison.duality → K
  leftNondegenerate :
    letI := residues.addCommGroup
    ∀ ω, (∀ η, pairing ω η = 0) → ω = 0
  rightNondegenerate :
    letI := comparison.dualityAddCommGroup
    ∀ η, (∀ ω, pairing ω η = 0) → η = 0
  pairing_add_left :
    letI := residues.addCommGroup
    ∀ (ω₁ ω₂ : residues.Differential) (η),
      pairing (ω₁ + ω₂) η = pairing ω₁ η + pairing ω₂ η
  pairing_add_right :
    letI := comparison.dualityAddCommGroup
    ∀ (ω) (η₁ η₂),
      pairing ω (η₁ + η₂) = pairing ω η₁ + pairing ω η₂

abbrev chapter01NodeRing (k : Type u) [Field k] : Type u :=
  MvPowerSeries (Fin 2) k ⧸
    Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) k))

abbrev chapter01NodeDifferentials (k : Type u) [Field k] : Type u :=
  Ω[chapter01NodeRing k⁄k]

def chapter01NodeOrdinaryDifferentialsHaveTorsion (k : Type u) [Field k] : Prop :=
  chapter01HasTorsion (R := chapter01NodeRing k) (M := chapter01NodeDifferentials k)

theorem chapter01_node_ordinary_differentials_have_torsion
    (k : Type u) [Field k] : chapter01NodeOrdinaryDifferentialsHaveTorsion k := by
  let _ := (⊥ : UniformSpace k)
  let _ := (⊥ : UniformSpace (DualNumber k))
  have hε : MvPowerSeries.HasEval (fun _ : Fin 2 => (DualNumber.eps : DualNumber k)) := by
    constructor
    intro i
    exact IsNilpotent.isTopologicallyNilpotent ⟨2, DualNumber.eps_pow_two⟩
    simpa only [Filter.cofinite_eq_bot] using
      (Filter.tendsto_bot :
        Filter.Tendsto (fun _ : Fin 2 => (DualNumber.eps : DualNumber k)) ⊥ (nhds 0))
  let q : MvPowerSeries (Fin 2) k →+* DualNumber k :=
    MvPowerSeries.eval₂Hom (φ := algebraMap k (DualNumber k))
      (a := fun _ : Fin 2 => (DualNumber.eps : DualNumber k))
      (continuous_algebraMap k (DualNumber k)) hε
  have qX0 : q (MvPowerSeries.X 0) = DualNumber.eps := by
    dsimp [q]
    rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]
  have qX1 : q (MvPowerSeries.X 1) = DualNumber.eps := by
    dsimp [q]
    rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]
  have heps : (DualNumber.eps : DualNumber k) * DualNumber.eps = 0 := by
    simpa only [pow_two] using DualNumber.eps_pow_two
  have hq : ∀ a : MvPowerSeries (Fin 2) k,
      a ∈ Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) k)) →
        q a = 0 := by
    intro a ha
    rcases Ideal.mem_span_singleton'.mp ha with ⟨c, rfl⟩
    simp only [map_mul, qX0, qX1, heps, mul_zero]
  let qbar : chapter01NodeRing k →+* DualNumber k :=
    Ideal.Quotient.lift _ q hq
  have qbarX0 : qbar (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = DualNumber.eps := by
    dsimp [qbar]
    exact qX0
  have qbarX1 : qbar (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = DualNumber.eps := by
    dsimp [qbar]
    exact qX1
  let A := MvPowerSeries (Fin 2) k
  let B := DualNumber k
  let _ : Algebra A B := q.toAlgebra
  let _ : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro r
    change algebraMap k B r = q (algebraMap k A r)
    rw [MvPowerSeries.algebraMap_apply]
    dsimp [q]
    rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C])
  let dA : Derivation k A A := MvPowerSeries.pderiv k 0 - MvPowerSeries.pderiv k 1
  let dB : Derivation k A B := (Algebra.linearMap A B).compDer dA
  have dBX0 : dB (MvPowerSeries.X 0) = 1 := by
    dsimp [dB, dA]
    rw [MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (by decide)]
    simp
  have dBX1 : dB (MvPowerSeries.X 1) = -1 := by
    dsimp [dB, dA]
    rw [MvPowerSeries.pderiv_X_of_ne (by decide), MvPowerSeries.pderiv_X_self]
    simp
  have hdRel : dB (MvPowerSeries.X 0 * MvPowerSeries.X 1) = 0 := by
    rw [dB.leibniz, dBX0, dBX1]
    rw [Algebra.smul_def, Algebra.smul_def]
    simp only [RingHom.algebraMap_toAlgebra]
    rw [qX0, qX1]
    rw [mul_neg, mul_one, neg_add_cancel]
  have hd : ∀ a : A,
      a ∈ Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} : Set A) → dB a = 0 := by
    intro a ha
    rcases Ideal.mem_span_singleton'.mp ha with ⟨c, rfl⟩
    rw [dB.leibniz, hdRel]
    rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp only [map_mul, qX0, qX1, heps]
    simp
  let dRlin : chapter01NodeRing k →ₗ[k] B :=
    { QuotientAddGroup.lift (Ideal.span
          ({MvPowerSeries.X 0 * MvPowerSeries.X 1} : Set A)).toAddSubgroup
          dB.toAddMonoidHom (by
            intro a ha
            exact hd a ha) with
      map_smul' := by
        rintro c ⟨a⟩
        exact dB.map_smul c a }
  let _ : Algebra (chapter01NodeRing k) B := qbar.toAlgebra
  have hquotTower : IsScalarTower k (chapter01NodeRing k) B := by
    constructor
    intro r x b
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      simp only [Algebra.smul_def]
      simp only [RingHom.algebraMap_toAlgebra]
      rw [← Submodule.Quotient.mk_smul]
      dsimp [qbar]
      rw [show r • a = algebraMap k A r * a by rw [Algebra.smul_def], map_mul]
      rw [MvPowerSeries.algebraMap_apply]
      dsimp [q]
      rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]
      simp [B, mul_assoc]
  let _ : IsScalarTower k (chapter01NodeRing k) B := hquotTower
  let dR : Derivation k (chapter01NodeRing k) B :=
    { toLinearMap := dRlin
      map_one_eq_zero' := by
        change dRlin (Ideal.Quotient.mk _ 1) = 0
        change dB 1 = 0
        exact dB.map_one_eq_zero
      leibniz' := by
        rintro ⟨a⟩ ⟨b⟩
        change dB (a * b) = q a • dB b + q b • dB a
        exact dB.leibniz a b }
  have hdiv_X_of_mem : ∀ a : A,
      (MvPowerSeries.X 0 + MvPowerSeries.X 1) * a ∈
          Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} : Set A) →
        MvPowerSeries.X 0 ∣ a := by
    intro a ha
    rcases Ideal.mem_span_singleton'.mp ha with ⟨c, hc⟩
    rw [MvPowerSeries.X_dvd_iff]
    intro n hn
    have hcoef := congrArg (MvPowerSeries.coeff (R := k) (n + Finsupp.single 1 1)) hc
    simp only [MvPowerSeries.X_def] at hcoef
    rw [MvPowerSeries.monomial_mul_monomial, add_mul, map_add,
      MvPowerSeries.coeff_mul_monomial,
      MvPowerSeries.coeff_monomial_mul,
      MvPowerSeries.coeff_monomial_mul] at hcoef
    simpa [Finsupp.single_add, hn] using hcoef.symm
  have hdiv_Y_of_mem : ∀ a : A,
      (MvPowerSeries.X 0 + MvPowerSeries.X 1) * a ∈
          Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} : Set A) →
        MvPowerSeries.X 1 ∣ a := by
    intro a ha
    rcases Ideal.mem_span_singleton'.mp ha with ⟨c, hc⟩
    rw [MvPowerSeries.X_dvd_iff]
    intro n hn
    have hcoef := congrArg (MvPowerSeries.coeff (R := k) (n + Finsupp.single 0 1)) hc
    simp only [MvPowerSeries.X_def] at hcoef
    rw [MvPowerSeries.monomial_mul_monomial, add_mul, map_add,
      MvPowerSeries.coeff_mul_monomial,
      MvPowerSeries.coeff_monomial_mul,
      MvPowerSeries.coeff_monomial_mul] at hcoef
    have hnot : ¬ Finsupp.single 0 1 + Finsupp.single 1 1 ≤
        n + Finsupp.single 0 1 := by
      intro h
      have h' : 1 ≤ n 1 := by
        simpa [Finsupp.add_apply, Finsupp.single_apply] using h 1
      omega
    simpa [Finsupp.single_add, hn, hnot] using hcoef.symm
  have hdiv_Y_of_X_mul : ∀ b : A,
      MvPowerSeries.X 1 ∣ MvPowerSeries.X 0 * b →
        MvPowerSeries.X 1 ∣ b := by
    intro b hb
    rcases hb with ⟨c, hc⟩
    rw [MvPowerSeries.X_dvd_iff]
    intro n hn
    have hcoef := congrArg (MvPowerSeries.coeff (R := k) (n + Finsupp.single 0 1)) hc
    simp only [MvPowerSeries.X_def] at hcoef
    rw [MvPowerSeries.coeff_monomial_mul,
      MvPowerSeries.coeff_monomial_mul] at hcoef
    have hnot : ¬ Finsupp.single 1 1 ≤ n + Finsupp.single 0 1 := by
      intro h
      have h' : 1 ≤ n 1 := by
        simpa [Finsupp.add_apply, Finsupp.single_apply] using h 1
      omega
    simpa [Finsupp.single_add, hn, hnot] using hcoef
  have hmem_regular : ∀ a : A,
      (MvPowerSeries.X 0 + MvPowerSeries.X 1) * a ∈
          Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} : Set A) →
        a ∈ Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} : Set A) := by
    intro a ha
    rcases hdiv_X_of_mem a ha with ⟨b, hb⟩
    have hby : MvPowerSeries.X 1 ∣ MvPowerSeries.X 0 * b := by
      rw [← hb]
      exact hdiv_Y_of_mem a ha
    rcases hdiv_Y_of_X_mul b hby with ⟨c, hc⟩
    exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [hb, hc]; ring⟩
  have hregular_node :
      Ideal.Quotient.mk _ (MvPowerSeries.X 0 + MvPowerSeries.X 1) ∈
        nonZeroDivisors (chapter01NodeRing k) := by
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro z hz
      induction z using Submodule.Quotient.induction_on with
      | _ a =>
        change Ideal.Quotient.mk _
          ((MvPowerSeries.X 0 + MvPowerSeries.X 1) * a) = 0 at hz
        change Ideal.Quotient.mk _ a = 0
        rw [Ideal.Quotient.eq_zero_iff_mem] at hz ⊢
        exact hmem_regular a hz
    · intro z hz
      induction z using Submodule.Quotient.induction_on with
      | _ a =>
        change Ideal.Quotient.mk _ (a *
          (MvPowerSeries.X 0 + MvPowerSeries.X 1)) = 0 at hz
        have hz' : Ideal.Quotient.mk
            (Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1} : Set A))
            ((MvPowerSeries.X 0 + MvPowerSeries.X 1) * a) = 0 := by
          simpa [mul_comm] using hz
        change Ideal.Quotient.mk _ a = 0
        rw [Ideal.Quotient.eq_zero_iff_mem] at hz' ⊢
        exact hmem_regular a hz'
  let xR : chapter01NodeRing k := Ideal.Quotient.mk _ (MvPowerSeries.X 0)
  let yR : chapter01NodeRing k := Ideal.Quotient.mk _ (MvPowerSeries.X 1)
  have hxyR : xR * yR = 0 := by
    change Ideal.Quotient.mk _ (MvPowerSeries.X 0 * MvPowerSeries.X 1) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have dRx : dR xR = 1 := by
    change dB (MvPowerSeries.X 0) = 1
    exact dBX0
  have dRy : dR yR = -1 := by
    change dB (MvPowerSeries.X 1) = -1
    exact dBX1
  have hrel :
      xR • KaehlerDifferential.D k (chapter01NodeRing k) yR +
          yR • KaehlerDifferential.D k (chapter01NodeRing k) xR = 0 := by
    have h := (KaehlerDifferential.D k (chapter01NodeRing k)).leibniz xR yR
    rw [hxyR] at h
    simpa using h.symm
  let m : chapter01NodeDifferentials k :=
    xR • KaehlerDifferential.D k (chapter01NodeRing k) yR
  have hkill :
      (xR + yR) • m = 0 := by
    have hxDy :
        xR • KaehlerDifferential.D k (chapter01NodeRing k) yR =
          -(yR • KaehlerDifferential.D k (chapter01NodeRing k) xR) :=
      eq_neg_of_add_eq_zero_left hrel
    dsimp [m]
    calc
      (xR + yR) • (xR • KaehlerDifferential.D k (chapter01NodeRing k) yR) =
          xR • (xR • KaehlerDifferential.D k (chapter01NodeRing k) yR) +
            yR • (xR • KaehlerDifferential.D k (chapter01NodeRing k) yR) := by
              exact add_smul (xR : chapter01NodeRing k) yR
                (xR • KaehlerDifferential.D k (chapter01NodeRing k) yR)
      _ = xR • (-(yR • KaehlerDifferential.D k (chapter01NodeRing k) xR)) +
            yR • (xR • KaehlerDifferential.D k (chapter01NodeRing k) yR) := by
              rw [hxDy]
      _ = -((xR * yR) • KaehlerDifferential.D k (chapter01NodeRing k) xR) +
            (yR * xR) • KaehlerDifferential.D k (chapter01NodeRing k) yR := by
              have hsmulneg := smul_neg xR
                (yR • KaehlerDifferential.D k (chapter01NodeRing k) xR)
              have hxy_smul := smul_smul (M := chapter01NodeRing k) xR yR
                (KaehlerDifferential.D k (chapter01NodeRing k) xR)
              have hyx_smul := smul_smul (M := chapter01NodeRing k) yR xR
                (KaehlerDifferential.D k (chapter01NodeRing k) yR)
              calc
                xR • (-(yR • KaehlerDifferential.D k (chapter01NodeRing k) xR)) +
                    yR • (xR • KaehlerDifferential.D k (chapter01NodeRing k) yR) =
                    -(xR • (yR • KaehlerDifferential.D k (chapter01NodeRing k) xR)) +
                      yR • (xR • KaehlerDifferential.D k (chapter01NodeRing k) yR) := by
                        exact congrArg₂ (fun a b => a + b) hsmulneg rfl
                _ = -((xR * yR) • KaehlerDifferential.D k (chapter01NodeRing k) xR) +
                      yR • (xR • KaehlerDifferential.D k (chapter01NodeRing k) yR) := by
                        exact congrArg₂ (fun a b => a + b)
                          (congrArg Neg.neg hxy_smul) rfl
                _ = -((xR * yR) • KaehlerDifferential.D k (chapter01NodeRing k) xR) +
                      (yR * xR) • KaehlerDifferential.D k (chapter01NodeRing k) yR := by
                        exact congrArg₂ (fun a b => a + b) rfl hyx_smul
      _ = 0 := by
        have hyx : yR * xR = 0 := by
          rw [mul_comm, hxyR]
        rw [hxyR, hyx]
        have hzero_x :
            (0 : chapter01NodeRing k) •
                KaehlerDifferential.D k (chapter01NodeRing k) xR = 0 := by
          rw [← IsScalarTower.algebraMap_smul
            (R := chapter01NodeRing k)
            (TensorProduct k (chapter01NodeRing k) (chapter01NodeRing k))]
          rw [map_zero (algebraMap (chapter01NodeRing k)
            (TensorProduct k (chapter01NodeRing k) (chapter01NodeRing k)))]
          exact Ideal.Cotangent.smul_eq_zero_of_mem (I :=
            KaehlerDifferential.ideal k (chapter01NodeRing k))
              (x := (0 : TensorProduct k (chapter01NodeRing k) (chapter01NodeRing k))) (by simp)
            (KaehlerDifferential.D k (chapter01NodeRing k) xR)
        have hzero_y :
            (0 : chapter01NodeRing k) •
                KaehlerDifferential.D k (chapter01NodeRing k) yR = 0 := by
          rw [← IsScalarTower.algebraMap_smul
            (R := chapter01NodeRing k)
            (TensorProduct k (chapter01NodeRing k) (chapter01NodeRing k))]
          rw [map_zero (algebraMap (chapter01NodeRing k)
            (TensorProduct k (chapter01NodeRing k) (chapter01NodeRing k)))]
          exact Ideal.Cotangent.smul_eq_zero_of_mem (I :=
            KaehlerDifferential.ideal k (chapter01NodeRing k))
              (x := (0 : TensorProduct k (chapter01NodeRing k) (chapter01NodeRing k))) (by simp)
            (KaehlerDifferential.D k (chapter01NodeRing k) yR)
        rw [hzero_x, hzero_y]
        simp
  have hm_eval :
      dR.liftKaehlerDifferential m = -(DualNumber.eps : DualNumber k) := by
    dsimp [m]
    rw [LinearMap.map_smul, Derivation.liftKaehlerDifferential_comp_D, dRy]
    dsimp [xR]
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, qbarX0]
    exact mul_neg_one (DualNumber.eps : DualNumber k)
  have heps_ne : (DualNumber.eps : DualNumber k) ≠ 0 := by
    intro h
    have hs := congrArg TrivSqZeroExt.snd h
    simp only [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] at hs
    exact one_ne_zero hs
  have hm_ne : m ≠ 0 := by
    intro hm
    have h := congrArg dR.liftKaehlerDifferential hm
    rw [hm_eval, map_zero] at h
    exact heps_ne (neg_eq_zero.mp h)
  refine ⟨m, hm_ne, xR + yR, hregular_node, hkill⟩

def chapter01NodalDifferentialComparison (k : Type u) [Field k] : Prop :=
  ∃ D : Chapter01DifferentialComparison (chapter01NodeRing k),
    letI := D.ordinaryAddCommGroup
    letI := D.ordinaryModule
    letI := D.dualityAddCommGroup
    letI := D.dualityModule
    Nonempty (D.ordinary ≃ₗ[chapter01NodeRing k] chapter01NodeDifferentials k) ∧
      Nonempty (D.duality ≃ₗ[chapter01NodeRing k] chapter01NodeRing k)

theorem chapter01_nodal_differential_comparison
    (k : Type u) [Field k] : chapter01NodalDifferentialComparison k := by
  refine ⟨{ ordinary := chapter01NodeDifferentials k, duality := chapter01NodeRing k, ordinaryHasTorsion := chapter01_node_ordinary_differentials_have_torsion k, dualityWellBehaved := inferInstance }, ?_⟩
  exact ⟨⟨LinearEquiv.refl _ _⟩, ⟨LinearEquiv.refl _ _⟩⟩

/-! The completed local model is the usual node ``k[[u,v]]/(uv)``.  This local
  definition is used only as the node predicate; the later duality chapters supply
  the canonical relative dualizing module. -/
abbrev chapter01CompletedLocalRing (X : Scheme.{u}) (x : X) : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

abbrev chapter01NodeRingAt (X : Scheme.{u}) (x : X) : Type u :=
  chapter01NodeRing (X.residueField x)

def chapter01OrdinaryDoublePointAt (X : Scheme.{u}) (x : X) : Prop :=
  Nonempty (chapter01CompletedLocalRing X x ≃+* chapter01NodeRingAt X x)

def chapter01RegularPoint (X : Scheme.{u}) (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x)

def chapter01NodalScheme (X : Scheme.{u}) : Prop :=
  Chapter01PureDimensionOne X ∧ IsReduced X ∧
    ∀ x : X, chapter01RegularPoint X x ∨ chapter01OrdinaryDoublePointAt X x

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib snapshot has no named Gorenstein
  scheme-morphism property.  The injective-dimension characterization below is
  the standard noetherian-local replacement and is used only as a hypothesis. -/
def chapter01GorensteinLocalRing (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ injectiveDimension (ModuleCat.of R R) = ringKrullDim R

def chapter01GorensteinMorphism {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Flat f ∧ LocallyOfFinitePresentation f ∧
    geometrically
      (fun Y : Scheme.{u} => ∀ y : Y, chapter01GorensteinLocalRing (Y.presheaf.stalk y)) f

class Chapter01NodalRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S)
    : Prop extends Chapter01RelativeCurve f where
  geometricFibersNodal :
    geometrically (fun Y : Scheme.{u} => chapter01NodalScheme Y) f

class Chapter01GorensteinNodalRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S)
    : Prop extends Chapter01NodalRelativeCurve f where
  gorenstein : chapter01GorensteinMorphism f

def chapter01LocallyCutOutByOneEquationInSmoothSurface
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (i : X ⟶ Y),
    SmoothOfRelativeDimension 2 g ∧ IsClosedImmersion i ∧ i ≫ g = f ∧
      ∀ x : X, ∃ a : Y.presheaf.stalk (i x),
        a ∈ nonZeroDivisors (Y.presheaf.stalk (i x)) ∧
          RingHom.ker (i.stalkMap x).hom = Ideal.span ({a} : Set _) ∧
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
structure Chapter01DivisorLineBundleInterface (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] where
  /- A Weil divisor is identified with a Cartier divisor only under a
     local-factoriality hypothesis.  Regularity is the curve-level
     hypothesis used by the book for this dictionary. -/
  regularAt : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)
  divisorToLineBundle : Chapter01Divisor X → Chapter01LineBundleClass X
  lineBundleToDivisor : Chapter01LineBundleClass X → Chapter01Divisor X
  principalDivisor : Chapter01RationalFunctionUnit X → Chapter01Divisor X
  principalCoefficient :
    ∀ f x, principalDivisor f x =
      chapter01OrderAt x (f : Chapter01RationalFunction X)
  divisorToLineBundle_toDivisor :
    ∀ D, lineBundleToDivisor (divisorToLineBundle D) = D
  lineBundleToDivisor_toLineBundle :
    ∀ L, divisorToLineBundle (lineBundleToDivisor L) = L
  principalToTrivial :
    ∀ f, divisorToLineBundle (principalDivisor f) =
      chapter01LineBundleClassMk (chapter04TrivialLineBundle X)
  trivialToPrincipal :
    ∀ D, divisorToLineBundle D =
      chapter01LineBundleClassMk (chapter04TrivialLineBundle X) →
      ∃ f, D = principalDivisor f

def chapter01DivisorLineBundleEquiv {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X]
    (D : Chapter01DivisorLineBundleInterface X) :
    Chapter01Divisor X ≃ Chapter01LineBundleClass X :=
  { toFun := D.divisorToLineBundle
    invFun := D.lineBundleToDivisor
    left_inv := D.divisorToLineBundle_toDivisor
    right_inv := D.lineBundleToDivisor_toLineBundle }

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
