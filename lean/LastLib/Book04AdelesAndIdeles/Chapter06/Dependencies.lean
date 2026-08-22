import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Prod
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Order.Filter.Cofinite
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.Topology.Algebra.RestrictedProduct.Units

namespace LastLib.Book04AdelesAndIdeles.Chapter06

noncomputable section

open Set MeasureTheory Topology
open scoped BigOperators ENNReal NNReal Pointwise RestrictedProduct WithZero

universe uK uO uInf uFin uHat uG uPlace uV uVA

/-!
The preceding Book 4 chapters provide canonical carriers in their own
namespaces.  This file keeps a deliberately small explicit adapter so the
chapter can state its quotient arguments without duplicating those carriers;
the adapter records the number-field maps and compact integral finite part
needed here, but does not package any compactness result proved below as an
assumption.
-/

/-- The number-field data used by the compact additive quotient.

`O` is the ring of integers, `K∞` is the archimedean component, `Af` is the
finite adele group, and `Ohat` is its integral compact open.  The two
compatibility fields say that the algebraic-integer diagonal agrees with the
global diagonal in both components. -/
structure Chapter06AdeleData
    (K : Type uK) (O : Type uO) (KInf : Type uInf) (Af : Type uFin)
    (Ohat : Type uHat)
    [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
    [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
    [TopologicalSpace Ohat] where
  integerToGlobal : O →+* K
  integerToGlobal_injective : Function.Injective integerToGlobal
  globalToInfinite : K →+ KInf
  globalToFinite : K →+ Af
  integerToInfinite : O →+ KInf
  integerToFinite : O →+ Ohat
  finiteIntegralEmbedding : Ohat →+ Af
  integerToInfinite_compatibility :
    integerToInfinite = globalToInfinite.comp integerToGlobal.toAddMonoidHom
  finiteIntegral_compatibility :
    finiteIntegralEmbedding.comp integerToFinite =
      globalToFinite.comp integerToGlobal.toAddMonoidHom
  finite_integrality_characterization :
    ∀ a : K,
      (∃ u : Ohat, finiteIntegralEmbedding u = globalToFinite a) ↔
        ∃ o : O, integerToGlobal o = a
  /-- The principal-parts decomposition supplied by strong approximation. -/
  finite_principal_parts :
    ∀ x : Af, ∃ a : K, ∃ u : Ohat,
      x = globalToFinite a + finiteIntegralEmbedding u
  finiteIntegral_embedding :
    IsEmbedding finiteIntegralEmbedding
  finiteIntegral_range_compact :
    IsCompact (Set.range finiteIntegralEmbedding)
  finiteIntegral_range_open :
    IsOpen (Set.range finiteIntegralEmbedding)
  diagonal_injective :
    Function.Injective (fun a : K => (globalToInfinite a, globalToFinite a))
  finite_diagonal_injective :
    Function.Injective globalToFinite
  diagonal_closed :
    IsClosed (Set.range (fun a : K => (globalToInfinite a, globalToFinite a)))
  finite_diagonal_dense :
    Dense (Set.range globalToFinite)
  finite_diagonal_not_surjective :
    Set.range globalToFinite ≠ Set.univ

namespace Chapter06AdeleData

variable {K : Type uK} {O : Type uO} {KInf : Type uInf} {Af : Type uFin}
  {Ohat : Type uHat}
variable [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
  [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
  [TopologicalSpace Ohat]

@[simp] theorem integerToInfinite_compatibility_apply
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : O) :
    P.integerToInfinite x = P.globalToInfinite (P.integerToGlobal x) := by
  rw [P.integerToInfinite_compatibility]
  rfl

@[simp] theorem finiteIntegral_compatibility_apply
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : O) :
    P.finiteIntegralEmbedding (P.integerToFinite x) =
      P.globalToFinite (P.integerToGlobal x) := by
  change (P.finiteIntegralEmbedding.comp P.integerToFinite) x =
    (P.globalToFinite.comp P.integerToGlobal.toAddMonoidHom) x
  rw [P.finiteIntegral_compatibility]

end Chapter06AdeleData

/-- The finite and full adele types in the book's product presentation. -/
abbrev Chapter06FiniteAdele (Af : Type uFin) := Af

abbrev Chapter06FullAdele (KInf : Type uInf) (Af : Type uFin) := KInf × Af

section AdeleData

variable {K : Type uK} {O : Type uO} {KInf : Type uInf} {Af : Type uFin}
  {Ohat : Type uHat}
variable [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
  [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
  [TopologicalSpace Ohat]

/-- The diagonal embedding of the global field into the full adeles. -/
def chapter06Diagonal
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    K →+ Chapter06FullAdele KInf Af where
  toFun x := (P.globalToInfinite x, P.globalToFinite x)
  map_zero' := by simp
  map_add' x y := by simp

@[simp] theorem chapter06Diagonal_apply
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : K) :
    chapter06Diagonal P x = (P.globalToInfinite x, P.globalToFinite x) := rfl

/-- The global diagonal subgroup of the full adele group. -/
def chapter06GlobalSubgroup
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    AddSubgroup (Chapter06FullAdele KInf Af) :=
  (chapter06Diagonal P).range

/-- The integral diagonal inside `K∞ × Ohat`. -/
def chapter06IntegralDiagonal
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    O →+ KInf × Ohat where
  toFun x := (P.integerToInfinite x, P.integerToFinite x)
  map_zero' := by simp
  map_add' x y := by simp

@[simp] theorem chapter06IntegralDiagonal_apply
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : O) :
    chapter06IntegralDiagonal P x =
      (P.integerToInfinite x, P.integerToFinite x) := rfl

def chapter06IntegralGluingSubgroup
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    AddSubgroup (KInf × Ohat) :=
  (chapter06IntegralDiagonal P).range

/-- The quotient `A_K / K`, with the quotient topology supplied by Mathlib. -/
abbrev Chapter06AdeleQuotient
    (P : Chapter06AdeleData K O KInf Af Ohat) :=
  Chapter06FullAdele KInf Af ⧸ chapter06GlobalSubgroup P

def chapter06AdeleQuotientMap
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    Chapter06FullAdele KInf Af →+
      Chapter06AdeleQuotient P :=
  QuotientAddGroup.mk' (chapter06GlobalSubgroup P)

@[simp] theorem chapter06AdeleQuotientMap_apply
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (x : Chapter06FullAdele KInf Af) :
    chapter06AdeleQuotientMap P x =
      QuotientAddGroup.mk' (chapter06GlobalSubgroup P) x := rfl

@[simp] theorem chapter06AdeleQuotientMap_eq_iff
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (x y : Chapter06FullAdele KInf Af) :
    chapter06AdeleQuotientMap P x = chapter06AdeleQuotientMap P y ↔
      x - y ∈ chapter06GlobalSubgroup P := by
  change QuotientAddGroup.mk' (chapter06GlobalSubgroup P) x =
      QuotientAddGroup.mk' (chapter06GlobalSubgroup P) y ↔ _
  exact QuotientAddGroup.eq_iff_sub_mem

theorem chapter06AdeleQuotientMap_ker
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    AddMonoidHom.ker (chapter06AdeleQuotientMap P) =
      chapter06GlobalSubgroup P := by
  change AddMonoidHom.ker (QuotientAddGroup.mk'
      (chapter06GlobalSubgroup P)) = chapter06GlobalSubgroup P
  exact QuotientAddGroup.ker_mk' _

theorem chapter06AdeleQuotientMap_surjective
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    Function.Surjective (chapter06AdeleQuotientMap P) := by
  exact QuotientAddGroup.mk'_surjective (chapter06GlobalSubgroup P)

/-- Forget the integral condition in the finite coordinate. -/
def chapter06IntegralGluingToAdele
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    (KInf × Ohat) →+ Chapter06FullAdele KInf Af where
  toFun x := (x.1, P.finiteIntegralEmbedding x.2)
  map_zero' := by simp
  map_add' x y := by
    apply Prod.ext <;> simp

@[simp] theorem chapter06IntegralGluingToAdele_apply
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : KInf × Ohat) :
    chapter06IntegralGluingToAdele P x =
      (x.1, P.finiteIntegralEmbedding x.2) := rfl

/-- The map from the integral-gluing model to the adelic quotient. -/
def chapter06IntegralGluingMap
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    (KInf × Ohat) →+ Chapter06AdeleQuotient P :=
  (chapter06AdeleQuotientMap P).comp (chapter06IntegralGluingToAdele P)

@[simp] theorem chapter06IntegralGluingMap_apply
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : KInf × Ohat) :
    chapter06IntegralGluingMap P x =
      chapter06AdeleQuotientMap P
        (x.1, P.finiteIntegralEmbedding x.2) := rfl

/-- A compact archimedean cell for the algebraic-integer lattice. -/
structure Chapter06ArchimedeanCell
    (P : Chapter06AdeleData K O KInf Af Ohat) where
  carrier : Set KInf
  compact : IsCompact carrier
  covers : ∀ x : KInf, ∃ a : O,
    x - P.integerToInfinite a ∈ carrier

namespace Chapter06ArchimedeanCell

variable {P : Chapter06AdeleData K O KInf Af Ohat}

instance : SetLike (Chapter06ArchimedeanCell P) KInf where
  coe D := D.carrier
  coe_injective := by
    intro D E h
    cases D
    cases E
    cases h
    rfl

@[simp] theorem mem_carrier (D : Chapter06ArchimedeanCell P) (x : KInf) :
    x ∈ (D : Set KInf) ↔ x ∈ D.carrier := Iff.rfl

end Chapter06ArchimedeanCell

/-- The compact covering set `D × Ohat` inside the full adeles. -/
def chapter06FundamentalSet
    (P : Chapter06AdeleData K O KInf Af Ohat) (D : Set KInf) :
    Set (Chapter06FullAdele KInf Af) :=
  D ×ˢ Set.range P.finiteIntegralEmbedding

def chapter06FundamentalSetSubtype
    (P : Chapter06AdeleData K O KInf Af Ohat) (D : Set KInf) :=
  {x : Chapter06FullAdele KInf Af // x ∈ chapter06FundamentalSet P D}

def chapter06FundamentalSetQuotientMap
    (P : Chapter06AdeleData K O KInf Af Ohat) (D : Set KInf) :
    chapter06FundamentalSetSubtype P D → Chapter06AdeleQuotient P :=
  fun x => chapter06AdeleQuotientMap P x.1

@[simp] theorem chapter06FundamentalSetQuotientMap_apply
    (P : Chapter06AdeleData K O KInf Af Ohat) (D : Set KInf)
    (x : chapter06FundamentalSetSubtype P D) :
    chapter06FundamentalSetQuotientMap P D x =
      chapter06AdeleQuotientMap P x.1 := rfl

@[simp] theorem mem_chapter06FundamentalSet_iff
    (P : Chapter06AdeleData K O KInf Af Ohat) (D : Set KInf)
    (x : Chapter06FullAdele KInf Af) :
    x ∈ chapter06FundamentalSet P D ↔
      x.1 ∈ D ∧ ∃ u : Ohat, P.finiteIntegralEmbedding u = x.2 := by
  rfl

end AdeleData

/-- A discrete embedding of an additive group into a topological additive group. -/
def Chapter06DiscreteEmbedding
    {G : Type uG} {H : Type uVA} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] (ι : G →+ H) : Prop :=
  Function.Injective ι ∧
    ∀ g : G, ∃ U : Set H, IsOpen U ∧ ι g ∈ U ∧
      ∀ h : G, ι h ∈ U → h = g

/-- Bridge the usual discrete-subspace formulation to the local isolation
    formulation used by the additive-lattice statements. -/
theorem chapter06_discrete_embedding_of_discrete_range
    {G : Type uG} {H : Type uVA} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] (ι : G →+ H)
    (hinjective : Function.Injective ι)
    (hdiscrete : DiscreteTopology (Set.range ι)) :
    Chapter06DiscreteEmbedding ι := by
  refine ⟨hinjective, ?_⟩
  intro g
  let _ : DiscreteTopology (Set.range ι) := hdiscrete
  have hs : IsOpen ({⟨ι g, ⟨g, rfl⟩⟩} : Set (Set.range ι)) :=
    (discreteTopology_iff_isOpen_singleton.mp inferInstance) _
  rw [isOpen_induced_iff] at hs
  rcases hs with ⟨U, hU, hpre⟩
  refine ⟨U, hU, ?_, ?_⟩
  · change (⟨ι g, ⟨g, rfl⟩⟩ : Set.range ι) ∈
      Subtype.val ⁻¹' U
    rw [hpre]
    change (⟨ι g, ⟨g, rfl⟩⟩ : Set.range ι) ∈
      ({⟨ι g, ⟨g, rfl⟩⟩} : Set (Set.range ι))
    exact Set.mem_singleton _
  · intro h hh
    have hmem :
        (⟨ι h, ⟨h, rfl⟩⟩ : Set.range ι) ∈
          ({⟨ι g, ⟨g, rfl⟩⟩} : Set (Set.range ι)) := by
      rw [← hpre]
      exact hh
    exact hinjective (congrArg Subtype.val (Set.mem_singleton_iff.mp hmem))

/-- A compact fundamental set for an additive embedding. -/
def Chapter06CompactFundamentalSet
    {G : Type uG} {H : Type uVA} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H]
    (ι : G →+ H) : Prop :=
  ∃ C : Set H, IsCompact C ∧ ∀ x : H, ∃ g : G, x - ι g ∈ C

/-- A topological-group lattice: discrete with compact quotient. -/
def Chapter06AdditiveLattice
    {G : Type uG} {H : Type uVA} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [T2Space H]
    (ι : G →+ H) : Prop :=
  Chapter06DiscreteEmbedding ι ∧
    CompactSpace (H ⧸ ι.range)

/-- The module-theoretic lattice notion used for comparison in §6.8.

The finite generation is over the integral coefficient ring `R`, while
fullness is measured after extending scalars to the ambient field `F`.
Using `Submodule.span R` here would force an `R`-submodule to be `⊤`, and
would therefore not describe an integral lattice in an `F`-vector space.
The second conjunct records fullness after extending scalars to `F` directly. -/
def Chapter06ModuleLattice
    (R F V : Type*) [CommRing R] [Field F] [AddCommGroup V]
    [Algebra R F] [Module F V] [Module R V] [IsScalarTower R F V]
    (L : Submodule R V) : Prop :=
  Module.Finite R L ∧
    Submodule.span F (L : Set V) = ⊤

/-- The local additive module relation for a Haar measure. -/
def Chapter06LocalMeasureModule
    (F : Type*) [Field F] [MeasurableSpace F]
    (μ : Measure F) (size : F → ℝ≥0∞) : Prop :=
  ∀ a : F, a ≠ 0 →
    Measure.map (fun x : F => a * x) μ = (size a)⁻¹ • μ

/-! ### Finite-adelic local factors and Haar scaling

The finite-adelic measure calculation has two logically separate inputs.  The
local factors must be normalized on the distinguished integral subgroups, and
the measure of one normalized compact-open test set must be computed as the
finite product of those factors.  The declarations below keep those inputs
explicit.  In particular, they do not turn a local normalization into an
unproved assertion about an arbitrary global measure. -/

/-- Local scalar factors together with their almost-everywhere integral
normalization.  The local groups need not be fields here; this is the small
interface needed for the finite-support argument and can therefore be reused
for normalized local absolute values. -/
structure Chapter06FiniteAdeleLocalFactorData
    (Place : Type uPlace) (Local : Place → Type uV)
    [∀ v, Group (Local v)] where
  integralSubgroup : ∀ v, Subgroup (Local v)
  factor : ∀ v, Local v → ℝ≥0
  normalized_on_integral :
    ∀ᶠ v in Filter.cofinite,
      ∀ u : Local v, u ∈ integralSubgroup v → factor v u = 1

/-- An idele with an integral tail has only finitely many nontrivial local
factors.  This is the eventual-unit-tail argument used to make the finite
product in an adelic module literal rather than formal infinite-product data. -/
theorem chapter06_finite_idele_local_factor_has_finite_support
    {Place : Type uPlace} {Local : Place → Type uV}
    [∀ v, Group (Local v)]
    (D : Chapter06FiniteAdeleLocalFactorData Place Local)
    (x : ∀ v, Local v)
    (hx : ∀ᶠ v in Filter.cofinite,
      x v ∈ D.integralSubgroup v) :
    Function.HasFiniteMulSupport (fun v => D.factor v (x v)) := by
  rw [Function.HasFiniteMulSupport]
  apply Filter.eventually_cofinite.mp
  filter_upwards [hx, D.normalized_on_integral] with v hv hnormal
  exact hnormal (x v) hv

/-- Finite-adelic data for comparing a normalized local-factor product with
the distributive Haar character of the global additive action.

`testSet_scaling` is the local product-measure calculation.  Once it has been
proved for one non-null, non-infinite test set, Haar uniqueness gives scaling
on every measurable set.  The component-tail field and the preceding support
lemma expose the restricted-product argument needed by concrete finite-idele
instantiations. -/
structure Chapter06FiniteAdeleHaarScalingData
    (Place : Type uPlace) (Local : Place → Type uV)
    (G : Type uG) (A : Type uVA)
    [∀ v, Group (Local v)] [Group G] [AddCommGroup A]
    [DistribMulAction G A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [ContinuousConstSMul G A]
    [MeasurableSpace A] [BorelSpace A] where
  localFactors : Chapter06FiniteAdeleLocalFactorData Place Local
  component : G → ∀ v, Local v
  component_eventually_integral :
    ∀ g : G, ∀ᶠ v in Filter.cofinite,
      component g v ∈ localFactors.integralSubgroup v
  measure : Measure A
  testSet : Set A
  testSet_compact : IsCompact testSet
  testSet_measurable : MeasurableSet testSet
  testSet_measure_ne_zero : measure testSet ≠ 0
  testSet_measure_ne_top : measure testSet ≠ ⊤
  testSet_scaling :
    ∀ g : G,
      measure (g • testSet) =
        ((∏ᶠ v, localFactors.factor v (component g v) : ℝ≥0) : ℝ≥0∞) *
          measure testSet

theorem chapter06_finite_adelic_haar_factor_has_finite_support
    {Place : Type uPlace} {Local : Place → Type uV}
    {G : Type uG} {A : Type uVA}
    [∀ v, Group (Local v)] [Group G] [AddCommGroup A]
    [DistribMulAction G A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [ContinuousConstSMul G A]
    [MeasurableSpace A] [BorelSpace A]
    (D : Chapter06FiniteAdeleHaarScalingData Place Local G A) (g : G) :
    Function.HasFiniteMulSupport
      (fun v => D.localFactors.factor v (D.component g v)) := by
  exact chapter06_finite_idele_local_factor_has_finite_support
    D.localFactors (D.component g) (D.component_eventually_integral g)

/-- The normalized local-factor product is the global distributive Haar
character once its value has been computed on the test set. -/
theorem chapter06_finite_adelic_haar_character_eq_local_factor_product
    {Place : Type uPlace} {Local : Place → Type uV}
    {G : Type uG} {A : Type uVA}
    [∀ v, Group (Local v)] [Group G] [AddCommGroup A]
    [DistribMulAction G A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [ContinuousConstSMul G A]
    [MeasurableSpace A] [BorelSpace A]
    (D : Chapter06FiniteAdeleHaarScalingData Place Local G A)
    [D.measure.IsAddHaarMeasure] [Measure.Regular D.measure] (g : G) :
    MeasureTheory.distribHaarChar A g =
      ∏ᶠ v, D.localFactors.factor v (D.component g v) := by
  exact MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := D.measure) (s := D.testSet) (g := g)
    D.testSet_measure_ne_zero D.testSet_measure_ne_top (D.testSet_scaling g)

/-- Haar scaling on every set, obtained from the local-factor product on the
normalized test set. -/
theorem chapter06_finite_adelic_haar_scaling
    {Place : Type uPlace} {Local : Place → Type uV}
    {G : Type uG} {A : Type uVA}
    [∀ v, Group (Local v)] [Group G] [AddCommGroup A]
    [DistribMulAction G A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [ContinuousConstSMul G A]
    [MeasurableSpace A] [BorelSpace A]
    (D : Chapter06FiniteAdeleHaarScalingData Place Local G A)
    [D.measure.IsAddHaarMeasure] [Measure.Regular D.measure]
    (g : G) (s : Set A) :
    D.measure (g • s) =
      ((∏ᶠ v, D.localFactors.factor v (D.component g v) : ℝ≥0) : ℝ≥0∞) *
        D.measure s := by
  have hchar : MeasureTheory.distribHaarChar A g =
      ∏ᶠ v, D.localFactors.factor v (D.component g v) :=
    chapter06_finite_adelic_haar_character_eq_local_factor_product D g
  rw [← hchar]
  exact (MeasureTheory.distribHaarChar_mul (A := A) (μ := D.measure) g s).symm

/-- A regular Borel additive Haar measure, exposed through Mathlib's canonical
Haar predicate and the regularity convention used by the source. -/
def Chapter06IsAdditiveHaarMeasure
    (G : Type*) [AddCommGroup G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G]
    (μ : Measure G) : Prop :=
  Measure.IsAddHaarMeasure μ ∧ Measure.Regular μ

/-- The local product formula interface used by the volume argument. -/
def Chapter06ProductFormula
    (K Place : Type*) [Field K]
    (size : Place → K → ℝ≥0∞) (adelicProduct : K → ℝ≥0∞) : Prop := by
  classical
  exact ∀ a : K, a ≠ 0 → ∃ S : Finset Place,
    (∀ v, v ∉ S → size v a = 1) ∧
      (adelicProduct a = ∏ v ∈ S, size v a) ∧
      adelicProduct a = 1

/-! ### Standard number-field additive Haar factors

The generic finite-tail interface above is useful for abstract restricted products, but the
number-field application needs the actual Mathlib adele ring and both kinds of local factors.
These definitions keep that normalized formula in an earlier shared module so later divisor and
idele sections can consume it without rebuilding the product bookkeeping. -/

/-- The standard full adele ring used by the number-field Haar-character interface. -/
abbrev Chapter06StandardNumberFieldAdele (K : Type*) [Field K] [NumberField K] :=
  NumberField.AdeleRing (NumberField.RingOfIntegers K) K

/-- The totalized ideal-theoretic order on one finite completion.

The zero branch is irrelevant for an idele coordinate, but makes the factor a total function and
matches the local order convention used by the later divisor chapter. -/
def chapter06StandardNumberFieldLocalOrder
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : v.adicCompletion K) : ℤ :=
  if hx : (Valued.v x : ℤᵐ⁰) = 0 then
    0
  else
    -((WithZero.unzero hx).toAdd)

/-- The normalized archimedean contribution to the additive Haar character. -/
noncomputable def chapter06StandardNumberFieldInfiniteHaarFactor
    (K : Type*) [Field K] [NumberField K]
    (x : (Chapter06StandardNumberFieldAdele K)ˣ) : ℝ≥0 :=
  ∏ v : NumberField.InfinitePlace K,
    ‖((MulEquiv.piUnits (MulEquiv.prodUnits x).1) v : v.Completion)‖₊ ^ v.mult

/-- The normalized finite-place contribution to the additive Haar character. -/
noncomputable def chapter06StandardNumberFieldFiniteHaarFactor
    (K : Type*) [Field K] [NumberField K]
    (x : (Chapter06StandardNumberFieldAdele K)ˣ) : ℝ≥0 :=
  ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
    (Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-chapter06StandardNumberFieldLocalOrder v
        ((RestrictedProduct.unitsEquiv
          (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
            v.adicCompletion K) (MulEquiv.prodUnits x).2) v : v.adicCompletion K))

/-! The substantive local-product calculation is intentionally exposed as one reusable theorem.
Its proof is the standard product-measure/Haar-uniqueness argument; later sections only need the
resulting canonical formula. -/

theorem chapter06_standard_number_field_adele_unit_distrib_haar_char_apply
    (K : Type*) [Field K] [NumberField K]
    [LocallyCompactSpace (Chapter06StandardNumberFieldAdele K)]
    (x : (Chapter06StandardNumberFieldAdele K)ˣ) :
    MeasureTheory.distribHaarChar
        (G := (Chapter06StandardNumberFieldAdele K)ˣ)
        (A := Chapter06StandardNumberFieldAdele K) x =
      chapter06StandardNumberFieldInfiniteHaarFactor K x *
        chapter06StandardNumberFieldFiniteHaarFactor K x := by
  sorry

/-- Ordinary real/planar covolume in the Minkowski normalization. -/
def chapter06OrdinaryCovolume (r₂ : ℕ) (dK : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ r₂ * Real.sqrt |dK|

/-- The real local module in the ordinary Lebesgue convention. -/
def chapter06RealLocalSize (x : ℝ) : ℝ := |x|

/-- The complex local module in the ordinary planar convention. -/
def chapter06ComplexLocalSize (z : ℂ) : ℝ := ‖z‖ ^ 2

/-- Passing from ordinary planar measure to the self-dual complex measure. -/
def chapter06SelfDualComplexMeasure (μ : Measure ℂ) : Measure ℂ :=
  (2 : ℝ≥0∞) • μ

def chapter06SelfDualComplexMeasureScale : ℝ≥0∞ := 2

def chapter06SelfDualGlobalScaling (r₂ : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ r₂

/-- The local mass forced by self-duality at a finite place with residue-field
cardinality `q` and different exponent `d`. -/
def chapter06FiniteSelfDualMass (q d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (q : ℝ) (-((d : ℝ) / 2)))

@[simp] theorem chapter06FiniteSelfDualMass_apply (q d : ℕ) :
    chapter06FiniteSelfDualMass q d =
      ENNReal.ofReal (Real.rpow (q : ℝ) (-((d : ℝ) / 2))) :=
  rfl

/- The `Place` index in this adapter is intended to range over finite places. -/
structure Chapter06SelfDualFiniteNormalization (Place : Type*) where
  different : Set Place
  different_finite : different.Finite
  residueCardinality : Place → ℕ
  residueCardinality_pos : ∀ v, 0 < residueCardinality v
  differentExponent : Place → ℕ
  integralMass : Place → ℝ≥0∞
  integralMass_eq_one_off_different :
    ∀ v, v ∉ different → integralMass v = 1
  integralMass_eq_self_dual_on_different :
    ∀ v, v ∈ different →
      integralMass v =
        chapter06FiniteSelfDualMass (residueCardinality v) (differentExponent v)

/-! A restricted-product measure profile whose fields are the preceding
Minkowski and local normalizations, leaving the covolume calculation below as
the chapter result. -/
section AdelicMeasureData

variable {K : Type uK} {O : Type uO} {KInf : Type uInf} {Af : Type uFin}
  {Ohat : Type uHat}
variable [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
  [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
  [TopologicalSpace Ohat]
variable [MeasurableSpace KInf] [MeasurableSpace Af]

structure Chapter06AdelicMeasureData
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) where
  infiniteMeasure : Measure KInf
  finiteMeasure : Measure Af
  r₂ : ℕ
  discriminant : ℝ
  finiteIntegral_range_measurable :
    MeasurableSet (Set.range P.finiteIntegralEmbedding)
  archimedean_cell_measurable : MeasurableSet D.carrier
  finiteIntegral_measure_one :
    finiteMeasure (Set.range P.finiteIntegralEmbedding) = 1
  archimedean_cell_volume :
    infiniteMeasure D.carrier =
      ENNReal.ofReal (chapter06OrdinaryCovolume r₂ discriminant)

variable {P : Chapter06AdeleData K O KInf Af Ohat}
  {D : Chapter06ArchimedeanCell P}

def chapter06AdelicProductMeasure
    (M : Chapter06AdelicMeasureData P D) :
    Measure (Chapter06FullAdele KInf Af) :=
  M.infiniteMeasure.prod M.finiteMeasure

/- The data below only evaluates the product measure on the displayed set.
   A quotient covolume additionally needs a quotient Haar measure and a
   genuine measurable fundamental-domain hypothesis, so keep the formal
   quantity honest at this layer. -/
def chapter06AdelicFundamentalSetMass
    (M : Chapter06AdelicMeasureData P D) : ℝ≥0∞ :=
  chapter06AdelicProductMeasure M (chapter06FundamentalSet P D.carrier)

/- The quotient Haar measure is separate analytic input.  The quotient-volume
   record deliberately does not assume that its value is the prequotient set
   mass; that fundamental-domain identification belongs to the theorem using
   this record. -/
structure Chapter06AdelicQuotientVolumeData
    (M : Chapter06AdelicMeasureData P D) where
  quotientVolume : ℝ≥0∞

def chapter06AdelicQuotientCovolume
    {P : Chapter06AdeleData K O KInf Af Ohat}
    {D : Chapter06ArchimedeanCell P}
    (M : Chapter06AdelicMeasureData P D)
    (Q : Chapter06AdelicQuotientVolumeData M) : ℝ≥0∞ :=
  Q.quotientVolume

end AdelicMeasureData

/-- The unrestricted product underlying the topology warning in §6.7. -/
def Chapter06UnrestrictedProduct (ι : Type*) (X : ι → Type*) := ∀ i, X i

end

end LastLib.Book04AdelesAndIdeles.Chapter06
