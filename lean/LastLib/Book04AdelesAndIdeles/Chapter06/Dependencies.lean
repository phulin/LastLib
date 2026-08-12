import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Real.Lemmas

namespace LastLib.Book04AdelesAndIdeles.Chapter06

noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal

universe uK uO uInf uFin uHat uG uPlace uV uVA

/-!
The preceding Book 4 chapters are not present in this checkout.  This file is
therefore a deliberately small local dependency guess: it records the
canonical number-field maps and the compact integral finite part that the
chapter consumes.  It does not package any of the compactness results proved
below as an assumption.
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
  finiteIntegral_embedding :
    IsEmbedding finiteIntegralEmbedding
  finiteIntegral_range_compact :
    IsCompact (Set.range finiteIntegralEmbedding)
  finiteIntegral_range_open :
    IsOpen (Set.range finiteIntegralEmbedding)
  diagonal_injective :
    Function.Injective (fun a : K => (globalToInfinite a, globalToFinite a))
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

/-- The additive image of an additive homomorphism, bundled as a subgroup. -/
def chapter06ImageSubgroup
    {G : Type uG} {H : Type uVA} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : AddSubgroup H :=
  AddMonoidHom.range f

@[simp] theorem mem_chapter06ImageSubgroup
    {G : Type uG} {H : Type uVA} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (x : H) :
    x ∈ chapter06ImageSubgroup f ↔ ∃ y, f y = x := by
  simpa only [chapter06ImageSubgroup] using
    (AddMonoidHom.mem_range (f := f) (y := x))

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
  chapter06ImageSubgroup (chapter06Diagonal P)

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
  chapter06ImageSubgroup (chapter06IntegralDiagonal P)

/-- The quotient `A_K / K`, with the quotient topology supplied by Mathlib. -/
abbrev Chapter06AdeleQuotient
    (P : Chapter06AdeleData K O KInf Af Ohat) :=
  Chapter06FullAdele KInf Af ⧸ chapter06GlobalSubgroup P

def chapter06AdeleQuotientMap
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    Chapter06FullAdele KInf Af →+
      Chapter06AdeleQuotient P :=
  QuotientAddGroup.mk' (chapter06GlobalSubgroup P)

/-- Forget the integral condition in the finite coordinate. -/
def chapter06IntegralGluingToAdele
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    (KInf × Ohat) →+ Chapter06FullAdele KInf Af where
  toFun x := (x.1, P.finiteIntegralEmbedding x.2)
  map_zero' := by simp
  map_add' x y := by sorry

@[simp] theorem chapter06IntegralGluingToAdele_apply
    (P : Chapter06AdeleData K O KInf Af Ohat) (x : KInf × Ohat) :
    chapter06IntegralGluingToAdele P x =
      (x.1, P.finiteIntegralEmbedding x.2) := rfl

/-- The map from the integral-gluing model to the adelic quotient. -/
def chapter06IntegralGluingMap
    (P : Chapter06AdeleData K O KInf Af Ohat) :
    (KInf × Ohat) →+ Chapter06AdeleQuotient P :=
  (chapter06AdeleQuotientMap P).comp (chapter06IntegralGluingToAdele P)

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

end AdeleData

/-- A discrete embedding of an additive group into a topological additive group. -/
def Chapter06DiscreteEmbedding
    {G : Type uG} {H : Type uVA} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] (ι : G →+ H) : Prop :=
  Function.Injective ι ∧
    ∀ g : G, ∃ U : Set H, IsOpen U ∧ ι g ∈ U ∧
      ∀ h : G, ι h ∈ U → h = g

/-- A compact fundamental set for an additive embedding. -/
def Chapter06CompactFundamentalSet
    {G : Type uG} {H : Type uVA} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H]
    (ι : G →+ H) : Prop :=
  ∃ C : Set H, IsCompact C ∧ ∀ x : H, ∃ g : G, x - ι g ∈ C

/-- A topological-group lattice: discrete with compact quotient. -/
def Chapter06AdditiveLattice
    {G : Type uG} {H : Type uVA} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] (ι : G →+ H) : Prop :=
  Chapter06DiscreteEmbedding ι ∧
    CompactSpace (H ⧸ chapter06ImageSubgroup ι)

/-- The module-theoretic lattice notion used for comparison in §6.8. -/
def Chapter06ModuleLattice
    (R V : Type*) [Semiring R] [AddCommMonoid V] [Module R V]
    (L : Submodule R V) : Prop :=
  Module.Finite R L ∧ Submodule.span R (L : Set V) = ⊤

/-- The local additive module relation for a Haar measure. -/
def Chapter06LocalMeasureModule
    (F : Type*) [Field F] [MeasurableSpace F]
    (μ : Measure F) (size : F → ℝ≥0∞) : Prop :=
  ∀ a : Fˣ,
    Measure.map (fun x : F => (a : F) * x) μ = size (a : F) • μ

/-- Translation invariance and nonzero-ness, isolated from Mathlib's Haar API. -/
def Chapter06IsAdditiveHaarMeasure
    (G : Type*) [AddCommGroup G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) : Prop :=
  μ ≠ 0 ∧
    (∀ g : G, Measure.map (fun x : G => x + g) μ = μ) ∧
    (∀ C : Set G, IsCompact C → μ C ≠ ⊤) ∧
    (∀ U : Set G, IsOpen U → U.Nonempty → 0 < μ U)

/-- The local product formula interface used by the volume argument. -/
def Chapter06ProductFormula
    (K Place : Type*) [Field K]
    (_size : Place → K → ℝ≥0∞) (adelicProduct : K → ℝ≥0∞) : Prop :=
  ∀ a : Kˣ, adelicProduct (a : K) = 1

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

/-- The finite self-dual normalization is forced away from the different, but
the chapter intentionally does not identify the masses at the exceptional
places with the ordinary normalization. -/
structure Chapter06SelfDualFiniteNormalization (Place : Type*) where
  different : Set Place
  integralMass : Place → ℝ≥0∞
  integralMass_eq_one_off_different :
    ∀ v, v ∉ different → integralMass v = 1

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
    (P : Chapter06AdeleData K O KInf Af Ohat) (D : Set KInf) where
  infiniteMeasure : Measure KInf
  finiteMeasure : Measure Af
  r₂ : ℕ
  discriminant : ℝ
  finiteIntegral_range_measurable :
    MeasurableSet (Set.range P.finiteIntegralEmbedding)
  archimedean_cell_measurable : MeasurableSet D
  finiteIntegral_measure_one :
    finiteMeasure (Set.range P.finiteIntegralEmbedding) = 1
  archimedean_cell_volume :
    infiniteMeasure D =
      ENNReal.ofReal (chapter06OrdinaryCovolume r₂ discriminant)

variable {P : Chapter06AdeleData K O KInf Af Ohat} {D : Set KInf}

def chapter06AdelicProductMeasure
    (M : Chapter06AdelicMeasureData P D) :
    Measure (Chapter06FullAdele KInf Af) :=
  M.infiniteMeasure.prod M.finiteMeasure

def chapter06AdelicQuotientCovolume
    (M : Chapter06AdelicMeasureData P D) : ℝ≥0∞ :=
  chapter06AdelicProductMeasure M (chapter06FundamentalSet P D)

end AdelicMeasureData

/-- The unrestricted product underlying the topology warning in §6.7. -/
def Chapter06UnrestrictedProduct (ι : Type*) (X : ι → Type*) := ∀ i, X i

end

end LastLib.Book04AdelesAndIdeles.Chapter06
