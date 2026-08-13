import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LastLib.Book04AdelesAndIdeles.Chapter09.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter12

noncomputable section

open Filter Set
open NumberField
open LastLib.Book04AdelesAndIdeles.Chapter09
open scoped BigOperators NNReal RestrictedProduct TensorProduct nonZeroDivisors

/-!
Shared interfaces for Book 4, Chapter 12.

Mathlib supplies the finite and infinite adele rings and the restricted-product
unit equivalence.  The preceding idele chapters supply canonical number-field
module and valuation-to-ideal APIs; the generic portrait interfaces below keep
explicit data where a model-independent ray-level bridge is still needed.
-/

/-! ## Canonical adelic and idelic carriers -/

/-- The finite adele ring of a Dedekind domain and its fraction field. -/
abbrev chapter12FiniteAdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  IsDedekindDomain.FiniteAdeleRing R K

/-- The full adele ring of a Dedekind domain and its fraction field. -/
abbrev chapter12AdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  NumberField.AdeleRing R K

/-- The infinite adele ring of a field. -/
abbrev chapter12InfiniteAdeleRing (K : Type*) [Field K] :=
  NumberField.InfiniteAdeleRing K

/-- The finite ideles, defined canonically as units of the finite adele ring. -/
abbrev chapter12FiniteIdeles (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  (chapter12FiniteAdeleRing R K)ˣ

/-- The ideles, defined canonically as units of the full adele ring. -/
abbrev chapter12Ideles (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  (chapter12AdeleRing R K)ˣ

/-- The rational finite adeles, with the integral model `ℤ`. -/
abbrev chapter12RationalFiniteAdeleRing :=
  chapter12FiniteAdeleRing ℤ ℚ

/-- The rational adeles, with the integral model `ℤ`. -/
abbrev chapter12RationalAdeleRing :=
  chapter12AdeleRing ℤ ℚ

/-- The rational finite ideles. -/
abbrev chapter12RationalFiniteIdeles :=
  chapter12FiniteIdeles ℤ ℚ

/-- The rational ideles. -/
abbrev chapter12RationalIdeles :=
  chapter12Ideles ℤ ℚ

/-- The profinite integral coordinates in the rational finite adeles. -/
abbrev chapter12RationalProfiniteIntegers :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ

/-- The product of local integral unit groups, the unit analogue of `Ẑ`. -/
abbrev chapter12RationalProfiniteUnitGroup :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, (v.adicCompletionIntegers ℚ)ˣ

/-- A restricted product written without relying on a chapter-specific notation. -/
abbrev chapter12RestrictedProduct (ι : Type*) (R : ι → Type*)
    (A : ∀ i, Set (R i)) :=
  RestrictedProduct R A Filter.cofinite

@[simp]
theorem chapter12_restricted_product_eventually
    {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)}
    (x : chapter12RestrictedProduct ι R A) :
    ∀ᶠ i in Filter.cofinite, x i ∈ A i :=
  x.2

/-- The coordinate of a finite adele at a finite place. -/
def chapter12FiniteAdeleCoordinate
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter12FiniteAdeleRing R K)
    (v : IsDedekindDomain.HeightOneSpectrum R) : v.adicCompletion K :=
  x v

@[simp]
theorem chapter12_finite_adele_coordinate_apply
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter12FiniteAdeleRing R K)
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    chapter12FiniteAdeleCoordinate x v = x v :=
  rfl

theorem chapter12_finite_adele_is_integral_at_cofinitely_many_places
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter12FiniteAdeleRing R K) :
    ∀ᶠ v in Filter.cofinite,
      chapter12FiniteAdeleCoordinate x v ∈ v.adicCompletionIntegers K :=
  x.2

/-- The canonical finite-idele embedding of the global units. -/
def chapter12PrincipalFiniteIdeleHom
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Kˣ →* chapter12FiniteIdeles R K :=
  IsDedekindDomain.FiniteAdeleRing.unitEmbedding R K

/-- The canonical principal-idele homomorphism. -/
def chapter12PrincipalIdeleHom
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Kˣ →* chapter12Ideles R K :=
  Units.map (algebraMap K (chapter12AdeleRing R K))

/-- The subgroup of principal ideles. -/
def chapter12PrincipalIdeleSubgroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Subgroup (chapter12Ideles R K) :=
  (chapter12PrincipalIdeleHom R K).range

/-- The idele class group, as the quotient by principal ideles. -/
abbrev chapter12IdeleClassGroup
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :=
  chapter12Ideles R K ⧸ chapter12PrincipalIdeleSubgroup R K

/-- The quotient map from ideles to the idele class group. -/
def chapter12IdeleClassMk
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    chapter12Ideles R K →* chapter12IdeleClassGroup R K :=
  QuotientGroup.mk' (chapter12PrincipalIdeleSubgroup R K)

@[simp]
theorem chapter12_principal_finite_idele_hom_apply
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (u : Kˣ) :
    chapter12PrincipalFiniteIdeleHom R K u =
      IsDedekindDomain.FiniteAdeleRing.unitEmbedding R K u :=
  rfl

@[simp]
theorem chapter12_principal_idele_hom_apply
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (u : Kˣ) :
    chapter12PrincipalIdeleHom R K u =
      Units.map (algebraMap K (chapter12AdeleRing R K)) u :=
  rfl

/-! ## The book-facing module and finite-place ideal interfaces -/

/- The generic fields below retain a book-facing interface for arbitrary
   Dedekind models; number-field portraits use the canonical specialization
   `chapter12CanonicalIdeleModuleData` above. -/
structure Chapter12IdeleModuleData
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] where
  module : chapter12Ideles R K →* ℝ≥0
  principal_one : ∀ u : Kˣ, module (chapter12PrincipalIdeleHom R K u) = 1
  module_ne_zero : ∀ x, module x ≠ 0

def chapter12IdeleModule
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (M : Chapter12IdeleModuleData R K) : chapter12Ideles R K →* ℝ≥0 :=
  M.module

def chapter12IdeleModuleUnit
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (M : Chapter12IdeleModuleData R K) (x : chapter12Ideles R K) : ℝ≥0ˣ :=
  Units.mk0 (M.module x) (M.module_ne_zero x)

/-! The number-field module is already available from the preceding idele
chapter.  Keep the generic data structure above for interfaces over a
Dedekind model, but use this canonical specialization for portraits of a
number field. -/

def chapter12CanonicalIdeleModuleData
    (K : Type*) [Field K] [NumberField K] :
    Chapter12IdeleModuleData (𝓞 K) K where
  module := (Units.coeHom ℝ≥0).comp (chapter09IdeleModuleHom K)
  principal_one := by
    intro u
    sorry
  module_ne_zero := by
    intro x
    exact Units.ne_zero _

/-- The finite-unit factor in the canonical number-field idele decomposition. -/
abbrev chapter12CanonicalFiniteUnitIdeles
    (K : Type*) [Field K] [NumberField K] :=
  ↥(chapter09FiniteUnitIdeles K)

def chapter12NormOneIdeleClasses
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (M : Chapter12IdeleModuleData R K) :
    Set (chapter12IdeleClassGroup R K) :=
  {c | ∃ x : chapter12Ideles R K,
    M.module x = 1 ∧ chapter12IdeleClassMk R K x = c}

theorem chapter12_mem_norm_one_idele_classes_iff
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (M : Chapter12IdeleModuleData R K)
    (c : chapter12IdeleClassGroup R K) :
    c ∈ chapter12NormOneIdeleClasses M ↔
      ∃ x : chapter12Ideles R K,
        M.module x = 1 ∧ chapter12IdeleClassMk R K x = c :=
  Iff.rfl

/- A local uniformizer is a nonzero element of the completed integer ring with
valuation `WithZero.exp (-1)`.  Merely requiring a nonzero nonunit would also
allow higher powers of a uniformizer and is not sufficient for a single-place
idele. -/
def chapter12UniformizerAt
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (p : IsDedekindDomain.HeightOneSpectrum R)
    (π : p.adicCompletionIntegers K) : Prop :=
  π ≠ 0 ∧ Valued.v (π : p.adicCompletion K) = WithZero.exp (-1 : ℤ)

/- LOCAL_DEPENDENCY_GUESS: this interface is the valuation-vector-to-fractional-
ideal map used by the ideal/idele dictionary.  Its multiplicativity and
principal normalization are stated as reusable fields rather than assumed
ad hoc in the nonprincipal-ideal example. -/
structure Chapter12FiniteIdeleIdealData
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] where
  idealOf : chapter12FiniteIdeles R K → FractionalIdeal R⁰ K
  map_one : idealOf 1 = 1
  map_mul : ∀ x y, idealOf (x * y) = idealOf x * idealOf y
  principal : ∀ u : Kˣ, idealOf (chapter12PrincipalFiniteIdeleHom R K u) =
    FractionalIdeal.spanSingleton R⁰ (u : K)

def chapter12IdeleIdeal
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (D : Chapter12FiniteIdeleIdealData R K)
    (x : chapter12FiniteIdeles R K) : FractionalIdeal R⁰ K :=
  D.idealOf x

def chapter12SameFiniteIdeleValuation
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (D : Chapter12FiniteIdeleIdealData R K)
    (x y : chapter12FiniteIdeles R K) : Prop :=
  D.idealOf x = D.idealOf y

theorem chapter12_same_finite_idele_valuation_iff
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (D : Chapter12FiniteIdeleIdealData R K)
    (x y : chapter12FiniteIdeles R K) :
    chapter12SameFiniteIdeleValuation D x y ↔ D.idealOf x = D.idealOf y :=
  Iff.rfl

/- LOCAL_DEPENDENCY_GUESS: ray quotients require a congruence-level map in
   addition to the ordinary ideal map.  The interface records exactly that a
   ray invariant refines the ideal class and can detect a prescribed local
   unit change. -/
structure Chapter12RayDetectionData
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] where
  idealData : Chapter12FiniteIdeleIdealData R K
  quotient : Type*
  [quotientGroup : Group quotient]
  rayMap : chapter12FiniteIdeles R K →* quotient
  rayMap_sees_ideal : ∀ x y,
    rayMap x = rayMap y → idealData.idealOf x = idealData.idealOf y

def chapter12CompactModulo {V : Type*} [AddGroup V] [TopologicalSpace V] (L : Set V) : Prop :=
  ∃ F : Set V, IsCompact F ∧ ∀ x : V, ∃ l ∈ L, x - l ∈ F

/-! ## Small local-shape interfaces used by the explicit portraits -/

def chapter12CoordinateProductNorm {F : Type*} [CommMonoid F] (d : ℕ) :
    (Fin d → F) →* F where
  toFun y := ∏ i, y i
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

@[simp]
theorem chapter12_coordinate_product_norm_apply
    {F : Type*} [CommMonoid F] (d : ℕ) (y : Fin d → F) :
    chapter12CoordinateProductNorm d y = ∏ i, y i :=
  rfl

theorem chapter12_coordinate_product_norm_surjective
    {F : Type*} [CommMonoid F] (d : ℕ) [NeZero d] :
    Function.Surjective (chapter12CoordinateProductNorm (F := F) d) := by
  sorry

/- The right-factor algebra on a tensor product is deliberately not a global
   Mathlib instance.  Keep the canonical instance local to this reusable
   equivalence type instead of introducing an ambiguous global instance. -/
abbrev chapter12TensorAlgEquiv
    (R A B C : Type*) [CommSemiring R] [Semiring A] [CommSemiring B]
    [Semiring C] [Algebra R A] [Algebra R B] [Algebra B C] :=
  letI : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  A ⊗[R] B ≃ₐ[B] C

/- A split local tensor shape and a one-field local tensor shape. -/
def chapter12TensorSplitShape (K F : Type*) [Field K] [Field F]
    [Algebra ℚ K] [Algebra ℚ F] : Prop :=
  Nonempty (chapter12TensorAlgEquiv ℚ K F (F × F))

def chapter12TensorFieldShape (K F E : Type*) [Field K] [Field F] [Field E]
    [Algebra ℚ K] [Algebra ℚ F] [Algebra F E] : Prop :=
  Nonempty (chapter12TensorAlgEquiv ℚ K F E)

def chapter12IntegralTensorSplitShape (A B : Type*) [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B] : Prop :=
  Nonempty (A ⊗[ℤ] B ≃+* B × B)

def chapter12IntegralTensorQuadraticFieldShape (A B E : Type*) [CommRing A]
    [CommRing B] [CommRing E] [Algebra ℤ A] [Algebra ℤ B] [Algebra B E] : Prop :=
  Nonempty (A ⊗[ℤ] B ≃+* E)

/- A predicate spelling out the squarefree quadratic input. -/
def chapter12SquarefreeInteger (d : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬((p : ℤ) ^ 2 ∣ d)

def chapter12QuadraticGenerator {K : Type*} [Field K] [Algebra ℚ K]
    (d : ℤ) (θ : K) : Prop :=
  θ ^ 2 = (d : K) ∧ Module.finrank ℚ K = 2 ∧
    Algebra.adjoin ℚ ({θ} : Set K) = ⊤

def chapter12QuadraticDiscriminant (d : ℤ) : ℤ :=
  if d % 4 = 1 then d else 4 * d

inductive Chapter12QuadraticLocalBehavior
  | split
  | inert
  | ramified
  deriving DecidableEq, Repr

/- LOCAL_DEPENDENCY_GUESS: this is only the discriminant-support predicate;
   identifying it with local ramification needs the canonical finite-place
   ramification interface for quadratic number fields. -/
def chapter12QuadraticDiscriminantSupport (d : ℤ) (p : ℕ) : Prop :=
  p ∣ (chapter12QuadraticDiscriminant d).natAbs

/- The normalized product formula supplied by Mathlib for infinite adeles. -/
theorem chapter12_infinite_adele_product_formula
    {K : Type*} [Field K] [NumberField K] (x : K) :
    ‖algebraMap K (chapter12InfiniteAdeleRing K) x‖ =
      |Algebra.norm ℚ x| := by
  simpa only [chapter12InfiniteAdeleRing] using
    NumberField.InfiniteAdeleRing.coe_norm_eq_abs_norm x

end
end LastLib.Book04AdelesAndIdeles.Chapter12
