import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Topology.Algebra.Constructions

namespace LastLib.Book04AdelesAndIdeles.Chapter15

noncomputable section

open Set Filter
open NumberField
open scoped BigOperators RestrictedProduct

/-!
## Shared interfaces for Chapter 15

Mathlib has the restricted-product topology and the finite/full adele rings, but it
does not package the book's idele module, ray-class character API, or the matrix
restricted product.  The definitions below keep the book-facing notation close to
those canonical objects.  In particular, the local groups are genuine Mathlib
general-linear groups and the finite tails are genuine restricted products.
-/

/-! ### Places, local factors, and adelic groups -/

abbrev Chapter15FinitePlace (R : Type*) [CommRing R] :=
  IsDedekindDomain.HeightOneSpectrum R

abbrev Chapter15Place (R K : Type*) [CommRing R] [Field K] :=
  Sum (NumberField.InfinitePlace K) (Chapter15FinitePlace R)

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The completion attached to a finite or infinite place. -/
def chapter15LocalRing (p : Chapter15Place R K) : Type _ :=
  match p with
  | Sum.inl v => v.Completion
  | Sum.inr v => v.adicCompletion K

instance chapter15LocalRingCommRing (p : Chapter15Place R K) :
    CommRing (chapter15LocalRing p) := by
  cases p with
  | inl v =>
      change CommRing (v.Completion)
      infer_instance
  | inr v =>
      change CommRing (v.adicCompletion K)
      infer_instance

/-- The distinguished integral subset at a place; it is unrestricted at infinity. -/
def chapter15LocalIntegerSet (p : Chapter15Place R K) : Set (chapter15LocalRing p) :=
  match p with
  | Sum.inl _ => Set.univ
  | Sum.inr v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))

/-- The finite local integral model inside the field-valued general-linear group. -/
def chapter15FiniteMatrixIntegralSubgroup (n : ℕ) (v : Chapter15FinitePlace R) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :=
  (Matrix.GeneralLinearGroup.map
      (v.adicCompletionIntegers K).subtype).range

/-- The finite local integral model inside the multiplicative group of the field. -/
def chapter15FiniteUnitIntegralSubgroup (v : Chapter15FinitePlace R) :
    Subgroup ((v.adicCompletion K)ˣ) :=
  (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom).range

/-- The local matrix integral subgroup, with no condition at an infinite place. -/
def chapter15LocalMatrixIntegralSubgroup (n : ℕ) (p : Chapter15Place R K) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p)) := by
  cases p with
  | inl v =>
      change Subgroup (Matrix.GeneralLinearGroup (Fin n) v.Completion)
      exact ⊤
  | inr v =>
      change Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
      exact chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v

/-- The local unit integral subgroup, with no condition at an infinite place. -/
def chapter15LocalUnitIntegralSubgroup (p : Chapter15Place R K) :
    Subgroup ((chapter15LocalRing p)ˣ) := by
  cases p with
  | inl v =>
      change Subgroup ((v.Completion)ˣ)
      exact ⊤
  | inr v =>
      change Subgroup ((v.adicCompletion K)ˣ)
      exact chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v

/-- Matrix groups at the infinite places. -/
abbrev Chapter15ArchimedeanMatrixGroup (n : ℕ) (K : Type*) [Field K] :=
  (v : NumberField.InfinitePlace K) →
    Matrix.GeneralLinearGroup (Fin n) v.Completion

/-- The finite adelic matrix group, with the standard integral tail. -/
abbrev Chapter15FiniteMatrixGroup (n : ℕ) (R K : Type*) [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :=
  Πʳ v : Chapter15FinitePlace R,
    [Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K),
      chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v]

/-- The full matrix group as its infinite component times its finite restricted product. -/
abbrev Chapter15AdelicMatrixGroup (n : ℕ) (R K : Type*) [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :=
  Chapter15ArchimedeanMatrixGroup n K × Chapter15FiniteMatrixGroup n R K

/-- The literal all-place restricted product appearing in the book's definition. -/
abbrev Chapter15RestrictedAdelicMatrixGroup (n : ℕ) (R K : Type*) [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :=
  Πʳ p : Chapter15Place R K,
    [Matrix.GeneralLinearGroup (Fin n) (chapter15LocalRing p),
      chapter15LocalMatrixIntegralSubgroup n p]

/-- Unit groups at the infinite places. -/
abbrev Chapter15ArchimedeanIdeleGroup (K : Type*) [Field K] :=
  (v : NumberField.InfinitePlace K) → (v.Completion)ˣ

/-- The finite idele group as a restricted product of local multiplicative groups. -/
abbrev Chapter15FiniteIdeleGroup (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  Πʳ v : Chapter15FinitePlace R,
    [(v.adicCompletion K)ˣ,
      chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v]

/-- The finite standard integral idele level. -/
def chapter15StandardFiniteIdeleLevel :
    Subgroup (Chapter15FiniteIdeleGroup R K) where
  carrier := {g | ∀ v : Chapter15FinitePlace R,
    g v ∈ chapter15FiniteUnitIntegralSubgroup v}
  one_mem' := by
    intro v
    exact (chapter15FiniteUnitIntegralSubgroup v).one_mem
  mul_mem' := by
    intro g h hg hh v
    exact (chapter15FiniteUnitIntegralSubgroup v).mul_mem (hg v) (hh v)
  inv_mem' := by
    intro g hg v
    exact (chapter15FiniteUnitIntegralSubgroup v).inv_mem (hg v)

/-! ### Shared finite matrix levels -/

/-- A finite adelic matrix level together with its local factor description. -/
structure Chapter15FiniteMatrixLevel (n : ℕ) where
  localSubgroup : ∀ v : Chapter15FinitePlace R,
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
  subgroup : Subgroup (Chapter15FiniteMatrixGroup n R K)
  mem_iff : ∀ g, g ∈ subgroup ↔
    ∀ v : Chapter15FinitePlace R, g v ∈ localSubgroup v
  isCompact : IsCompact (subgroup : Set (Chapter15FiniteMatrixGroup n R K))
  isOpen : IsOpen (subgroup : Set (Chapter15FiniteMatrixGroup n R K))
  standard_outside_finite : ∃ S : Finset (Chapter15FinitePlace R),
    ∀ v ∉ S, localSubgroup v = chapter15FiniteMatrixIntegralSubgroup n v

theorem chapter15FiniteMatrixLevel_mem_iff
    (n : ℕ) (L : Chapter15FiniteMatrixLevel (R := R) (K := K) n)
    (g : Chapter15FiniteMatrixGroup n R K) :
    g ∈ L.subgroup ↔ ∀ v, g v ∈ L.localSubgroup v :=
  L.mem_iff g

/-- The idele group, equipped with the graph/restricted-product topology. -/
abbrev Chapter15IdeleGroup (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  Chapter15ArchimedeanIdeleGroup K × Chapter15FiniteIdeleGroup R K

/-- The literal all-place restricted product version of the idele group. -/
abbrev Chapter15RestrictedIdeleGroup (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  Πʳ p : Chapter15Place R K,
    [(chapter15LocalRing p)ˣ, chapter15LocalUnitIntegralSubgroup p]

/-! ### Shared quotient and finite-level interfaces -/

/-- Equality of two representatives in a left/right double quotient. -/
def chapter15DoubleCosetRel {G : Type*} [Group G]
    (H K : Subgroup G) (x y : G) : Prop :=
  ∃ h ∈ H, ∃ k ∈ K, h * x * k = y

def chapter15DoubleCosetSetoid {G : Type*} [Group G]
    (H K : Subgroup G) : Setoid G where
  r := chapter15DoubleCosetRel H K
  iseqv := by
    constructor
    · intro x
      exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    · intro x y ⟨h, hh, k, hk, heq⟩
      refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
      calc
        h⁻¹ * y * k⁻¹ = h⁻¹ * (h * x * k) * k⁻¹ := by rw [← heq]
        _ = h⁻¹ * (h * (x * (k * k⁻¹))) := by simp only [mul_assoc]
        _ = x := by simp
    · intro x y z ⟨h₁, hh₁, k₁, hk₁, hxy⟩ ⟨h₂, hh₂, k₂, hk₂, hyz⟩
      refine ⟨h₂ * h₁, H.mul_mem hh₂ hh₁, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
      rw [← hyz, ← hxy]
      simp only [mul_assoc]

/-- The type `H \ G / K`. -/
abbrev Chapter15DoubleQuotient {G : Type*} [Group G]
    (H K : Subgroup G) :=
  Quotient (chapter15DoubleCosetSetoid H K)

/-- The canonical representative map into a double quotient. -/
def chapter15DoubleQuotientMk {G : Type*} [Group G]
    (H K : Subgroup G) (g : G) :
    Chapter15DoubleQuotient H K := Quotient.mk (chapter15DoubleCosetSetoid H K) g

theorem chapter15DoubleQuotient_mk_eq_iff {G : Type*} [Group G]
    (H K : Subgroup G) (x y : G) :
    chapter15DoubleQuotientMk H K x = chapter15DoubleQuotientMk H K y ↔
      chapter15DoubleCosetRel H K x y := by
  sorry

theorem chapter15DoubleQuotient_mk_eq_of_left_right {G : Type*} [Group G]
    (H K : Subgroup G) {x y : G} (h : G) (hh : h ∈ H) (k : G) (hk : k ∈ K)
    (heq : h * x * k = y) :
    chapter15DoubleQuotientMk H K x = chapter15DoubleQuotientMk H K y := by
  exact (chapter15DoubleQuotient_mk_eq_iff H K _ _).2 ⟨h, hh, k, hk, heq⟩

/-- The canonical full adele ring from pinned Mathlib. -/
abbrev Chapter15AdeleRing (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  NumberField.AdeleRing R K

/-- The units of the full adele ring; this has the induced unit topology. -/
abbrev Chapter15AdeleUnitGroup (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :=
  (Chapter15AdeleRing R K)ˣ

/-! ### Restricted-product identifications -/

/- LOCAL_DEPENDENCY_GUESS: the source uses the standard decomposition of an
all-place restricted product into its finite restricted factor and its finite
archimedean factor.  Pinned Mathlib provides both restricted products and the
number-field finiteness of the infinite places, but not this book-facing
equivalence as a named declaration. -/
def chapter15_restricted_matrix_group_equiv_product
    (n : ℕ) [NumberField K] :
    Chapter15RestrictedAdelicMatrixGroup n R K ≃ₜ*
      Chapter15AdelicMatrixGroup n R K := by
  sorry

def chapter15_restricted_idele_group_equiv_product
    [NumberField K] :
    Chapter15RestrictedIdeleGroup R K ≃ₜ*
      Chapter15IdeleGroup R K := by
  sorry

/- The finite-idele part is the canonical unit restricted product supplied by Mathlib. -/
def chapter15_finite_idele_group_equiv_finite_adele_units :
    Chapter15FiniteIdeleGroup R K ≃*
      (IsDedekindDomain.FiniteAdeleRing R K)ˣ := by
  sorry

def chapter15_finite_idele_group_homeomorph_finite_adele_units
    [NumberField K] :
    Chapter15FiniteIdeleGroup R K ≃ₜ*
      (IsDedekindDomain.FiniteAdeleRing R K)ˣ := by
  sorry

/- The underlying multiplicative groups agree with units of the full adele
ring; the topology on the graph model is kept separate. -/
def chapter15_idele_group_equiv_full_adele_units
    [NumberField K] :
    Chapter15IdeleGroup R K ≃* Chapter15AdeleUnitGroup R K := by
  sorry

/- The graph/restricted-product topology agrees with the induced unit topology
on the canonical full adele ring. -/
def chapter15_idele_group_homeomorph_full_adele_units
    [NumberField K] :
    Chapter15IdeleGroup R K ≃ₜ* Chapter15AdeleUnitGroup R K := by
  sorry

/-! ### Generic predicates used by later sections -/

/-- A family of local assertions holds almost everywhere at finite places. -/
def chapter15AlmostEverywhereFinite (P : Chapter15FinitePlace R → Prop) : Prop :=
  ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite, P v

/-- The matrix-entry formulation of the restricted tail. -/
def chapter15MatrixEntriesIntegralAlmostEverywhere
    (g : Chapter15FiniteMatrixGroup n R K) : Prop :=
  ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
    ∀ i j : Fin n, g v i j ∈ v.adicCompletionIntegers K

/-- The same predicate for the inverse matrix. -/
def chapter15InverseMatrixEntriesIntegralAlmostEverywhere
    (g : Chapter15FiniteMatrixGroup n R K) : Prop :=
  ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
    ∀ i j : Fin n, (g⁻¹) v i j ∈ v.adicCompletionIntegers K

/-- A book-facing full lattice in `K^n`. -/
abbrev Chapter15VectorSpace (n : ℕ) (K : Type*) := Fin n → K

/-- A fractional ideal over the chosen fraction field, using Mathlib's canonical type. -/
abbrev Chapter15FractionalIdeal (R K : Type*) [CommRing R] [Field K]
    [Algebra R K] := FractionalIdeal (nonZeroDivisors R) K

end

end LastLib.Book04AdelesAndIdeles.Chapter15
