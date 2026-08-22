import LastLib.Book04AdelesAndIdeles.Chapter12.Core
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.NumberField.Discriminant.Different

namespace LastLib.Book04AdelesAndIdeles.Chapter12

noncomputable section

open Set NumberField
open NumberField.InfinitePlace
open LastLib.Book04AdelesAndIdeles.Chapter09
open scoped BigOperators TensorProduct

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! # Book 4, Chapter 12, §12.2: The Gaussian field -/

/- A concrete model is kept as data so later repairs can replace it by the
   canonical quadratic-field construction without changing the chapter API. -/
structure Chapter12GaussianFieldData
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K] where
  i : K
  i_sq : i ^ 2 = -1
  degree_two : Module.finrank ℚ K = 2
  generates : Algebra.adjoin ℚ ({i} : Set K) = ⊤
  complexEmbedding : K →+* ℂ
  complexEmbedding_i : complexEmbedding i = Complex.I
  ringOfIntegersEquiv : 𝓞 K ≃+* GaussianInt
  ringOfIntegers_i :
    algebraMap (𝓞 K) K (ringOfIntegersEquiv.symm (⟨0, 1⟩ : GaussianInt)) = i

def chapter12GaussianUnitValues
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) : Set K :=
  {1, -1, G.i, -G.i}

theorem chapter12_gaussian_unit_values
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) :
    Set.range (fun u : (𝓞 K)ˣ =>
      (algebraMap (𝓞 K) K (u : 𝓞 K) : K)) = chapter12GaussianUnitValues G := by
  sorry

/- The one complex place and no real places, together with the resulting
   archimedean product, are recorded in one reusable portrait. -/
structure Chapter12GaussianInfinitePortrait
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) where
  no_real_place : ∀ v : InfinitePlace K, ¬IsReal v
  unique_complex_place : ∃! v : InfinitePlace K, IsComplex v
  equiv : chapter12InfiniteAdeleRing K ≃+* ℂ

theorem chapter12_gaussian_has_one_complex_place
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) :
    Nonempty (Chapter12GaussianInfinitePortrait G) := by
  sorry

/-- The normalized complex absolute value used by the product formula. -/
def chapter12GaussianNormalizedAbsoluteValue (z : ℂ) : ℝ :=
  ‖z‖ ^ 2

theorem chapter12_gaussian_normalized_absolute_value_formula (z : ℂ) :
    chapter12GaussianNormalizedAbsoluteValue z = ‖z‖ ^ 2 :=
  rfl

def chapter12DirichletUnitRank (r₁ r₂ : ℕ) : ℕ := r₁ + r₂ - 1

theorem chapter12_gaussian_unit_rank_zero :
    chapter12DirichletUnitRank 0 1 = 0 := by
  simp [chapter12DirichletUnitRank]

def chapter12GaussianClassNumberOne
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (_G : Chapter12GaussianFieldData K) : Prop :=
  Subsingleton (ClassGroup (𝓞 K))

theorem chapter12_gaussian_class_number_one
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) :
    chapter12GaussianClassNumberOne G := by
  sorry

/-! ## The norm-one class quotient -/

def chapter12UnitCircleSubgroup : Subgroup ℂˣ where
  carrier := {z | ‖(z : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    sorry
  inv_mem' := by
    intro x hx
    simpa [norm_inv, hx]

abbrev chapter12UnitCircle := chapter12UnitCircleSubgroup

abbrev chapter12GaussianProfiniteUnitGroup
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] :=
  chapter12CanonicalFiniteUnitIdeles K

structure Chapter12GaussianDiagonalUnitData
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) where
  finiteUnitEmbedding : (𝓞 K)ˣ →*
    chapter12GaussianProfiniteUnitGroup (K := K)
  circleUnitValue : (𝓞 K)ˣ →* chapter12UnitCircle

def chapter12GaussianCanonicalDiagonalUnitData
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) :
    Chapter12GaussianDiagonalUnitData G where
  finiteUnitEmbedding :=
    chapter09FiniteUnitSubtypeEmbedding K
  circleUnitValue :=
    { toFun := fun u =>
        ⟨Units.map (G.complexEmbedding.comp (algebraMap (𝓞 K) K)) u, by
          sorry⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro u v
        ext
        simp }

def chapter12GaussianDiagonalUnitHom
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    {G : Chapter12GaussianFieldData K}
    (D : Chapter12GaussianDiagonalUnitData G) :
    (𝓞 K)ˣ →* (chapter12UnitCircle × chapter12GaussianProfiniteUnitGroup (K := K)) where
  toFun u := (D.circleUnitValue u, D.finiteUnitEmbedding u)
  map_one' := by simp
  map_mul' u v := by simp

def chapter12GaussianDiagonalUnitSubgroup
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    {G : Chapter12GaussianFieldData K}
    (D : Chapter12GaussianDiagonalUnitData G) :
    Subgroup (chapter12UnitCircle × chapter12GaussianProfiniteUnitGroup (K := K)) :=
  (chapter12GaussianDiagonalUnitHom D).range

abbrev chapter12GaussianDiagonalUnitQuotient
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    {G : Chapter12GaussianFieldData K}
    (D : Chapter12GaussianDiagonalUnitData G) :=
  (chapter12UnitCircle × chapter12GaussianProfiniteUnitGroup (K := K)) ⧸
    chapter12GaussianDiagonalUnitSubgroup D

abbrev chapter12GaussianNormOneClassCarrier
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (M : Chapter12IdeleModuleData (𝓞 K) K) :=
  chapter12NormOneIdeleClassCarrier M

theorem chapter12_gaussian_norm_one_class_is_diagonal_unit_quotient
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) :
    Nonempty (chapter12GaussianNormOneClassCarrier
      (chapter12CanonicalIdeleModuleData K) ≃*
      chapter12GaussianDiagonalUnitQuotient
        (chapter12GaussianCanonicalDiagonalUnitData G)) := by
  sorry

theorem chapter12_gaussian_norm_one_diagonal_quotient_is_compact
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) :
    IsCompact (Set.univ : Set (chapter12GaussianDiagonalUnitQuotient
      (chapter12GaussianCanonicalDiagonalUnitData G))) := by
  sorry

/-! ## Prime behavior and scalar extension -/

def chapter12GaussianPrimeBehavior (p : ℕ) :
    Chapter12QuadraticLocalBehavior :=
  if p = 2 then .ramified else if p % 4 = 1 then .split else .inert

theorem chapter12_gaussian_prime_behavior
    (p : ℕ) (hp : p.Prime) :
    (p = 2 ∧ chapter12GaussianPrimeBehavior p = .ramified) ∨
      (p % 4 = 1 ∧ chapter12GaussianPrimeBehavior p = .split) ∨
      (p % 4 = 3 ∧ chapter12GaussianPrimeBehavior p = .inert) := by
  sorry

theorem chapter12_gaussian_split_local_tensor_shape
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K)
    (p : Nat.Primes) (hcongr : p.1 % 4 = 1) :
    chapter12TensorSplitShape K ℚ_[p] := by
  sorry

/- The inert factor is existential data because the chosen carrier for the
   quadratic local field is not canonical in the available API.  The tensor
   equivalence is part of the data, so the factor cannot be unrelated to the
   scalar extension. -/
structure Chapter12GaussianInertLocalFactorData
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) (p : Nat.Primes) where
  E : Type*
  [fieldE : Field E]
  [algebraE : Algebra ℚ_[p] E]
  [finiteDimensionalE : FiniteDimensional ℚ_[p] E]
  [unramifiedE : Algebra.Unramified ℚ_[p] E]
  degree_two : Module.finrank ℚ_[p] E = 2
  tensor_shape : chapter12TensorFieldShape K ℚ_[p] E

theorem chapter12_gaussian_inert_local_tensor_shape
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) (p : Nat.Primes)
    (hcongr : p.1 % 4 = 3) :
    Nonempty (Chapter12GaussianInertLocalFactorData G p) := by
  sorry

/- The ramified prime is represented by a quadratic field factor of the same
   scalar extension, together with the global ramification certificate at 2.
   This keeps the factor tied to `K ⊗[ℚ] ℚ_[2]` rather than treating any
   quadratic field over `ℚ_[2]` as the Gaussian completion. -/
structure Chapter12GaussianRamifiedLocalFactorData
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) where
  E : Type*
  [fieldE : Field E]
  [algebraE : Algebra ℚ_[2] E]
  [finiteDimensionalE : FiniteDimensional ℚ_[2] E]
  degree_two : Module.finrank ℚ_[2] E = 2
  tensor_shape : chapter12TensorFieldShape K ℚ_[2] E
  ramified_at_two : ¬Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(2 : ℤ)})

theorem chapter12_gaussian_ramified_local_tensor_shape
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) :
    Nonempty (Chapter12GaussianRamifiedLocalFactorData G) := by
  sorry

/-- Scalar extension is the adelic identity used at split and nonsplit places. -/
abbrev chapter12AdeleScalarExtension
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] :=
  K ⊗[ℚ] chapter12RationalAdeleRing

theorem chapter12_gaussian_adelic_scalar_extension
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] :
    Nonempty (chapter12AdeleRing (𝓞 K) K ≃+*
      chapter12AdeleScalarExtension (K := K)) := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter12
