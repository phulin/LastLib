import LastLib.Book04AdelesAndIdeles.Chapter12.Core
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

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
  {c : chapter12IdeleClassGroup (𝓞 K) K // c ∈ chapter12NormOneIdeleClasses M}

theorem chapter12_gaussian_norm_one_class_is_diagonal_unit_quotient
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (G : Chapter12GaussianFieldData K) :
    Nonempty (chapter12GaussianNormOneClassCarrier
      (chapter12CanonicalIdeleModuleData K) ≃
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

/- LOCAL_DEPENDENCY_GUESS: `E` is the canonical quadratic local factor of
   `K ⊗[ℚ] ℚ_[p]`; the pinned APIs do not yet expose its chosen carrier. -/
theorem chapter12_gaussian_inert_local_tensor_shape
    {K E : Type*} [Field K] [Field E] [NumberField K]
    [Algebra ℚ K]
    (p : Nat.Primes) [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    [Algebra.Unramified ℚ_[p] E]
    (G : Chapter12GaussianFieldData K)
    (hcongr : p.1 % 4 = 3)
    (hdegree : Module.finrank ℚ_[p] E = 2) :
    chapter12TensorFieldShape K ℚ_[p] E := by
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
