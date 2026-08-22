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
  have hclass (z : GaussianInt) (hz : IsUnit z) :
      z = 1 ∨ z = -1 ∨ z = (⟨0, 1⟩ : GaussianInt) ∨
        z = -(⟨0, 1⟩ : GaussianInt) := by
    rcases z with ⟨a, b⟩
    have hn : (⟨a, b⟩ : GaussianInt).norm = 1 :=
      (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) _).2 hz
    have hcoord : a * a + b * b = 1 := by
      simpa [Zsqrtd.norm_def] using hn
    have ha_lower : -1 ≤ a := by
      by_contra h
      have h' : a ≤ -2 := by omega
      nlinarith [sq_nonneg b]
    have ha_upper : a ≤ 1 := by
      by_contra h
      have h' : 2 ≤ a := by omega
      nlinarith [sq_nonneg b]
    have hb_lower : -1 ≤ b := by
      by_contra h
      have h' : b ≤ -2 := by omega
      nlinarith [sq_nonneg a]
    have hb_upper : b ≤ 1 := by
      by_contra h
      have h' : 2 ≤ b := by omega
      nlinarith [sq_nonneg a]
    have ha_cases : a = -1 ∨ a = 0 ∨ a = 1 := by omega
    have hb_cases : b = -1 ∨ b = 0 ∨ b = 1 := by omega
    rcases ha_cases with rfl | rfl | rfl <;>
      rcases hb_cases with rfl | rfl | rfl <;>
      norm_num [Zsqrtd.ext_iff] at hcoord <;>
      norm_num [Zsqrtd.ext_iff]
  have hmap_back (u : (𝓞 K)ˣ) :
      G.ringOfIntegersEquiv.symm
          ((Units.map G.ringOfIntegersEquiv.toMonoidHom u : GaussianIntˣ) : GaussianInt) =
        (u : 𝓞 K) := by
    change G.ringOfIntegersEquiv.symm
        (G.ringOfIntegersEquiv (u : 𝓞 K)) = (u : 𝓞 K)
    simp
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    let z : GaussianIntˣ := Units.map G.ringOfIntegersEquiv.toMonoidHom u
    have hz : IsUnit (z : GaussianInt) := z.isUnit
    have hback := hmap_back u
    rcases hclass (z : GaussianInt) hz with h | h | h | h
    · have hu : (u : 𝓞 K) = 1 := by
        rw [← hback, h]
        simp
      simp [chapter12GaussianUnitValues, hu]
    · have hu : (u : 𝓞 K) = -1 := by
        rw [← hback, h]
        simp
      simp [chapter12GaussianUnitValues, hu]
    · have hu : (u : 𝓞 K) = G.ringOfIntegersEquiv.symm (⟨0, 1⟩ : GaussianInt) := by
        rw [← hback, h]
      simp [chapter12GaussianUnitValues, hu, G.ringOfIntegers_i]
    · have hu : (u : 𝓞 K) = -G.ringOfIntegersEquiv.symm (⟨0, 1⟩ : GaussianInt) := by
        rw [← hback, h]
        simp
      simp [chapter12GaussianUnitValues, hu, G.ringOfIntegers_i]
  · intro hx
    simp only [chapter12GaussianUnitValues, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩
    · let q : GaussianIntˣ := Units.mk (⟨0, 1⟩ : GaussianInt) (⟨0, -1⟩ : GaussianInt) (by
        norm_num [Zsqrtd.ext_iff]) (by norm_num [Zsqrtd.ext_iff])
      let u : (𝓞 K)ˣ := Units.map G.ringOfIntegersEquiv.symm.toMonoidHom q
      refine ⟨u, ?_⟩
      simp [u, q, G.ringOfIntegers_i]
    · let q : GaussianIntˣ := Units.mk (⟨0, -1⟩ : GaussianInt) (⟨0, 1⟩ : GaussianInt) (by
        norm_num [Zsqrtd.ext_iff]) (by norm_num [Zsqrtd.ext_iff])
      let u : (𝓞 K)ˣ := Units.map G.ringOfIntegersEquiv.symm.toMonoidHom q
      refine ⟨u, ?_⟩
      change algebraMap (𝓞 K) K
        (G.ringOfIntegersEquiv.symm (⟨0, -1⟩ : GaussianInt)) = -G.i
      rw [show (⟨0, -1⟩ : GaussianInt) = -(⟨0, 1⟩ : GaussianInt) by
        norm_num [Zsqrtd.ext_iff], map_neg, map_neg, G.ringOfIntegers_i]

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
  classical
  have hno_real_embedding (φ : K →+* ℂ) :
      ¬ComplexEmbedding.IsReal φ := by
    intro hφ
    have hre : hφ.embedding G.i ^ 2 = (-1 : ℝ) := by
      rw [← map_pow, G.i_sq, map_neg, map_one]
    nlinarith [sq_nonneg (hφ.embedding G.i)]
  have hno_real : ∀ v : InfinitePlace K, ¬IsReal v := by
    intro v hv
    exact hno_real_embedding v.embedding (isReal_iff.mp hv)
  have hreal_empty : IsEmpty {v : InfinitePlace K // IsReal v} := by
    exact ⟨fun v => hno_real v.1 v.2⟩
  have hreal : nrRealPlaces K = 0 :=
    Fintype.card_eq_zero_iff.mpr hreal_empty
  have halg : (‹Algebra ℚ K› : Algebra ℚ K) =
      (DivisionRing.toRatAlgebra : Algebra ℚ K) :=
    Subsingleton.elim _ _
  have hrank := card_add_two_mul_card_eq_rank K
  have hdegree := G.degree_two
  have hmodule : (‹Algebra ℚ K› : Algebra ℚ K).toModule =
      (DivisionRing.toRatAlgebra : Algebra ℚ K).toModule :=
    congrArg (fun A : Algebra ℚ K => A.toModule) halg
  rw [hmodule] at hdegree
  have hrank' : nrRealPlaces K + 2 * nrComplexPlaces K = 2 := by
    exact hrank.trans hdegree
  rw [hreal] at hrank'
  have hcomplex : nrComplexPlaces K = 1 := by omega
  let v : InfinitePlace K := InfinitePlace.mk G.complexEmbedding
  have hvcomplex₀ : IsComplex (InfinitePlace.mk G.complexEmbedding) := by
    apply isComplex_iff.mpr
    intro hreal
    rcases embedding_mk_eq G.complexEmbedding with h | h
    · exact hno_real_embedding G.complexEmbedding (h ▸ hreal)
    · exact hno_real_embedding G.complexEmbedding
        (ComplexEmbedding.isReal_conjugate_iff.mp (h ▸ hreal))
  have hvcomplex : IsComplex v := by
    simpa [v] using hvcomplex₀
  have hplaces : Fintype.card (InfinitePlace K) = 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, hreal, hcomplex]
  obtain ⟨w, hw⟩ := (Fintype.card_eq_one_iff.mp hplaces)
  have hv : ∀ w' : InfinitePlace K, w' = v := by
    intro w'
    exact (hw w').trans (hw v).symm
  let _ : Unique (InfinitePlace K) :=
    { default := v
      uniq := hv }
  let e : chapter12InfiniteAdeleRing K ≃+* ℂ :=
    (RingEquiv.piUnique (fun w : InfinitePlace K => w.Completion)).trans
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvcomplex)
  exact ⟨{ no_real_place := hno_real, unique_complex_place :=
    ⟨v, hvcomplex, fun w hw => hv w⟩, equiv := e }⟩

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
  unfold chapter12GaussianClassNumberOne
  let _ : IsPrincipalIdealRing (𝓞 K) :=
    IsPrincipalIdealRing.of_surjective G.ringOfIntegersEquiv.symm.toRingHom
      G.ringOfIntegersEquiv.symm.surjective
  have hcard : Fintype.card (ClassGroup (𝓞 K)) = 1 :=
    (card_classGroup_eq_one_iff).2 inferInstance
  obtain ⟨c, hc⟩ := (Fintype.card_eq_one_iff).1 hcard
  exact ⟨fun x y => (hc x).trans (hc y).symm⟩

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
