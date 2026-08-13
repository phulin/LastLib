import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section05SeveralExtensionsAndTheFundamentalEquality
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section03IntegralElementsAreBounded
import Mathlib.Analysis.Normed.Unbundled.FiniteExtension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

universe u10K u10L u10Γ

open scoped BigOperators TensorProduct WithZero
open Polynomial

noncomputable section

/-!
# Chapter 10: Extensions of valuations

This file is a statement-generation formalization of Sections 10.1--10.7 of
Book 1.  The declarations deliberately keep the valuation-theoretic data
explicit: this makes the extension, residue, and ramification assertions
usable independently of the other generated chapters.
-/

/-! # Book 1, Chapter 10, Section 10.6: Finite Extensions of Complete Fields
-/

/-! ## 10.6. Finite extensions of complete fields -/

/-- Coordinate max norm attached to a finite basis. -/
def Chapter10CoordinateNorm {K L ι : Type*} [NormedField K]
    [AddCommGroup L] [Module K L] [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι K L) : L → ℝ :=
  fun x => Finset.univ.sup' Finset.univ_nonempty (fun i => ‖b.repr x i‖)

/-- Two real-valued norms are equivalent up to positive constants. -/
def Chapter10EquivalentRealNorms {L : Type*} (N M : L → ℝ) : Prop :=
  ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
    (∀ x, N x ≤ c * M x) ∧ (∀ x, M x ≤ d * N x)

/-- Coordinate Cauchy condition, stated without choosing a topology on L. -/
def Chapter10CauchyInNorm {L : Type*} [AddGroup L]
    (N : L → ℝ) (s : ℕ → L) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ m n : ℕ,
    N₀ ≤ m → N₀ ≤ n → N (s m - s n) < ε

/-- Convergence in a specified real-valued norm. -/
def Chapter10TendsToInNorm {L : Type*} [AddGroup L]
    (N : L → ℝ) (s : ℕ → L) (x : L) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ,
    N₀ ≤ n → N (s n - x) < ε

/-- The coordinate max norm is complete when the base field is complete. -/
theorem chapter10_coordinate_norm_complete
    {K L ι : Type*} [NormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι K L) (s : ℕ → L)
    (hs : Chapter10CauchyInNorm (Chapter10CoordinateNorm b) s) :
    ∃ x : L, Chapter10TendsToInNorm (Chapter10CoordinateNorm b) s x := by
  let coeff : ι → ℕ → K := fun i n => b.repr (s n) i
  have hcoeff : ∀ i, CauchySeq (coeff i) := by
    intro i
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hcoord : ‖b.repr (s m - s n) i‖ < ε := by
      have hsup := hN m n hm hn
      exact lt_of_le_of_lt (Module.Basis.norm_repr_le_norm b i) hsup
    rw [map_sub] at hcoord
    change ‖(b.repr (s m)) i - (b.repr (s n)) i‖ < ε at hcoord
    change dist (coeff i m) (coeff i n) < ε
    simpa only [dist_eq_norm, coeff] using hcoord
  choose lim hlim using fun i => cauchySeq_tendsto_of_complete (hcoeff i)
  let x : L := (b.equivFun).symm lim
  refine ⟨x, ?_⟩
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, ∀ i ∈ (Finset.univ : Finset ι),
      ‖b.repr (s n - x) i‖ < ε := by
    rw [Finset.eventually_all]
    intro i hi
    have hi' := (Metric.tendsto_atTop.1 (hlim i)) ε hε
    rcases hi' with ⟨N, hN⟩
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    have hxi : b.repr x i = lim i := by
      change (b.equivFun x) i = lim i
      dsimp [x]
      exact congrFun (b.equivFun.apply_symm_apply lim) i
    rw [map_sub]
    change ‖(b.repr (s n)) i - (b.repr x) i‖ < ε
    rw [hxi]
    simpa only [coeff, dist_eq_norm] using hN n hn
  rcases (Filter.eventually_atTop.1 hevent) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  change Finset.univ.sup' Finset.univ_nonempty (fun i => ‖b.repr (s n - x) i‖) < ε
  rw [Finset.sup'_lt_iff Finset.univ_nonempty]
  intro i hi
  exact hN n hn i hi

/-- Every K-linear endomorphism is bounded for a coordinate norm. -/
theorem chapter10_coordinate_norm_eq_pi_norm
    {K L ι : Type*} [NormedField K] [AddCommGroup L] [Module K L]
    [Fintype ι] [Nonempty ι] (b : Module.Basis ι K L) (x : L) :
    Chapter10CoordinateNorm b x = ‖b.equivFun x‖ := by
  simp only [Chapter10CoordinateNorm, Pi.norm_def, Module.Basis.equivFun_apply]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    have h := Finset.le_sup' (fun j : ι => ‖b.repr x j‖₊) hi
    rw [Finset.sup'_eq_sup Finset.univ_nonempty] at h
    simpa only [coe_nnnorm] using (NNReal.coe_le_coe.mpr h)
  · obtain ⟨i, hi, hi_sup⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : ι => ‖b.repr x i‖₊)
    rw [← Finset.sup'_eq_sup Finset.univ_nonempty, hi_sup]
    simpa only [coe_nnnorm] using
      (Finset.le_sup' (fun j : ι => ‖b.repr x j‖) hi)

theorem chapter10_coordinate_norm_linear_map_bound
    {K L ι : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L]
    [Fintype ι] [Nonempty ι] [FiniteDimensional K L]
    (b : Module.Basis ι K L) (T : L →ₗ[K] L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : L,
      Chapter10CoordinateNorm b (T x) ≤
        C * Chapter10CoordinateNorm b x := by
  let Fₗ : (ι → K) →ₗ[K] (ι → K) :=
    b.equivFun.toLinearMap.comp (T.comp b.equivFun.symm.toLinearMap)
  let F : (ι → K) →L[K] (ι → K) :=
    { toLinearMap := Fₗ
      cont := by exact LinearMap.continuous_of_finiteDimensional Fₗ }
  obtain ⟨C, hC, hF⟩ := F.isBoundedLinearMap.bound
  refine ⟨C, le_of_lt hC, ?_⟩
  have hcoord (y : L) : Chapter10CoordinateNorm b y = ‖b.equivFun y‖ :=
    chapter10_coordinate_norm_eq_pi_norm b y
  have hF_apply (x : L) : F (b.equivFun x) = b.equivFun (T x) := by
    change Fₗ (b.equivFun x) = b.equivFun (T x)
    simp [Fₗ]
  intro x
  have h := hF (b.equivFun x)
  calc
    Chapter10CoordinateNorm b (T x) = ‖b.equivFun (T x)‖ := hcoord _
    _ = ‖F (b.equivFun x)‖ := by rw [hF_apply]
    _ ≤ C * ‖b.equivFun x‖ := h
    _ = C * Chapter10CoordinateNorm b x := by rw [hcoord]

/-- Coordinate norms from two bases are equivalent. -/
theorem chapter10_coordinate_norms_equivalent
    {K L ι κ : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L]
    [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    [FiniteDimensional K L]
    (b : Module.Basis ι K L) (c : Module.Basis κ K L) :
    Chapter10EquivalentRealNorms (Chapter10CoordinateNorm b)
      (Chapter10CoordinateNorm c) := by
  let Fbcₗ : (ι → K) →ₗ[K] (κ → K) :=
    c.equivFun.toLinearMap.comp b.equivFun.symm.toLinearMap
  let Fcbₗ : (κ → K) →ₗ[K] (ι → K) :=
    b.equivFun.toLinearMap.comp c.equivFun.symm.toLinearMap
  let Fbc : (ι → K) →L[K] (κ → K) :=
    { toLinearMap := Fbcₗ
      cont := by exact LinearMap.continuous_of_finiteDimensional Fbcₗ }
  let Fcb : (κ → K) →L[K] (ι → K) :=
    { toLinearMap := Fcbₗ
      cont := by exact LinearMap.continuous_of_finiteDimensional Fcbₗ }
  obtain ⟨Cbc, hCbc, hbc⟩ := Fbc.isBoundedLinearMap.bound
  obtain ⟨Ccb, hCcb, hcb⟩ := Fcb.isBoundedLinearMap.bound
  have hcoordb (x : L) : Chapter10CoordinateNorm b x = ‖b.equivFun x‖ :=
    chapter10_coordinate_norm_eq_pi_norm b x
  have hcoordc (x : L) : Chapter10CoordinateNorm c x = ‖c.equivFun x‖ :=
    chapter10_coordinate_norm_eq_pi_norm c x
  have hbc_apply (x : L) : Fbc (b.equivFun x) = c.equivFun x := by
    change Fbcₗ (b.equivFun x) = c.equivFun x
    simp [Fbcₗ]
  have hcb_apply (x : L) : Fcb (c.equivFun x) = b.equivFun x := by
    change Fcbₗ (c.equivFun x) = b.equivFun x
    simp [Fcbₗ]
  refine ⟨Ccb, Cbc, hCcb, hCbc, ?_, ?_⟩
  · intro x
    calc
      Chapter10CoordinateNorm b x = ‖b.equivFun x‖ := hcoordb _
      _ = ‖Fcb (c.equivFun x)‖ := by rw [hcb_apply]
      _ ≤ Ccb * ‖c.equivFun x‖ := hcb (c.equivFun x)
      _ = Ccb * Chapter10CoordinateNorm c x := by rw [hcoordc]
  · intro x
    calc
      Chapter10CoordinateNorm c x = ‖c.equivFun x‖ := hcoordc _
      _ = ‖Fbc (b.equivFun x)‖ := by rw [hbc_apply]
      _ ≤ Cbc * ‖b.equivFun x‖ := hbc (b.equivFun x)
      _ = Cbc * Chapter10CoordinateNorm b x := by rw [hcoordb]

/-- Multiplication is bounded by a constant times the product of coordinate norms. -/
theorem chapter10_coordinate_norm_multiplication_bound
    {K L ι : Type*} [NormedField K] [IsUltrametricDist K]
    [Field L] [Algebra K L]
    [Fintype ι] [Nonempty ι] [FiniteDimensional K L]
    (b : Module.Basis ι K L) (i : ι) (hBi : b i = (1 : L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : L,
      Chapter10CoordinateNorm b (x * y) ≤
        C * Chapter10CoordinateNorm b x * Chapter10CoordinateNorm b y := by
  obtain ⟨C, hC, hmul⟩ :=
    Module.Basis.norm_mul_le_const_mul_norm (B := b) hBi
      IsUltrametricDist.isNonarchimedean_norm
  refine ⟨C, le_of_lt hC, ?_⟩
  intro x y
  simpa [Chapter10CoordinateNorm, Module.Basis.norm] using hmul x y

/-- Nonarchimedean triangle inequality for a real-valued norm. -/
def Chapter10NonarchimedeanNorm {L : Type*} [Add L] (N : L → ℝ) : Prop :=
  ∀ x y : L, N (x + y) ≤ max (N x) (N y)

/-- Extension of the base-field norm. -/
def Chapter10ExtendsBaseNorm {K L : Type*} [NormedField K]
    [Field L] [Algebra K L] (N : L → ℝ) : Prop :=
  ∀ x : K, N (algebraMap K L x) = ‖x‖

/-- Power multiplicativity, including the norm formula's uniqueness condition. -/
def Chapter10PowerMultiplicative {L : Type*} [Pow L ℕ] (N : L → ℝ) : Prop :=
  ∀ (x : L) (n : ℕ), N (x ^ n) = N x ^ n

/-- The property characterizing the unique nonarchimedean extension norm. -/
def Chapter10UniqueExtensionNormProperty
    {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    (N : AlgebraNorm K L) : Prop :=
  Chapter10NonarchimedeanNorm (N : L → ℝ) ∧
    Chapter10PowerMultiplicative (N : L → ℝ) ∧
    Chapter10ExtendsBaseNorm (K := K) (L := L) (N : L → ℝ)


/-- The actual absolute-value axioms for an algebraic extension. -/
def Chapter10AlgebraicExtensionNormProperty
    {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    (N : L → ℝ) : Prop :=
  N 0 = 0 ∧ N 1 = 1 ∧
    (∀ x, 0 ≤ N x) ∧ (∀ x, N x = 0 ↔ x = 0) ∧
    (∀ x y, N (x * y) = N x * N y) ∧
    (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧
    Chapter10ExtendsBaseNorm (K := K) (L := L) N
/-- Any nonarchimedean norm on a finite extension is equivalent to a coordinate norm. -/
theorem chapter10_nonarchimedean_norm_equivalent_to_coordinate_norm
    {K L ι : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    [FiniteDimensional K L]
    (b : Module.Basis ι K L) (N : AlgebraNorm K L)
    (_hN : Chapter10NonarchimedeanNorm (N : L → ℝ)) :
    Chapter10EquivalentRealNorms (N : L → ℝ) (Chapter10CoordinateNorm b) := by
  let : NormedRing L := N.toRingNorm.toNormedRing
  let : NormedSpace K L :=
    { norm_smul_le := fun k x => le_of_eq (map_smul_eq_mul N k x) }
  let Fₗ : L →ₗ[K] (ι → K) := b.equivFun.toLinearMap
  let Gₗ : (ι → K) →ₗ[K] L := b.equivFun.symm.toLinearMap
  let F : L →L[K] (ι → K) :=
    { toLinearMap := Fₗ
      cont := by exact LinearMap.continuous_of_finiteDimensional Fₗ }
  let G : (ι → K) →L[K] L :=
    { toLinearMap := Gₗ
      cont := by exact LinearMap.continuous_of_finiteDimensional Gₗ }
  obtain ⟨c, hc, hG⟩ := G.isBoundedLinearMap.bound
  obtain ⟨d, hd, hF⟩ := F.isBoundedLinearMap.bound
  have hcoord (y : L) : Chapter10CoordinateNorm b y = ‖b.equivFun y‖ :=
    chapter10_coordinate_norm_eq_pi_norm b y
  have hF_apply (x : L) : F x = b.equivFun x := by
    change Fₗ x = b.equivFun x
    simp [Fₗ]
  have hG_apply (x : L) : G (F x) = x := by
    change Gₗ (Fₗ x) = x
    simp [Fₗ, Gₗ]
  refine ⟨c, d, hc, hd, ?_, ?_⟩
  · intro x
    have h := hG (F x)
    calc
      N x = ‖x‖ := rfl
      _ = ‖G (F x)‖ := by rw [hG_apply]
      _ ≤ c * ‖F x‖ := h
      _ = c * Chapter10CoordinateNorm b x := by rw [hF_apply, hcoord]
  · intro x
    have h := hF x
    calc
      Chapter10CoordinateNorm b x = ‖F x‖ := by rw [hF_apply, hcoord]
      _ ≤ d * ‖x‖ := h
      _ = d * N x := by rfl

/-- The reverse inequality in the finite-dimensional nonarchimedean norm lemma. -/
theorem chapter10_nonarchimedean_norm_reverse_coordinate_bound
    {K L ι : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    [FiniteDimensional K L]
    (b : Module.Basis ι K L) (N : AlgebraNorm K L)
    (hN : Chapter10NonarchimedeanNorm (N : L → ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : L,
      c * Chapter10CoordinateNorm b x ≤ N x := by
  obtain ⟨c, d, hc, hd, _hupper, hlower⟩ :=
    chapter10_nonarchimedean_norm_equivalent_to_coordinate_norm b N hN
  refine ⟨d⁻¹, inv_pos.mpr hd, ?_⟩
  intro x
  calc
    d⁻¹ * Chapter10CoordinateNorm b x ≤ d⁻¹ * (d * N x) :=
      mul_le_mul_of_nonneg_left (hlower x) (le_of_lt (inv_pos.mpr hd))
    _ = N x := by field_simp

/-- The one-dimensional induction step uses a positive distance from a closed subspace. -/
theorem chapter10_closed_subspace_distance_step
    {K L : Type*} [NormedField K] [CompleteSpace K]
    [NormedField L] [Algebra K L] (W : Submodule K L) (e : L)
    (hclosed : IsClosed (W : Set L)) (he : e ∉ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : W, δ ≤ ‖e - w‖ := by
  have hWnonempty : (W : Set L).Nonempty := ⟨0, W.zero_mem⟩
  let δ : ℝ := Metric.infDist e (W : Set L)
  refine ⟨δ, ?_, ?_⟩
  · exact (hclosed.notMem_iff_infDist_pos hWnonempty).mp he
  · intro w
    simpa [δ, dist_eq_norm] using Metric.infDist_le_dist_of_mem w.property

/-- Every finite algebraic extension of a complete normed field is complete. -/
theorem chapter10_finite_extension_is_complete
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
    CompleteSpace L := by
  exact FiniteDimensional.complete K L

/--
Uniqueness over an arbitrary algebraic extension.  The values are compared
as real absolute values, so this statement does not silently fix a value
group for the algebraic extension.
-/
theorem chapter10_unique_complete_extension_norm
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] :
    ∃ N : L → ℝ,
      Chapter10AlgebraicExtensionNormProperty (K := K) (L := L) N ∧
        ∀ N' : L → ℝ,
          Chapter10AlgebraicExtensionNormProperty (K := K) (L := L) N' →
            ∀ x, N' x = N x := by
  let S : AlgebraNorm K L := spectralAlgNorm K L
  have hS : Chapter10AlgebraicExtensionNormProperty (K := K) (L := L) S := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [S, spectralAlgNorm_def] using (spectralNorm_zero (K := K) (L := L))
    · simpa [S] using (spectralAlgNorm_one (K := K) (L := L))
    · intro x
      simpa [S, spectralAlgNorm_def] using (spectralNorm_nonneg (K := K) (L := L) x)
    · intro x
      exact map_eq_zero_iff_eq_zero S
    · intro x y
      simpa [S] using (spectralAlgNorm_mul (K := K) (L := L) x y)
    · intro x y
      simpa [S, spectralAlgNorm_def] using
        (isNonarchimedean_spectralNorm (K := K) (L := L) x y)
    · intro k
      simpa [S] using (spectralAlgNorm_extends (K := K) (L := L) k)
  refine ⟨S, hS, ?_⟩
  intro N' hN' x
  rcases hN' with ⟨h0, h1, hpos, hzero, hmul, hadd, hext⟩
  let f : AbsoluteValue L ℝ :=
    { toFun := N'
      map_mul' := hmul
      nonneg' := hpos
      eq_zero' := hzero
      add_le' := by
        intro a b
        refine (hadd a b).trans ?_
        rw [max_le_iff]
        exact ⟨le_add_of_nonneg_right (hpos b), le_add_of_nonneg_left (hpos a)⟩ }
  have hf := spectralNorm_unique_field_norm_ext (K := K) (L := L) (f := f) hext x
  simpa [f, S, spectralAlgNorm_def] using hf

/-- K-automorphisms preserve the unique extension norm. -/
theorem chapter10_automorphism_preserves_unique_norm
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (N : AlgebraNorm K L)
    (hN : Chapter10UniqueExtensionNormProperty N)
    (σ : L ≃ₐ[K] L) :
    ∀ x : L, N (σ x) = N x := by
  have hp : IsPowMul N := fun x n _hn => hN.2.1 x n
  have hspec : N = spectralAlgNorm K L := spectralNorm_unique hp
  intro x
  rw [hspec]
  simpa [spectralAlgNorm_def] using
    (spectralNorm_eq_of_equiv (K := K) (L := L) σ x).symm

/-- Norm/product formula for a finite extension. -/
def Chapter10NormProductFormula
    {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    (N : L → ℝ) : Prop :=
  ∀ x : L,
    N x = Real.rpow ‖Algebra.norm K x‖
      ((Module.finrank K L : ℝ)⁻¹)

theorem chapter10_complete_extension_norm_product_formula
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (N : AlgebraNorm K L)
    (hN : Chapter10UniqueExtensionNormProperty N) :
    Chapter10NormProductFormula (K := K) (L := L) (N : L → ℝ) := by sorry

/-! The trivial absolute-value branch is separate because the spectral-norm
construction used above is stated for nontrivial normed fields. -/
/-- The trivial absolute value extends uniquely across an algebraic extension. -/
theorem chapter10_trivial_extension_norm_unique
    {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (htrivial : ∀ x : K, x ≠ 0 → ‖x‖ = 1) :
    ∃! N : L → ℝ,
      Chapter10AlgebraicExtensionNormProperty (K := K) (L := L) N := by sorry

/-- Factorization-form henselianity gives the unique valuation extension. -/
theorem chapter10_henselian_unique_extension
    {K L Γ₀ Γ₁ Γ₂ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂] [Algebra.IsAlgebraic K L]
    (v : Valuation K Γ₀) (hH : Chapter10IsHenselianValuedField v)
    (w₁ : Valuation L Γ₁) (w₂ : Valuation L Γ₂)
    (h₁ : v.IsEquiv (w₁.comap (algebraMap K L)))
    (h₂ : v.IsEquiv (w₂.comap (algebraMap K L))) :
    w₁.IsEquiv w₂ := by
  exact chapter10_henselian_valuation_has_unique_branch v hH w₁ w₂ h₁ h₂

/-- Every algebraic element lies in a finite intermediate extension. -/
theorem chapter10_algebraic_element_in_finite_subextension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x : L} (hx : IsAlgebraic K x) :
    ∃ E : IntermediateField K L, x ∈ E ∧ FiniteDimensional K E := by
  let E : IntermediateField K L := IntermediateField.adjoin K ({x} : Set L)
  refine ⟨E, ?_, ?_⟩
  · exact IntermediateField.subset_adjoin K ({x} : Set L) (Set.mem_singleton x)
  · exact IntermediateField.adjoin.finiteDimensional hx.isIntegral

/-- Compatible finite-extension norms glue over an infinite algebraic extension. -/
theorem chapter10_compatible_finite_values_glue
    {K L : Type*} [NormedField K] [CompleteSpace K]
    [Field L] [Algebra K L]
    (Nfin : ∀ E : IntermediateField K L, E → ℝ)
    (hfinite : ∀ x : L, ∃ E : IntermediateField K L,
      x ∈ E ∧ FiniteDimensional K E)
    (hcompat : ∀ (E F : IntermediateField K L) (hEF : E ≤ F) (x : E),
      Nfin E x = Nfin F ⟨x.1, hEF x.2⟩) :
    ∃ N : L → ℝ, ∀ (E : IntermediateField K L) (x : E),
      N (x : L) = Nfin E x := by
  let Eof : L → IntermediateField K L := fun x => Classical.choose (hfinite x)
  have hmem : ∀ x : L, x ∈ Eof x := fun x => (Classical.choose_spec (hfinite x)).1
  let N : L → ℝ := fun x => Nfin (Eof x) ⟨x, hmem x⟩
  refine ⟨N, ?_⟩
  intro E x
  let F := Eof (x : L)
  let G := E ⊔ F
  have hEG := hcompat E G le_sup_left x
  have hFG := hcompat F G le_sup_right ⟨x, hmem (x : L)⟩
  dsimp [N, F, G]
  rw [hFG]
  simpa using hEG.symm

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
