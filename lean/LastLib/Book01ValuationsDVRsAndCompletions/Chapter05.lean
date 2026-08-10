import Mathlib.Algebra.Module.DedekindDomain
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter05

open IsLocalRing
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators DirectSum nonZeroDivisors WithZero

noncomputable section

/-!
# Chapter 5: The valuation filtration

This file is a statement-generation pass for Chapter 5 of *Valuations, DVRs, and
Completions*.  The declarations are deliberately self-contained: the DVR and
local-ring notions used below are Mathlib notions, while the few constructions
which are not exposed by Mathlib are recorded as chapter-local interfaces.
-/

section SuccessivePrecision

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (π : A) (hπ : Irreducible π)

/-- Book §5.1: reduction at precision `n` is reduction modulo `𝔪^n`. -/
def chapterReduction (n : ℕ) (x : A) :
    A ⧸ (IsLocalRing.maximalIdeal A ^ n : Ideal A) :=
  Ideal.Quotient.mk _ x

/-- Book §5.1: reduction modulo `𝔪` is the leading residue digit. -/
def chapterLeadingDigit (x : A) : IsLocalRing.ResidueField A :=
  IsLocalRing.residue A x

/-- Book §5.1, displayed precision assertion. -/
theorem chapter_reduction_mod_maximalIdeal_is_leading_digit (x : A) :
    chapterLeadingDigit A x = IsLocalRing.residue A x := by
  rfl

/-- Book §5.1: the `n`th precision quotient is `A / 𝔪^n`. -/
theorem chapter_precision_is_power_quotient (n : ℕ) (x : A) :
    chapterReduction A n x = Ideal.Quotient.mk _ x := by
  rfl

include hπ in
/-- Book §5.1: in a DVR, `𝔪^n = (π^n)`. -/
theorem chapter_maximalIdeal_pow_eq_uniformizer_span (n : ℕ) :
    IsLocalRing.maximalIdeal A ^ n = Ideal.span {π ^ n} := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]

/-- Book §5.1: the powers of the maximal ideal form a strictly descending chain. -/
theorem chapter_maximalIdeal_pow_strictly_descends (n : ℕ) :
    IsLocalRing.maximalIdeal A ^ (n + 1) < IsLocalRing.maximalIdeal A ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  apply Ideal.pow_succ_lt_pow
  rw [hϖ.maximalIdeal_eq]
  intro h
  exact hϖ.ne_zero (Ideal.span_singleton_eq_bot.mp h)

/-- Book §5.1: the separated filtration has zero intersection. -/
theorem chapter_maximalIdeal_pow_iInf_eq_bot :
    ⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n = (⊥ : Ideal A) := by
  exact Ideal.iInf_pow_eq_bot_of_isLocalRing _
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top

/-- The `n`th graded layer `𝔪^n / 𝔪^(n+1)`, viewed as an `A`-module. -/
def chapterGradedPieceDenominator (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (n : ℕ) :
    Submodule A (↥(IsLocalRing.maximalIdeal A ^ n : Ideal A)) :=
  Submodule.comap (IsLocalRing.maximalIdeal A ^ n : Submodule A A).subtype
    (IsLocalRing.maximalIdeal A ^ (n + 1) : Submodule A A)
abbrev chapterGradedPiece (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (n : ℕ) : Type _ :=
  (↥(IsLocalRing.maximalIdeal A ^ n : Ideal A)) ⧸
    chapterGradedPieceDenominator A n

/-- A representative in the `n`th layer for the class of `a * π^n`. -/
def chapterLayerRepresentative (n : ℕ) (a : A) :
    chapterGradedPiece A n := by
  refine Submodule.Quotient.mk ⟨a * π ^ n, ?_⟩
  rw [chapter_maximalIdeal_pow_eq_uniformizer_span A π hπ n]
  exact Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self (π ^ n))

/-- Book §5.1: multiplication by `π^n` induces the map between successive layers. -/
def chapterLayerMultiplicationMap
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) (n : ℕ) :
    (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) →ₗ[A] chapterGradedPiece A n := by
  let g : A →ₗ[A] ↥(IsLocalRing.maximalIdeal A ^ n : Ideal A) :=
    LinearMap.codRestrict (IsLocalRing.maximalIdeal A ^ n : Submodule A A)
      (LinearMap.mulLeft A (π ^ n)) (by
        intro a
        rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
        simpa [LinearMap.mulLeft_apply, mul_comm] using
          (Ideal.mul_mem_left (Ideal.span {π ^ n}) a
            (Ideal.mem_span_singleton_self (π ^ n))))
  let f : A →ₗ[A] chapterGradedPiece A n :=
    (chapterGradedPieceDenominator A n).mkQ.comp g
  have hf : (IsLocalRing.maximalIdeal A : Submodule A A) ≤ f.ker := by
    intro a ha
    apply (Submodule.Quotient.mk_eq_zero (chapterGradedPieceDenominator A n)).2
    change (π ^ n) * a ∈ (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)
    rw [pow_succ (IsLocalRing.maximalIdeal A) n]
    apply Ideal.mul_mem_mul
    · rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    · exact ha
  exact Submodule.liftQ (IsLocalRing.maximalIdeal A : Submodule A A) f
    (by simpa [f] using hf)

/-- Book §5.1, displayed map `ā ↦ overline{a π^n}`. -/
theorem chapterLayerMultiplicationMap_apply (n : ℕ) (a : A) :
    chapterLayerMultiplicationMap (A := A) π hπ n (Ideal.Quotient.mk _ a) =
      chapterLayerRepresentative (A := A) π hπ n a := by
  unfold chapterLayerMultiplicationMap
  rw [← Ideal.Quotient.mk_eq_mk]
  rw [Submodule.liftQ_apply]
  apply (Submodule.Quotient.eq (chapterGradedPieceDenominator A n)).2
  apply Submodule.mem_comap.mpr
  simp [LinearMap.codRestrict_apply, LinearMap.mulLeft_apply, mul_comm]

include hπ in
/-- Book §5.1: cancellation proves injectivity on the layer map. -/
theorem chapter_uniformizer_layer_cancellation (n : ℕ) {a : A}
    (ha : a * π ^ n ∈ Ideal.span {π ^ (n + 1)}) :
    a ∈ Ideal.span {π} := by
  rw [Ideal.mem_span_singleton] at ha ⊢
  obtain ⟨c, hc⟩ := ha
  refine ⟨c, ?_⟩
  apply (mul_right_cancel₀ (pow_ne_zero n hπ.ne_zero))
  simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hc

/-- Book §5.1: multiplication by `π^n` is an isomorphism of the residue layer. -/
theorem chapterLayerMultiplicationMap_bijective (n : ℕ) :
    Function.Bijective (chapterLayerMultiplicationMap (A := A) π hπ n) := by
  classical
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [chapterLayerMultiplicationMap_apply (A := A) π hπ n a,
      chapterLayerMultiplicationMap_apply (A := A) π hπ n b] at hxy
    apply (Ideal.Quotient.eq).2
    rw [hπ.maximalIdeal_eq]
    apply chapter_uniformizer_layer_cancellation (A := A) π hπ n
    rw [← chapter_maximalIdeal_pow_eq_uniformizer_span A π hπ (n + 1)]
    have hxy' := (Submodule.Quotient.eq (chapterGradedPieceDenominator A n)).mp hxy
    change (a * π ^ n - b * π ^ n) ∈
      (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A) at hxy'
    simpa [sub_mul] using hxy'
  · intro z
    obtain ⟨z, rfl⟩ :=
      Submodule.Quotient.mk_surjective (chapterGradedPieceDenominator A n) z
    have hz : (z : A) ∈ Ideal.span {π ^ n} := by
      rw [← chapter_maximalIdeal_pow_eq_uniformizer_span A π hπ n]
      exact z.property
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hz
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [chapterLayerMultiplicationMap_apply (A := A) π hπ n a]
    apply (Submodule.Quotient.eq (chapterGradedPieceDenominator A n)).2
    change a * π ^ n - (z : A) ∈
      (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)
    rw [ha]
    simp [mul_comm]

theorem chapter_graded_piece_is_torsion_by_maximalIdeal (n : ℕ) :
    Module.IsTorsionBySet A (chapterGradedPiece A n)
      (IsLocalRing.maximalIdeal A : Set A) := by
  intro x a
  induction x using Submodule.Quotient.induction_on
    (chapterGradedPieceDenominator A n) with
  | _ z =>
    apply (Submodule.Quotient.mk_eq_zero (chapterGradedPieceDenominator A n)).2
    change (a : A) • (z : A) ∈
      (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)
    rw [smul_eq_mul, pow_succ' (IsLocalRing.maximalIdeal A) n]
    exact Ideal.mul_mem_mul a.2 z.2

/-- The layer isomorphism supplied by multiplication by `π^n`. -/
noncomputable def chapterLayerMultiplicationEquiv (n : ℕ) :
    (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) ≃ₗ[A] chapterGradedPiece A n :=
  LinearEquiv.ofBijective (chapterLayerMultiplicationMap (A := A) π hπ n)
    (chapterLayerMultiplicationMap_bijective (A := A) π hπ n)

/-- Book §5.1: each successive layer is one-dimensional over the residue field. -/
noncomputable instance chapterGradedPiece.residueFieldModule (n : ℕ) :
    Module (IsLocalRing.ResidueField A) (chapterGradedPiece A n) := by
  exact Module.IsTorsionBySet.module
    (chapter_graded_piece_is_torsion_by_maximalIdeal (A := A) n)

noncomputable def chapterLayerResidueLinearMap (n : ℕ) :
    IsLocalRing.ResidueField A →ₗ[IsLocalRing.ResidueField A]
      chapterGradedPiece A n :=
  { toFun := chapterLayerMultiplicationMap (A := A) π hπ n
    map_add' := (chapterLayerMultiplicationMap (A := A) π hπ n).map_add
    map_smul' := by
      intro c x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      let hM := chapter_graded_piece_is_torsion_by_maximalIdeal (A := A) n
      let L := chapterLayerMultiplicationMap (A := A) π hπ n
      change L ((Ideal.Quotient.mk _ a) • (Ideal.Quotient.mk _ b)) =
        IsLocalRing.residue A a • L (Ideal.Quotient.mk _ b)
      have hsmul : IsLocalRing.residue A a •
          L (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) b) =
          a • L (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) b) := by
        exact Module.IsTorsionBySet.mk_smul hM a _
      rw [hsmul, ← L.map_smul]
      rfl }

/-- Book §5.1, one-dimensional layer assertion. -/
theorem chapter_graded_piece_finrank_one (n : ℕ) :
    Module.finrank (IsLocalRing.ResidueField A) (chapterGradedPiece A n) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let f := chapterLayerResidueLinearMap (A := A) π hπ n
  have hf : Function.Bijective f := by
    change Function.Bijective
      (chapterLayerMultiplicationMap (A := A) π hπ n)
    exact chapterLayerMultiplicationMap_bijective (A := A) π hπ n
  let e := LinearEquiv.ofBijective f hf
  calc
    Module.finrank (IsLocalRing.ResidueField A) (chapterGradedPiece A n) =
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField A) := e.finrank_eq.symm
    _ = 1 := CommSemiring.finrank_self _

/-- Book §5.1: every layer is linearly equivalent to the residue field. -/
theorem chapter_graded_piece_equiv_residue_field (n : ℕ) :
    Nonempty (chapterGradedPiece A n ≃ₗ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField A) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let f := chapterLayerResidueLinearMap (A := A) π hπ n
  have hf : Function.Bijective f := by
    change Function.Bijective
      (chapterLayerMultiplicationMap (A := A) π hπ n)
    exact chapterLayerMultiplicationMap_bijective (A := A) π hπ n
  exact ⟨(LinearEquiv.ofBijective f hf).symm⟩

/-- Book §5.1: the quotient map from precision `n+1` to precision `n`. -/
def chapterFiltrationProjection
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (n : ℕ) :
    (A ⧸ (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)) →ₗ[A]
      (A ⧸ (IsLocalRing.maximalIdeal A ^ n : Ideal A)) := by
  let f := (Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal A ^ n)).toLinearMap
  have hf : (IsLocalRing.maximalIdeal A ^ (n + 1) : Submodule A A) ≤ f.ker := by
    intro a ha
    change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)) a = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).2
      (Ideal.pow_le_pow_right (Nat.le_succ n) ha)
  exact Submodule.liftQ (IsLocalRing.maximalIdeal A ^ (n + 1) : Submodule A A) f hf

/-- Book §5.1: the successive layer injects into the precision-`n+1` quotient. -/
def chapterFiltrationInjection
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (n : ℕ) :
    chapterGradedPiece A n →ₗ[A]
      (A ⧸ (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)) := by
  let f : (↥(IsLocalRing.maximalIdeal A ^ n : Ideal A)) →ₗ[A]
      (A ⧸ (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)) :=
    (Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal A ^ (n + 1))).toLinearMap.comp
      (IsLocalRing.maximalIdeal A ^ n : Submodule A A).subtype
  have hf : chapterGradedPieceDenominator A n ≤ f.ker := by
    intro z hz
    change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))) (z : A) = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).2 hz
  exact Submodule.liftQ (chapterGradedPieceDenominator A n) f hf

/-- Book §5.1: the filtration step is a short exact sequence. -/
theorem chapter_filtration_short_exact (n : ℕ) :
    Function.Injective (chapterFiltrationInjection (A := A) n) ∧
      Function.Exact (chapterFiltrationInjection (A := A) n)
        (chapterFiltrationProjection (A := A) n) ∧
      Function.Surjective (chapterFiltrationProjection (A := A) n) := by
  classical
  let ι := chapterFiltrationInjection (A := A) n
  let p := chapterFiltrationProjection (A := A) n
  have hp : Function.Surjective p := by
    rintro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    unfold p chapterFiltrationProjection
    rw [← Ideal.Quotient.mk_eq_mk, Submodule.liftQ_apply]
    rfl
  have hi : Function.Injective ι := by
    intro x y hxy
    obtain ⟨x, rfl⟩ :=
      Submodule.Quotient.mk_surjective (chapterGradedPieceDenominator A n) x
    obtain ⟨y, rfl⟩ :=
      Submodule.Quotient.mk_surjective (chapterGradedPieceDenominator A n) y
    apply (Submodule.Quotient.eq (chapterGradedPieceDenominator A n)).2
    change (x : A) - (y : A) ∈ (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    have hxy' :
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))) (x : A) =
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))) (y : A) := by
      simpa [ι, chapterFiltrationInjection, Submodule.liftQ_apply,
        Ideal.Quotient.mkₐ_eq_mk] using hxy
    rw [map_sub]
    exact sub_eq_zero.mpr hxy'
  have he : Function.Exact ι p := by
    intro y
    constructor
    · intro hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hy' : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)) a = 0 := by
        change (chapterFiltrationProjection (A := A) n)
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)) a) = 0 at hy
        unfold chapterFiltrationProjection at hy
        rw [← Ideal.Quotient.mk_eq_mk, Submodule.liftQ_apply] at hy
        exact hy
      have ha : a ∈ (IsLocalRing.maximalIdeal A ^ n : Ideal A) :=
        (Ideal.Quotient.eq_zero_iff_mem).mp hy'
      let z : ↥(IsLocalRing.maximalIdeal A ^ n : Ideal A) := ⟨a, ha⟩
      refine ⟨Submodule.Quotient.mk z, ?_⟩
      unfold ι chapterFiltrationInjection
      rw [Submodule.liftQ_apply]
      rfl
    · rintro ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ :=
        Submodule.Quotient.mk_surjective (chapterGradedPieceDenominator A n) x
      have hι : ι (Submodule.Quotient.mk x) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)) (x : A) := by
        unfold ι chapterFiltrationInjection
        rw [Submodule.liftQ_apply]
        rfl
      rw [hι]
      unfold p chapterFiltrationProjection
      rw [← Ideal.Quotient.mk_eq_mk, Submodule.liftQ_apply]
      exact (Ideal.Quotient.eq_zero_iff_mem).2 x.property
  exact ⟨hi, he, hp⟩

/-- Book §5.1: the short exact filtration sequence is length-additive. -/
theorem chapter_length_filtration_step (n : ℕ) :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)) =
      Module.length A (chapterGradedPiece A n) +
        Module.length A (A ⧸ (IsLocalRing.maximalIdeal A ^ n : Ideal A)) := by
  obtain ⟨hi, he, hp⟩ := chapter_filtration_short_exact (A := A) n
  exact Module.length_eq_add_of_exact
    (chapterFiltrationInjection (A := A) n)
    (chapterFiltrationProjection (A := A) n) hi hp he

include hπ in
/-- Book §5.1, first displayed length formula. -/
theorem chapter_length_uniformizer_quotient (n : ℕ) :
    Module.length A (A ⧸ (Ideal.span {π ^ n} : Ideal A)) = (n : ℕ∞) := by
  rw [← chapter_maximalIdeal_pow_eq_uniformizer_span A π hπ n]
  simpa using (IsDiscreteValuationRing.length_quotient_pow_maximalIdeal A n)

/-- Book §5.1, second displayed length formula. -/
theorem chapter_length_principal_quotient {x : A} (hx : x ≠ 0) :
    Module.length A (A ⧸ (Ideal.span {x} : Ideal A)) =
      IsDiscreteValuationRing.addVal A x := by
  simpa [Ring.ord] using (Ring.ord_eq_addVal x)

include hπ in
/-- Book §5.1: a finitely generated torsion module decomposes into uniformizer blocks,
and its length is the sum of the exponents. -/
theorem chapter_finite_torsion_module_decomposition_and_length
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : Module.IsTorsion A M) :
    ∃ (d : ℕ) (n : Fin d → ℕ),
      Nonempty (M ≃ₗ[A] ⨁ i : Fin d,
        A ⧸ (Ideal.span {π ^ n i} : Ideal A)) ∧
      Module.length A M = ∑ i : Fin d, (n i : ℕ∞) := by
  classical
  have hM' : Module.IsTorsion' M (Submonoid.powers π) := by
    intro x
    obtain ⟨a, ha⟩ := @hM x
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero a.2) hπ
    refine ⟨⟨π ^ n, ⟨n, rfl⟩⟩, ?_⟩
    change (π ^ n) • x = 0
    have ha' : ((u : A) * π ^ n) • x = 0 := by
      rw [← hu]
      exact ha
    have hcancel := congrArg (fun z : M => (↑(u⁻¹) : A) • z) ha'
    simpa [smul_smul] using hcancel
  obtain ⟨d, n, ⟨e⟩⟩ :=
    Module.torsion_by_prime_power_decomposition (R := A) (M := M)
      (p := π) hπ hM'
  refine ⟨d, n, ?_, ?_⟩
  · exact ⟨by simpa [Ideal.submodule_span_eq] using e⟩
  · calc
      Module.length A M =
          Module.length A (⨁ i : Fin d, A ⧸ (Ideal.span {π ^ n i} : Ideal A)) :=
        e.length_eq
      _ = ∑ i : Fin d, Module.length A
          (A ⧸ (Ideal.span {π ^ n i} : Ideal A)) := by
        rw [(DirectSum.linearEquivFunOnFintype A (Fin d)
          (fun i => A ⧸ (Ideal.span {π ^ n i} : Ideal A))).length_eq,
          Module.length_pi_of_fintype]
      _ = ∑ i : Fin d, (n i : ℕ∞) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact chapter_length_uniformizer_quotient A π hπ (n i)

end SuccessivePrecision

section LeadingTermsAndDigits

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (π : A) (hπ : Irreducible π)

/--
The external associated-graded object is the direct sum of the successive
quotients.  Mathlib does not provide the associated-graded ring construction
for this filtration, so the polynomial ring below is retained as the concrete
ring model used by the initial-form declarations.
-/
abbrev chapterAssociatedGradedObject : Type _ :=
  ⨁ n : ℕ, chapterGradedPiece A n

/- The concrete polynomial model for the associated graded ring. -/
abbrev chapterAssociatedGradedRing : Type _ :=
  Polynomial (IsLocalRing.ResidueField A)

/-- The polynomial realization carries its usual commutative-ring structure. -/
noncomputable instance chapterAssociatedGradedRing.commRing :
    CommRing (chapterAssociatedGradedRing (A := A)) := by
  dsimp [chapterAssociatedGradedRing]
  infer_instance

noncomputable instance chapterAssociatedGradedRing.module :
    Module A (chapterAssociatedGradedRing (A := A)) := by
  let f : A →+* chapterAssociatedGradedRing (A := A) :=
    (Polynomial.C : IsLocalRing.ResidueField A →+*
      Polynomial (IsLocalRing.ResidueField A)).comp (IsLocalRing.residue A)
  exact Module.compHom (chapterAssociatedGradedRing (A := A)) f

/-- The chosen inclusion of a graded piece into the polynomial realization. -/
def chapterGradedInclusion (n : ℕ) :
    chapterGradedPiece A n →ₗ[A] chapterAssociatedGradedRing (A := A) := by
  classical
  let f : A →ₗ[A] chapterAssociatedGradedRing (A := A) :=
    { toFun := fun a => Polynomial.C (IsLocalRing.residue A a) * Polynomial.X ^ n
      map_add' := by
        intro a b
        simp only [map_add, add_mul]
      map_smul' := by
        intro a b
        simp only [smul_eq_mul, map_mul, RingHom.toModule_smul,
          RingHom.comp_apply, RingHom.id_apply]
        ring }
  have hf : (IsLocalRing.maximalIdeal A : Submodule A A) ≤ f.ker := by
    intro a ha
    change Polynomial.C (IsLocalRing.residue A a) * Polynomial.X ^ n = 0
    have hz : IsLocalRing.residue A a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).2 ha
    rw [hz]
    simp
  exact (Submodule.liftQ (IsLocalRing.maximalIdeal A : Submodule A A) f hf).comp
    (chapterLayerMultiplicationEquiv (A := A) π hπ n).symm.toLinearMap

/-- The class of `π` in `𝔪/𝔪^2`. -/
def chapterUniformizerLayerClass (π : A) (hπ : Irreducible π) :
    chapterGradedPiece A 1 := by
  exact chapterLayerRepresentative (A := A) π hπ 1 1

/-- The initial form of the uniformizer in the polynomial realization. -/
def chapterInitialFormUniformizer (π : A) (hπ : Irreducible π) :
    chapterAssociatedGradedRing (A := A) := by
  exact Polynomial.X

/-- The finite valuation degree of an element, with `0` assigned to the zero element. -/
def chapterInitialDegree (x : A) : ℕ :=
  (IsDiscreteValuationRing.addVal A x).toNat

/-- The polynomial-model initial form of an element in its first nonzero graded piece. -/
noncomputable def chapterInitialForm (π : A) (hπ : Irreducible π) (x : A) :
    chapterAssociatedGradedRing (A := A) := by
  classical
  exact if hx : x = 0 then 0 else
    let hfac := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
    let n := Classical.choose hfac
    let u := Classical.choose (Classical.choose_spec hfac)
    Polynomial.C (IsLocalRing.residue A (u : A)) * Polynomial.X ^ n

theorem chapterInitialForm_eq_factorization {x : A} (hx : x ≠ 0)
    {n : ℕ} (u : Aˣ) (hu : x = (u : A) * π ^ n) :
    chapterInitialForm (A := A) π hπ x =
      Polynomial.C (IsLocalRing.residue A (u : A)) * Polynomial.X ^ n := by
  classical
  let hfac := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  let n₀ := Classical.choose hfac
  let u₀ := Classical.choose (Classical.choose_spec hfac)
  have hu₀ : x = (u₀ : A) * π ^ n₀ :=
    Classical.choose_spec (Classical.choose_spec hfac)
  have hn : n₀ = n := by
    apply ENat.natCast_inj.mp
    calc
      (n₀ : ℕ∞) = IsDiscreteValuationRing.addVal A x := by
        rw [hu₀, IsDiscreteValuationRing.addVal_def' u₀ hπ n₀]
      _ = (n : ℕ∞) := by
        rw [hu, IsDiscreteValuationRing.addVal_def' u hπ n]
  have huu : (u₀ : A) = (u : A) := by
    apply mul_right_cancel₀ (pow_ne_zero n hπ.ne_zero)
    calc
      (u₀ : A) * π ^ n = (u₀ : A) * π ^ n₀ := by rw [hn]
      _ = x := hu₀.symm
      _ = (u : A) * π ^ n := hu
  unfold chapterInitialForm
  rw [dif_neg hx]
  change Polynomial.C (IsLocalRing.residue A (u₀ : A)) * Polynomial.X ^ n₀ =
    Polynomial.C (IsLocalRing.residue A (u : A)) * Polynomial.X ^ n
  rw [hn, huu]

/-- Book §5.2, displayed associated-graded identification `gr_𝔪(A) ≅ k[T]`.

The direct sum is the external associated-graded object; the componentwise
condition records the chosen polynomial realization and sends the class of
the uniformizer to `T`.
-/
theorem chapter_associated_graded_equiv_polynomial :
    ∃ e : chapterAssociatedGradedObject (A := A) ≃ₗ[IsLocalRing.ResidueField A]
        chapterAssociatedGradedRing (A := A),
      (∀ (n : ℕ) (x : chapterGradedPiece A n),
        e (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) n x) =
          chapterGradedInclusion (A := A) π hπ n x) ∧
      e (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) 1
          (chapterUniformizerLayerClass (A := A) π hπ)) =
        chapterInitialFormUniformizer (A := A) π hπ := by
  classical
  let E : (n : ℕ) → chapterGradedPiece A n ≃ₗ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField A := fun n =>
    (LinearEquiv.ofBijective
      (chapterLayerResidueLinearMap (A := A) π hπ n) (by
        change Function.Bijective
          (chapterLayerMultiplicationMap (A := A) π hπ n)
        exact chapterLayerMultiplicationMap_bijective (A := A) π hπ n)).symm
  let e₀ := DirectSum.congrLinearEquiv E
  let ePoly :
      (⨁ n : ℕ, IsLocalRing.ResidueField A) ≃ₗ[IsLocalRing.ResidueField A]
        chapterAssociatedGradedRing (A := A) :=
    (finsuppLEquivDirectSum (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A) ℕ).symm.trans
      ((PolynomialModule.coeffLinearEquiv (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField A)).symm.trans
        (PolynomialModule.equivPolynomial (R := IsLocalRing.ResidueField A)
          (S := IsLocalRing.ResidueField A)))
  let e := e₀.trans ePoly
  have hE (n : ℕ) (a : A) :
      E n (chapterLayerRepresentative (A := A) π hπ n a) =
        IsLocalRing.residue A a := by
    have hf : Function.Bijective
        (chapterLayerResidueLinearMap (A := A) π hπ n) := by
      change Function.Bijective
        (chapterLayerMultiplicationMap (A := A) π hπ n)
      exact chapterLayerMultiplicationMap_bijective (A := A) π hπ n
    dsimp [E]
    apply (LinearEquiv.ofBijective
      (chapterLayerResidueLinearMap (A := A) π hπ n) hf).injective
    rw [(LinearEquiv.ofBijective
      (chapterLayerResidueLinearMap (A := A) π hπ n) hf).apply_symm_apply]
    symm
    change chapterLayerMultiplicationMap (A := A) π hπ n
        (Ideal.Quotient.mk _ a) =
      chapterLayerRepresentative (A := A) π hπ n a
    exact chapterLayerMultiplicationMap_apply (A := A) π hπ n a
  have hA (n : ℕ) (a : A) :
      (chapterLayerMultiplicationEquiv (A := A) π hπ n).symm
          (chapterLayerRepresentative (A := A) π hπ n a) =
        Ideal.Quotient.mk _ a := by
    apply (chapterLayerMultiplicationEquiv (A := A) π hπ n).injective
    rw [(chapterLayerMultiplicationEquiv (A := A) π hπ n).apply_symm_apply]
    symm
    change chapterLayerMultiplicationMap (A := A) π hπ n
        (Ideal.Quotient.mk _ a) =
      chapterLayerRepresentative (A := A) π hπ n a
    exact chapterLayerMultiplicationMap_apply (A := A) π hπ n a
  have hIncl (n : ℕ) (a : A) :
      chapterGradedInclusion (A := A) π hπ n
          (chapterLayerRepresentative (A := A) π hπ n a) =
        Polynomial.C (IsLocalRing.residue A a) * Polynomial.X ^ n := by
    have hA' :
        (↑((chapterLayerMultiplicationEquiv (A := A) π hπ n).symm
          (chapterLayerRepresentative (A := A) π hπ n a)) :
          A ⧸ (IsLocalRing.maximalIdeal A : Submodule A A)) =
        Submodule.Quotient.mk a := by
      exact congrArg (fun z : A ⧸ (IsLocalRing.maximalIdeal A : Ideal A) =>
        (z : A ⧸ (IsLocalRing.maximalIdeal A : Submodule A A))) (hA n a)
    simp only [chapterGradedInclusion, LinearMap.comp_apply]
    change (Submodule.liftQ _ _ _)
      (↑((chapterLayerMultiplicationEquiv (A := A) π hπ n).symm
        (chapterLayerRepresentative (A := A) π hπ n a)) :
        A ⧸ (IsLocalRing.maximalIdeal A : Submodule A A)) = _
    rw [hA']
    rfl
  have hrep (n : ℕ) (x : chapterGradedPiece A n) :
      ∃ a : A, x = chapterLayerRepresentative (A := A) π hπ n a := by
    obtain ⟨z, rfl⟩ :=
      Submodule.Quotient.mk_surjective (chapterGradedPieceDenominator A n) x
    have hz : (z : A) ∈ Ideal.span {π ^ n} := by
      rw [← chapter_maximalIdeal_pow_eq_uniformizer_span A π hπ n]
      exact z.property
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hz
    refine ⟨a, ?_⟩
    apply (Submodule.Quotient.eq (chapterGradedPieceDenominator A n)).2
    change (z : A) - a * π ^ n ∈
      (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)
    rw [ha]
    have hz : π ^ n * a - a * π ^ n = 0 := by ring
    rw [hz]
    exact Ideal.zero_mem _
  have he₀ (n : ℕ) (x : chapterGradedPiece A n) :
      e₀ (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) n x) =
        DirectSum.of (fun _ : ℕ => IsLocalRing.ResidueField A) n (E n x) := by
    simp [e₀, DirectSum.congrLinearEquiv, DirectSum.congrAddEquiv]
  have hePoly (n : ℕ) (c : IsLocalRing.ResidueField A) :
      ePoly (DirectSum.of (fun _ : ℕ => IsLocalRing.ResidueField A) n c) =
        Polynomial.monomial n c := by
    change PolynomialModule.equivPolynomial (R := IsLocalRing.ResidueField A)
      (S := IsLocalRing.ResidueField A)
      ((PolynomialModule.coeffLinearEquiv (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A)).symm
      ((finsuppLEquivDirectSum (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A) ℕ).symm
        (DirectSum.of (fun _ : ℕ => IsLocalRing.ResidueField A) n c))) = _
    change PolynomialModule.equivPolynomial (R := IsLocalRing.ResidueField A)
      (S := IsLocalRing.ResidueField A)
      ((PolynomialModule.coeffLinearEquiv (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A)).symm
      ((finsuppLEquivDirectSum (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A) ℕ).symm
        (DirectSum.lof (IsLocalRing.ResidueField A) ℕ
          (fun _ : ℕ => IsLocalRing.ResidueField A) n c))) = _
    rw [finsuppLEquivDirectSum_symm_lof]
    rfl
  have hcomponent : ∀ (n : ℕ) (x : chapterGradedPiece A n),
      e (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) n x) =
        chapterGradedInclusion (A := A) π hπ n x := by
    intro n x
    obtain ⟨a, ha⟩ := hrep n x
    rw [ha]
    change ePoly (e₀ (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) n
      (chapterLayerRepresentative (A := A) π hπ n a))) = _
    rw [he₀, hePoly, hE, hIncl]
    exact (Polynomial.C_mul_X_pow_eq_monomial).symm
  refine ⟨e, hcomponent, ?_⟩
  calc
    e (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) 1
        (chapterUniformizerLayerClass (A := A) π hπ)) =
        chapterGradedInclusion (A := A) π hπ 1
          (chapterUniformizerLayerClass (A := A) π hπ) :=
      hcomponent 1 (chapterUniformizerLayerClass (A := A) π hπ)
    _ = Polynomial.C (IsLocalRing.residue A 1) * Polynomial.X ^ 1 := by
      exact hIncl 1 1
    _ = chapterInitialFormUniformizer (A := A) π hπ := by
      simp [chapterInitialFormUniformizer]

/-- Book §5.2: multiplication of successive quotient classes gives the graded product. -/
def chapterGradedPieceMultiplication (i j : ℕ) :
    chapterGradedPiece A i →ₗ[A]
      chapterGradedPiece A j →ₗ[A] chapterGradedPiece A (i + j) := by
  classical
  let eᵢ := chapterLayerMultiplicationEquiv (A := A) π hπ i
  let eⱼ := chapterLayerMultiplicationEquiv (A := A) π hπ j
  let eᵢⱼ := chapterLayerMultiplicationEquiv (A := A) π hπ (i + j)
  let μ : (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) →ₗ[A]
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) →ₗ[A]
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) :=
    LinearMap.mul A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A))
  exact
    { toFun := fun x =>
        { toFun := fun y => eᵢⱼ (μ (eᵢ.symm x) (eⱼ.symm y))
          map_add' := by
            intro y z
            rw [eⱼ.symm.map_add, (μ (eᵢ.symm x)).map_add, eᵢⱼ.map_add]
          map_smul' := by
            intro c y
            change eᵢⱼ ((μ (eᵢ.symm x)) (eⱼ.symm (c • y))) =
              (RingHom.id A) c • eᵢⱼ ((μ (eᵢ.symm x)) (eⱼ.symm y))
            rw [eⱼ.symm.map_smul, (μ (eᵢ.symm x)).map_smul,
              eᵢⱼ.map_smul]
            rfl }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        change eᵢⱼ ((μ (eᵢ.symm (x + y))) (eⱼ.symm z)) =
          eᵢⱼ ((μ (eᵢ.symm x)) (eⱼ.symm z)) +
            eᵢⱼ ((μ (eᵢ.symm y)) (eⱼ.symm z))
        have hμ := congrArg (fun f => f (eⱼ.symm z))
          (μ.map_add (eᵢ.symm x) (eᵢ.symm y))
        rw [eᵢ.symm.map_add, ← eᵢⱼ.map_add, hμ]
        simp only [LinearMap.add_apply]
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro y
        change eᵢⱼ ((μ (eᵢ.symm (c • x))) (eⱼ.symm y)) =
          (RingHom.id A) c • eᵢⱼ ((μ (eᵢ.symm x)) (eⱼ.symm y))
        have hμ := congrArg (fun f => f (eⱼ.symm y))
          (μ.map_smul c (eᵢ.symm x))
        rw [eᵢ.symm.map_smul, ← eᵢⱼ.map_smul, hμ]
        rfl }

/-- Book §5.2: the graded product sends uniformizer-layer representatives to
the representative of the product. -/
theorem chapterGradedPieceMultiplication_apply (i j : ℕ) (a b : A) :
    chapterGradedPieceMultiplication (A := A) π hπ i j
        (chapterLayerRepresentative (A := A) π hπ i a)
        (chapterLayerRepresentative (A := A) π hπ j b) =
      chapterLayerRepresentative (A := A) π hπ (i + j) (a * b) := by
  classical
  have hi :
      (chapterLayerMultiplicationEquiv (A := A) π hπ i).symm
          (chapterLayerRepresentative (A := A) π hπ i a) =
        Ideal.Quotient.mk _ a := by
    apply (chapterLayerMultiplicationEquiv (A := A) π hπ i).injective
    rw [(chapterLayerMultiplicationEquiv (A := A) π hπ i).apply_symm_apply]
    symm
    change chapterLayerMultiplicationMap (A := A) π hπ i
        (Ideal.Quotient.mk _ a) =
      chapterLayerRepresentative (A := A) π hπ i a
    exact chapterLayerMultiplicationMap_apply (A := A) π hπ i a
  have hj :
      (chapterLayerMultiplicationEquiv (A := A) π hπ j).symm
          (chapterLayerRepresentative (A := A) π hπ j b) =
        Ideal.Quotient.mk _ b := by
    apply (chapterLayerMultiplicationEquiv (A := A) π hπ j).injective
    rw [(chapterLayerMultiplicationEquiv (A := A) π hπ j).apply_symm_apply]
    symm
    change chapterLayerMultiplicationMap (A := A) π hπ j
        (Ideal.Quotient.mk _ b) =
      chapterLayerRepresentative (A := A) π hπ j b
    exact chapterLayerMultiplicationMap_apply (A := A) π hπ j b
  change (chapterLayerMultiplicationEquiv (A := A) π hπ (i + j))
      (LinearMap.mul A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A))
        ((chapterLayerMultiplicationEquiv (A := A) π hπ i).symm
          (chapterLayerRepresentative (A := A) π hπ i a))
        ((chapterLayerMultiplicationEquiv (A := A) π hπ j).symm
          (chapterLayerRepresentative (A := A) π hπ j b))) =
    chapterLayerRepresentative (A := A) π hπ (i + j) (a * b)
  rw [hi, hj]
  change (chapterLayerMultiplicationEquiv (A := A) π hπ (i + j))
      (Ideal.Quotient.mk _ (a * b)) =
    chapterLayerRepresentative (A := A) π hπ (i + j) (a * b)
  change chapterLayerMultiplicationMap (A := A) π hπ (i + j)
      (Ideal.Quotient.mk _ (a * b)) = _
  exact chapterLayerMultiplicationMap_apply (A := A) π hπ (i + j) (a * b)

/-- Book §5.2: initial forms multiply. -/
theorem chapter_initial_form_mul {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    chapterInitialForm (A := A) π hπ (x * y) =
      chapterInitialForm (A := A) π hπ x * chapterInitialForm (A := A) π hπ y := by
  classical
  obtain ⟨nx, ux, hux⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  obtain ⟨ny, uy, huy⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  have hxy : x * y = ((ux * uy : Aˣ) : A) * π ^ (nx + ny) := by
    rw [hux, huy, pow_add]
    simp [mul_assoc, mul_left_comm]
  rw [chapterInitialForm_eq_factorization (A := A) π hπ (mul_ne_zero hx hy)
      (ux * uy) hxy,
    chapterInitialForm_eq_factorization (A := A) π hπ hx ux hux,
    chapterInitialForm_eq_factorization (A := A) π hπ hy uy huy]
  simp [map_mul, pow_add, mul_assoc]
  ring

/-- Book §5.2: equal-degree initial forms can cancel, producing a strict valuation increase. -/
theorem chapter_initial_form_cancellation_strict_valuation
    {x y : A} (hx : x ≠ 0) (hy : y ≠ 0)
    (hdegree : IsDiscreteValuationRing.addVal A x =
      IsDiscreteValuationRing.addVal A y)
    (hcancel : chapterInitialForm (A := A) π hπ x +
        chapterInitialForm (A := A) π hπ y = 0) :
    IsDiscreteValuationRing.addVal A x <
      IsDiscreteValuationRing.addVal A (x + y) := by
  classical
  obtain ⟨nx, ux, hux⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  obtain ⟨ny, uy, huy⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  have hnx : nx = ny := by
    apply ENat.natCast_inj.mp
    calc
      (nx : ℕ∞) = IsDiscreteValuationRing.addVal A x := by
        rw [hux, IsDiscreteValuationRing.addVal_def' ux hπ nx]
      _ = IsDiscreteValuationRing.addVal A y := hdegree
      _ = (ny : ℕ∞) := by
        rw [huy, IsDiscreteValuationRing.addVal_def' uy hπ ny]
  have hcancel' :
      Polynomial.C (IsLocalRing.residue A (ux : A)) * Polynomial.X ^ nx +
        Polynomial.C (IsLocalRing.residue A (uy : A)) * Polynomial.X ^ nx = 0 := by
    simpa [chapterInitialForm_eq_factorization (A := A) π hπ hx ux hux,
      chapterInitialForm_eq_factorization (A := A) π hπ hy uy huy, hnx]
      using hcancel
  have hcoeff := congrArg (fun p : Polynomial (IsLocalRing.ResidueField A) => p.coeff nx)
    hcancel'
  have hres : IsLocalRing.residue A ((ux : A) + (uy : A)) = 0 := by
    simpa [map_add] using hcoeff
  have hmem : (ux : A) + (uy : A) ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (by
    rw [← hπ.maximalIdeal_eq]
    exact hmem)
  have hsum : x + y = c * π ^ (nx + 1) := by
    calc
      x + y = ((ux : A) + (uy : A)) * π ^ ny := by
        rw [hux, huy, hnx]
        ring
      _ = (c * π) * π ^ ny := by rw [hc]
      _ = c * π ^ (nx + 1) := by
        calc
          (c * π) * π ^ ny = c * (π * π ^ ny) := by ring
          _ = c * π ^ (ny + 1) := by rw [pow_succ']
          _ = c * π ^ (nx + 1) := by rw [hnx]
  have hdvd : π ^ (nx + 1) ∣ x + y := by
    refine ⟨c, ?_⟩
    simpa [mul_comm] using hsum
  have hle : (nx + 1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal A (x + y) := by
    have hle' := (IsDiscreteValuationRing.addVal_le_iff_dvd).2 hdvd
    rw [hπ.addVal_pow] at hle'
    exact hle'
  have hxval : IsDiscreteValuationRing.addVal A x = nx :=
    IsDiscreteValuationRing.addVal_def x ux hπ nx hux
  rw [hxval]
  exact lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self nx)) hle

/-- Book §5.2: relative to the original `π`-coordinate, replacing the
uniformizer by `uπ` rescales the degree-one generator by `ū`. -/
theorem chapter_initial_form_uniformizer_change
    (u : Aˣ) :
    chapterInitialForm (A := A) π hπ ((u : A) * π) =
      Polynomial.C (IsLocalRing.residue A (u : A)) *
        chapterInitialFormUniformizer (A := A) π hπ := by
  rw [chapterInitialForm_eq_factorization (A := A) π hπ
    (n := 1) (mul_ne_zero (Units.ne_zero u) hπ.ne_zero) u (by simp)]
  simp [chapterInitialFormUniformizer]

/-- A set of residue representatives, including `0`. -/
def chapterIsResidueRepresentativeSet (S : Set A) : Prop :=
  (0 : A) ∈ S ∧
    Function.Bijective (fun s : S => IsLocalRing.residue A (s : A))

/-- Book §5.2: residue representative sets exist. -/
theorem chapter_exists_residue_representative_set :
    ∃ S : Set A, chapterIsResidueRepresentativeSet A S := by
  classical
  let f := IsLocalRing.residue A
  let s : IsLocalRing.ResidueField A → A := fun r =>
    if r = 0 then 0 else Classical.choose (IsLocalRing.residue_surjective (R := A) r)
  have hs : ∀ r, f (s r) = r := by
    intro r
    by_cases hr : r = 0
    · simp [s, f, hr]
    · simpa [s, f, hr] using
        (Classical.choose_spec (IsLocalRing.residue_surjective (R := A) r))
  let S : Set A := Set.range s
  refine ⟨S, ⟨?_, ?_⟩⟩
  · exact ⟨0, by simp [s]⟩
  · constructor
    · intro x y hxy
      rcases x.property with ⟨r, hr⟩
      rcases y.property with ⟨t, ht⟩
      apply Subtype.ext
      have hres : f (s r) = f (s t) := by simpa [hr, ht] using hxy
      have hrt : r = t := by
        calc
          r = f (s r) := (hs r).symm
          _ = f (s t) := hres
          _ = t := hs t
      exact hr.symm.trans ((congrArg s hrt).trans ht)
    · intro r
      exact ⟨⟨s r, ⟨r, rfl⟩⟩, hs r⟩

/-- The finite digit polynomial attached to a list of representatives. -/
def chapterDigitExpansion (S : Set A) (n : ℕ) (digits : Fin n → S) : A :=
  ∑ i : Fin n, (digits i : A) * π ^ (i : ℕ)

/-- The class of a finite digit expansion modulo `π^n`. -/
def chapterDigitExpansionClass (S : Set A) (n : ℕ) (digits : Fin n → S) :
    A ⧸ (Ideal.span {π ^ n} : Ideal A) :=
  Ideal.Quotient.mk _ (chapterDigitExpansion (A := A) π S n digits)

/-- The representative chosen for the first residue digit of `x`. -/
noncomputable def chapterChosenResidueDigit
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S) (x : A) : S :=
  Classical.choose (hS.2.surjective (IsLocalRing.residue A x))

/-- Book §5.2: the chosen first digit has the same residue as `x`. -/
theorem chapterChosenResidueDigit_spec
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S) (x : A) :
    IsLocalRing.residue A (chapterChosenResidueDigit A S hS x : A) =
      IsLocalRing.residue A x := by
  exact Classical.choose_spec (hS.2.surjective (IsLocalRing.residue A x))

include π hπ in
/-- The quotient obtained after subtracting the first digit and dividing by `π`. -/
noncomputable def chapterDigitQuotient
    (π : A) (hπ : Irreducible π)
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S) (x : A) : A := by
  classical
  exact Classical.choose (show ∃ y : A,
      x - (chapterChosenResidueDigit A S hS x : A) = π * y from by
    have hz : IsLocalRing.residue A
        (x - (chapterChosenResidueDigit A S hS x : A)) = 0 := by
      rw [map_sub, chapterChosenResidueDigit_spec A S hS x]
      exact sub_self _
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp hz
    rw [hπ.maximalIdeal_eq] at hm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨y, by simpa [mul_comm] using hy.symm⟩)

/-- Book §5.2: one step of the digit extraction algorithm. -/
theorem chapter_digit_extraction_step
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S) (x : A) :
    x - (chapterChosenResidueDigit A S hS x : A) =
      π * chapterDigitQuotient (A := A) (π := π) (hπ := hπ) S hS x := by
  unfold chapterDigitQuotient
  exact Classical.choose_spec (show ∃ y : A,
      x - (chapterChosenResidueDigit A S hS x : A) = π * y from by
    have hz : IsLocalRing.residue A
        (x - (chapterChosenResidueDigit A S hS x : A)) = 0 := by
      rw [map_sub, chapterChosenResidueDigit_spec A S hS x]
      exact sub_self _
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp hz
    rw [hπ.maximalIdeal_eq] at hm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨y, by simpa [mul_comm] using hy.symm⟩)

include hπ in
/-- Book §5.2, displayed digit expansion: existence and uniqueness modulo `π^n`. -/
theorem chapter_unique_digit_expansion
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S) (n : ℕ) :
    ∀ x : A ⧸ (Ideal.span {π ^ n} : Ideal A),
      ∃! digits : Fin n → S,
        chapterDigitExpansionClass (A := A) π S n digits = x := by
  classical
  have hcons : ∀ (k : ℕ) (d : S) (tail : Fin k → S),
      chapterDigitExpansion (A := A) π S (k + 1) (Fin.cons d tail) =
        (d : A) + π * chapterDigitExpansion (A := A) π S k tail := by
    intro k d tail
    simp [chapterDigitExpansion, Fin.sum_univ_succ, pow_succ',
      Fin.cons, mul_comm, mul_left_comm]
    rw [Finset.mul_sum]
  have hrepr : ∀ (k : ℕ) (digits : Fin (k + 1) → S),
      Fin.cons (digits 0) (fun i => digits i.succ) = digits := by
    intro k digits
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  have hcancel_mem : ∀ (k : ℕ) {z : A},
      π * z ∈ (Ideal.span {π ^ (k + 1)} : Ideal A) →
        z ∈ (Ideal.span {π ^ k} : Ideal A) := by
    intro k z hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz
    refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
    apply mul_left_cancel₀ hπ.ne_zero
    calc
      π * (c * π ^ k) = c * π ^ (k + 1) := by
        rw [pow_succ']
        ring
      _ = π * z := hc
  have hpow_mem_max : ∀ (k : ℕ),
      (Ideal.span {π ^ (k + 1)} : Ideal A) ≤ IsLocalRing.maximalIdeal A := by
    intro k z hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz
    rw [hπ.maximalIdeal_eq]
    rw [← hc]
    apply Ideal.mul_mem_left _ c
    rw [pow_succ']
    simpa [mul_comm] using
      (Ideal.mul_mem_left _ (π ^ k) (Ideal.mem_span_singleton_self π))
  induction n with
  | zero =>
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨(fun i => Fin.elim0 i), ?_, ?_⟩
      · change Ideal.Quotient.mk (Ideal.span {π ^ 0}) 0 =
          Ideal.Quotient.mk (Ideal.span {π ^ 0}) a
        rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        rw [pow_zero, Ideal.span_singleton_one]
        simp
      · intro digits hdigits
        funext i
        exact Fin.elim0 i
  | succ k ih =>
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      let d : S := chapterChosenResidueDigit A S hS a
      let y : A := chapterDigitQuotient (A := A) π hπ S hS a
      obtain ⟨tail, htail, htail_unique⟩ :=
        ih (Ideal.Quotient.mk (Ideal.span {π ^ k}) y)
      have hexists :
          chapterDigitExpansionClass (A := A) π S (k + 1) (Fin.cons d tail) =
            Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)}) a := by
        change Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)})
              (chapterDigitExpansion (A := A) π S (k + 1) (Fin.cons d tail)) =
            Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)}) a
        rw [hcons]
        rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        have htail_mem :
            chapterDigitExpansion (A := A) π S k tail - y ∈
              (Ideal.span {π ^ k} : Ideal A) := by
          apply (Ideal.Quotient.eq_zero_iff_mem).mp
          change Ideal.Quotient.mk (Ideal.span {π ^ k})
              (chapterDigitExpansion (A := A) π S k tail - y) = 0
          rw [map_sub]
          exact sub_eq_zero.mpr htail
        have hstep := chapter_digit_extraction_step
          (A := A) (π := π) (hπ := hπ) S hS a
        have hrewrite :
            (d : A) + π * chapterDigitExpansion
                (A := A) π S k tail - a =
              π * (chapterDigitExpansion (A := A) π S k tail - y) := by
          change (chapterChosenResidueDigit A S hS a : A) +
              π * chapterDigitExpansion (A := A) π S k tail - a =
            π * (chapterDigitExpansion (A := A) π S k tail -
              chapterDigitQuotient (A := A) π hπ S hS a)
          calc
            (chapterChosenResidueDigit A S hS a : A) +
                π * chapterDigitExpansion (A := A) π S k tail - a =
              -(a - (chapterChosenResidueDigit A S hS a : A)) +
                π * chapterDigitExpansion (A := A) π S k tail := by ring
            _ = -(π * chapterDigitQuotient (A := A) π hπ S hS a) +
                π * chapterDigitExpansion (A := A) π S k tail := by
              rw [hstep]
            _ = π * (chapterDigitExpansion (A := A) π S k tail -
                chapterDigitQuotient (A := A) π hπ S hS a) := by ring
        have hm : chapterDigitExpansion (A := A) π S k tail - y ∈
            (Ideal.span {π ^ k} : Ideal A) := by
          exact htail_mem
        have hmemterm :
            π * (chapterDigitExpansion (A := A) π S k tail - y) ∈
              (Ideal.span {π ^ (k + 1)} : Ideal A) := by
          rw [show π ^ (k + 1) = π * π ^ k by
            rw [pow_succ']]
          rw [← Ideal.span_singleton_mul_span_singleton]
          exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self π) hm
        exact hrewrite ▸ hmemterm
      refine ⟨Fin.cons d tail, hexists, ?_⟩
      · intro digits₁ h₁
        let digits₂ : Fin (k + 1) → S := Fin.cons d tail
        have h₂ :
            chapterDigitExpansionClass (A := A) π S (k + 1) digits₂ =
              Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)}) a := by
          simpa [digits₂] using hexists
        have heq : chapterDigitExpansionClass (A := A) π S (k + 1) digits₁ =
            chapterDigitExpansionClass (A := A) π S (k + 1) digits₂ :=
          h₁.trans h₂.symm
        have hmem :
            chapterDigitExpansion (A := A) π S (k + 1) digits₁ -
              chapterDigitExpansion (A := A) π S (k + 1) digits₂ ∈
                (Ideal.span {π ^ (k + 1)} : Ideal A) := by
          apply (Ideal.Quotient.eq_zero_iff_mem).mp
          change Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)})
              (chapterDigitExpansion (A := A) π S (k + 1) digits₁ -
                chapterDigitExpansion (A := A) π S (k + 1) digits₂) = 0
          rw [map_sub]
          exact sub_eq_zero.mpr heq
        let tail₁ : Fin k → S := fun i => digits₁ i.succ
        let tail₂ : Fin k → S := fun i => digits₂ i.succ
        have hmem' := hmem
        rw [← hrepr (k := k) digits₁, ← hrepr (k := k) digits₂] at hmem'
        have hfirst : digits₁ 0 = digits₂ 0 := by
          have hdm : ((digits₁ 0 : S) : A) - (digits₂ 0 : S) ∈
              IsLocalRing.maximalIdeal A := by
            have hraw :
                chapterDigitExpansion (A := A) π S (k + 1)
                    (Fin.cons (digits₁ 0) tail₁) -
                    chapterDigitExpansion (A := A) π S (k + 1)
                      (Fin.cons (digits₂ 0) tail₂) -
                  π * (chapterDigitExpansion (A := A) π S k tail₁ -
                    chapterDigitExpansion (A := A) π S k tail₂) ∈
                IsLocalRing.maximalIdeal A := by
              apply Ideal.sub_mem (IsLocalRing.maximalIdeal A)
              · exact hpow_mem_max k hmem'
              · rw [hπ.maximalIdeal_eq]
                simpa [mul_comm] using
                  (Ideal.mul_mem_left (Ideal.span {π})
                    (chapterDigitExpansion (A := A) π S k tail₁ -
                      chapterDigitExpansion (A := A) π S k tail₂)
                    (Ideal.mem_span_singleton_self π))
            simpa [hcons, tail₁, tail₂, sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_assoc,
              mul_comm, mul_left_comm] using hraw
          apply hS.2.1
          apply sub_eq_zero.mp
          rw [← map_sub]
          apply (IsLocalRing.residue_eq_zero_iff _).2
          exact hdm
        have htail_mem :
            chapterDigitExpansion (A := A) π S k tail₁ -
              chapterDigitExpansion (A := A) π S k tail₂ ∈
                (Ideal.span {π ^ k} : Ideal A) := by
          apply hcancel_mem k
          simpa [hcons, tail₁, tail₂, hfirst, sub_eq_add_neg,
            add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_assoc,
            mul_comm, mul_left_comm] using hmem'
        have htail_eq : chapterDigitExpansionClass (A := A) π S k tail₁ =
            chapterDigitExpansionClass (A := A) π S k tail₂ := by
          apply sub_eq_zero.mp
          change Ideal.Quotient.mk (Ideal.span {π ^ k})
              (chapterDigitExpansion (A := A) π S k tail₁ -
                chapterDigitExpansion (A := A) π S k tail₂) = 0
          exact (Ideal.Quotient.eq_zero_iff_mem).2 htail_mem
        have htail_fun : tail₁ = tail₂ := by
          apply (ih (chapterDigitExpansionClass (A := A) π S k tail₁)).unique
          · rfl
          · exact htail_eq.symm
        calc
          digits₁ = Fin.cons (digits₁ 0) tail₁ :=
            (hrepr (k := k) digits₁).symm
          _ = Fin.cons (digits₂ 0) tail₂ := by rw [hfirst, htail_fun]
          _ = digits₂ := hrepr (k := k) digits₂
          _ = Fin.cons d tail := by rfl

/-- The `n`th prefix of an infinite digit string. -/
def chapterInfiniteDigitPrefix (S : Set A) (digits : ℕ → S) (n : ℕ) : A :=
  Finset.sum (Finset.range n) (fun i => (digits i : A) * π ^ i)

include hπ in
/-- Book §5.2: in an adically complete ring, every infinite digit string converges. -/
theorem chapter_infinite_digit_expansion_exists
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (digits : ℕ → S) :
    ∃ x : A, ∀ n : ℕ,
      x - chapterInfiniteDigitPrefix (A := A) π S digits n ∈
        IsLocalRing.maximalIdeal A ^ n := by
  classical
  let t : ℕ → A := fun i => (digits i : A) * π ^ i
  let f : ℕ → A := fun n => ∑ i ∈ Finset.range n, t i
  have hfdiff : ∀ {m n : ℕ}, m ≤ n →
      f n - f m ∈ (IsLocalRing.maximalIdeal A) ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
        have hstep : f (n + 1) - f m = (f n - f m) + t n := by
          calc
            f (n + 1) - f m = (f n + t n) - f m := by
              simp [f, t, Finset.sum_range_succ]
            _ = (f n - f m) + t n := by ring
        rw [hstep]
        apply Ideal.add_mem
        · exact ih
        · have hpow : π ^ n ∈ (IsLocalRing.maximalIdeal A) ^ m := by
            exact (Ideal.pow_le_pow_right hmn) (by
              rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
              exact Ideal.mem_span_singleton_self _)
          exact Ideal.mul_mem_left _ (digits n : A) hpow
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((IsLocalRing.maximalIdeal A) ^ m •
        (⊤ : Submodule A A))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    simpa [sub_eq_add_neg, add_comm] using
      (neg_mem (hfdiff hmn))
  obtain ⟨x, hx⟩ := IsPrecomplete.prec
    (I := IsLocalRing.maximalIdeal A) (M := A)
    (IsAdicComplete.toIsPrecomplete (I := IsLocalRing.maximalIdeal A) (M := A))
    (f := f) hcauchy
  refine ⟨x, ?_⟩
  intro n
  have hn : f n - x ∈ (IsLocalRing.maximalIdeal A) ^ n := by
    simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hx n
  simpa [f, t, chapterInfiniteDigitPrefix, sub_eq_add_neg, add_comm] using
    (neg_mem hn)

include hπ in
/-- Book §5.2: Hausdorffness makes the infinite digit expansion unique. -/
theorem chapter_infinite_digit_expansion_unique
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (digits : ℕ → S) :
    ∃! x : A, ∀ n : ℕ,
      x - chapterInfiniteDigitPrefix (A := A) π S digits n ∈
        IsLocalRing.maximalIdeal A ^ n := by
  classical
  obtain ⟨x, hx⟩ := chapter_infinite_digit_expansion_exists
    (A := A) (π := π) (hπ := hπ) S hS digits
  refine ⟨x, hx, ?_⟩
  intro y hy
  symm
  apply (IsHausdorff.eq_iff_smodEq
    (I := IsLocalRing.maximalIdeal A) (x := x) (y := y)).2
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  have hxy :
      (x - chapterInfiniteDigitPrefix (A := A) π S digits n) -
          (y - chapterInfiniteDigitPrefix (A := A) π S digits n) ∈
        (IsLocalRing.maximalIdeal A) ^ n :=
    Ideal.sub_mem _ (hx n) (hy n)
  convert hxy using 1; ring

include hπ in
/-- Book §5.2: in an adically complete DVR, every element has a unique
infinite digit expansion. -/
theorem chapter_complete_element_unique_infinite_digit_expansion
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (x : A) :
    ∃! digits : ℕ → S, ∀ n : ℕ,
      x - chapterInfiniteDigitPrefix (A := A) π S digits n ∈
        IsLocalRing.maximalIdeal A ^ n := by
  classical
  let q : ℕ → A := Nat.rec x (fun _ y =>
    chapterDigitQuotient (A := A) π hπ S hS y)
  let digits : ℕ → S := fun n =>
    chapterChosenResidueDigit A S hS (q n)
  have hq (n : ℕ) : q (n + 1) =
      chapterDigitQuotient (A := A) π hπ S hS (q n) := by
    rfl
  have hprefix : ∀ n : ℕ,
      x - chapterInfiniteDigitPrefix (A := A) π S digits n =
        π ^ n * q n := by
    intro n
    induction n with
    | zero => simp [chapterInfiniteDigitPrefix, q]
    | succ n ih =>
      have hstep := chapter_digit_extraction_step
        (A := A) (π := π) (hπ := hπ) S hS (q n)
      have hstep' : q n - (digits n : A) = π * q (n + 1) := by
        simpa [digits, hq n] using hstep
      calc
        x - chapterInfiniteDigitPrefix (A := A) π S digits (n + 1) =
            (x - chapterInfiniteDigitPrefix (A := A) π S digits n) -
              (digits n : A) * π ^ n := by
                simp [chapterInfiniteDigitPrefix, Finset.sum_range_succ]
                ring
        _ = π ^ n * q n - (digits n : A) * π ^ n := by rw [ih]
        _ = π ^ n * (q n - (digits n : A)) := by ring
        _ = π ^ n * (π * q (n + 1)) := by rw [hstep']
        _ = π ^ (n + 1) * q (n + 1) := by
          rw [pow_succ']
          ring
  have hex : ∀ n : ℕ,
      x - chapterInfiniteDigitPrefix (A := A) π S digits n ∈
        IsLocalRing.maximalIdeal A ^ n := by
    intro n
    rw [hprefix n, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    simpa [mul_comm] using
      (Ideal.mul_mem_left (Ideal.span {π ^ n}) (q n)
        (Ideal.mem_span_singleton_self (π ^ n)))
  refine ⟨digits, hex, ?_⟩
  intro digits' hdigits'
  funext n
  apply Subtype.ext
  have hprefix_eq (d : ℕ → S) (m : ℕ) :
      chapterDigitExpansion (A := A) π S m (fun i => d i) =
        chapterInfiniteDigitPrefix (A := A) π S d m := by
    rw [chapterDigitExpansion, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have hfinite : (fun i : Fin (n + 1) => digits' i) =
      (fun i : Fin (n + 1) => digits i) := by
    have hmem :
        chapterDigitExpansion (A := A) π S (n + 1) (fun i => digits' i) -
          chapterDigitExpansion (A := A) π S (n + 1) (fun i => digits i) ∈
          Ideal.span {π ^ (n + 1)} := by
      have hsub := Ideal.sub_mem (IsLocalRing.maximalIdeal A ^ (n + 1))
        (hex (n + 1)) (hdigits' (n + 1))
      have hsub' :
          chapterInfiniteDigitPrefix (A := A) π S digits' (n + 1) -
              chapterInfiniteDigitPrefix (A := A) π S digits (n + 1) ∈
            IsLocalRing.maximalIdeal A ^ (n + 1) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub
      rw [hprefix_eq digits' (n + 1), hprefix_eq digits (n + 1)]
      simpa [hπ.maximalIdeal_eq, Ideal.span_singleton_pow] using hsub'
    have hclass :
        chapterDigitExpansionClass (A := A) π S (n + 1) (fun i => digits' i) =
          chapterDigitExpansionClass (A := A) π S (n + 1) (fun i => digits i) := by
      apply sub_eq_zero.mp
      change Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})
          (chapterDigitExpansion (A := A) π S (n + 1) (fun i => digits' i) -
            chapterDigitExpansion (A := A) π S (n + 1) (fun i => digits i)) = 0
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem
    exact (chapter_unique_digit_expansion
      (A := A) (π := π) (hπ := hπ) S hS (n + 1)
      (chapterDigitExpansionClass (A := A) π S (n + 1) (fun i => digits' i))).unique
      rfl hclass.symm
  simpa using congrArg Subtype.val (congrFun hfinite ⟨n, Nat.lt_succ_self n⟩)

/-- The localization `ℤ_(p)` used in the base-`p` example. -/
abbrev chapterZLocalizedAtPrime (p : ℕ) [Fact p.Prime] :=
  Localization.AtPrime
    (Ideal.span ({(p : ℤ)} : Set ℤ))

/-- The finite prefix represented by the first `n` digits of a base-`p` string. -/
def chapterBasePDigitPrefix (p : ℕ) (digits : ℕ → Fin p) (n : ℕ) : ℤ :=
  Finset.sum (Finset.range n) (fun i => ((digits i : ℕ) : ℤ) * (p : ℤ) ^ i)

/-- Congruence meaning that a localized integer represents a base-`p` digit string. -/
def chapterBasePStringRepresents (p : ℕ) [Fact p.Prime] (digits : ℕ → Fin p)
    (x : chapterZLocalizedAtPrime p) : Prop :=
  ∀ n : ℕ,
    x - algebraMap ℤ (chapterZLocalizedAtPrime p) (chapterBasePDigitPrefix p digits n) ∈
      Ideal.span {algebraMap ℤ (chapterZLocalizedAtPrime p) ((p : ℤ) ^ n)}

/-- Book §5.2, base-`p` example: not every infinite string represents an element of `ℤ_(p)`. -/
theorem chapter_not_every_infinite_base_p_string_represents_a_localized_integer
    (p : ℕ) [Fact p.Prime] :
    ∃ digits : ℕ → Fin p,
      ¬ ∃ x : chapterZLocalizedAtPrime p, chapterBasePStringRepresents p digits x := by
  classical
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hPprime : P.IsPrime := by
    dsimp [P]
    exact Ideal.isPrime_span_singleton_of_prime
      (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))
  have hprefix_succ (digits : ℕ → Fin p) (n : ℕ) :
      chapterBasePDigitPrefix p digits (n + 1) =
        chapterBasePDigitPrefix p digits n +
          ((digits n : ℕ) : ℤ) * (p : ℤ) ^ n := by
    simp [chapterBasePDigitPrefix, Finset.sum_range_succ]
  have hmod : ∀ (x : chapterZLocalizedAtPrime p)
      (digits₁ digits₂ : ℕ → Fin p),
      chapterBasePStringRepresents p digits₁ x →
      chapterBasePStringRepresents p digits₂ x →
      ∀ n : ℕ,
        chapterBasePDigitPrefix p digits₁ n ≡
          chapterBasePDigitPrefix p digits₂ n [ZMOD (p : ℤ) ^ n] := by
    intro x digits₁ digits₂ hx₁ hx₂ n
    have hmem :
        algebraMap ℤ (chapterZLocalizedAtPrime p)
            (chapterBasePDigitPrefix p digits₂ n -
              chapterBasePDigitPrefix p digits₁ n) ∈
          Ideal.span {algebraMap ℤ (chapterZLocalizedAtPrime p) ((p : ℤ) ^ n)} := by
      have hsub := Ideal.sub_mem
        (Ideal.span {algebraMap ℤ (chapterZLocalizedAtPrime p) ((p : ℤ) ^ n)})
        (hx₁ n) (hx₂ n)
      simpa [map_sub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsub
    have hmap :
        algebraMap ℤ (chapterZLocalizedAtPrime p)
            (chapterBasePDigitPrefix p digits₂ n -
              chapterBasePDigitPrefix p digits₁ n) ∈
          Ideal.map (algebraMap ℤ (chapterZLocalizedAtPrime p))
            (Ideal.span {((p : ℤ) ^ n)}) := by
      simpa [Ideal.map_span] using hmem
    obtain ⟨m, hm, hmprod⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (M := P.primeCompl) (S := chapterZLocalizedAtPrime p)
        (Ideal.span {((p : ℤ) ^ n)})
        (chapterBasePDigitPrefix p digits₂ n -
          chapterBasePDigitPrefix p digits₁ n)).mp hmap
    change m ∉ P at hm
    have hmprod' : m *
          (chapterBasePDigitPrefix p digits₂ n -
            chapterBasePDigitPrefix p digits₁ n) ∈ P ^ n := by
      rw [show P ^ n = Ideal.span {((p : ℤ) ^ n)} by
        change (Ideal.span ({(p : ℤ)} : Set ℤ)) ^ n =
          Ideal.span {((p : ℤ) ^ n)}
        exact Ideal.span_singleton_pow (p : ℤ) n]
      exact hmprod
    have hdiff :
        chapterBasePDigitPrefix p digits₂ n -
            chapterBasePDigitPrefix p digits₁ n ∈ P ^ n :=
      (Ideal.IsPrime.mul_mem_pow P (hI := hPprime) hmprod').resolve_left hm
    have hdiv :
        ((p : ℤ) ^ n) ∣
          chapterBasePDigitPrefix p digits₂ n -
            chapterBasePDigitPrefix p digits₁ n := by
      apply Ideal.mem_span_singleton.mp
      simpa [P, Ideal.span_singleton_pow] using hdiff
    rw [Int.modEq_iff_dvd]
    exact hdiv
  have hunique : ∀ (x : chapterZLocalizedAtPrime p)
      (digits₁ digits₂ : ℕ → Fin p),
      chapterBasePStringRepresents p digits₁ x →
      chapterBasePStringRepresents p digits₂ x → digits₁ = digits₂ := by
    intro x digits₁ digits₂ hx₁ hx₂
    funext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hprefix :
            chapterBasePDigitPrefix p digits₁ n =
              chapterBasePDigitPrefix p digits₂ n := by
          unfold chapterBasePDigitPrefix
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih k (Finset.mem_range.mp hk)]
        have hmul := hmod x digits₁ digits₂ hx₁ hx₂ (n + 1)
        rw [hprefix_succ digits₁ n, hprefix_succ digits₂ n, hprefix] at hmul
        have hmul' := Int.ModEq.add_left_cancel'
          (chapterBasePDigitPrefix p digits₂ n) hmul
        have hdigit :
            ((digits₁ n : ℕ) : ℤ) ≡ ((digits₂ n : ℕ) : ℤ)
              [ZMOD (p : ℤ)] := by
          apply Int.ModEq.mul_right_cancel'
            (c := (p : ℤ) ^ n) (m := (p : ℤ))
            (pow_ne_zero n
              (Int.ofNat_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero))
          simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using hmul'
        have hmodnat :
            (digits₁ n : ℕ) % p = (digits₂ n : ℕ) % p := by
          have hmodint :
              ((digits₁ n : ℕ) : ℤ) % (p : ℤ) =
                ((digits₂ n : ℕ) : ℤ) % (p : ℤ) := by
            simpa [Int.ModEq] using hdigit
          rw [← Int.natCast_mod, ← Int.natCast_mod] at hmodint
          exact_mod_cast hmodint
        have hval : (digits₁ n : ℕ) = (digits₂ n : ℕ) := by
          simpa [Nat.mod_eq_of_lt (digits₁ n).isLt,
            Nat.mod_eq_of_lt (digits₂ n).isLt] using hmodnat
        exact Fin.ext hval
  have hnotcount : ¬ Countable (ℕ → Fin p) := by
    intro hcount
    obtain ⟨f, hf⟩ := @exists_surjective_nat (ℕ → Fin p) inferInstance hcount
    let zero : Fin p := ⟨0, (Fact.out : Nat.Prime p).pos⟩
    let one : Fin p := ⟨1, (Fact.out : Nat.Prime p).one_lt⟩
    have hone : one ≠ zero := by
      intro h
      have hv := congrArg Fin.val h
      norm_num at hv
    let diagonal : ℕ → Fin p := fun n => if f n n = zero then one else zero
    have hdiag : ∀ n, diagonal n ≠ f n n := by
      intro n
      by_cases h : f n n = zero
      · simp only [diagonal, h]
        exact hone
      · simp only [diagonal, h]
        exact Ne.symm h
    obtain ⟨n, hn⟩ := hf diagonal
    exact hdiag n (congrFun hn n).symm
  by_contra h
  have hall : ∀ digits : ℕ → Fin p,
      ∃ x : chapterZLocalizedAtPrime p,
        chapterBasePStringRepresents p digits x := by
    intro digits
    by_contra hd
    exact h ⟨digits, hd⟩
  let representative : (ℕ → Fin p) → chapterZLocalizedAtPrime p :=
    fun digits => Classical.choose (hall digits)
  have hrepresentative : ∀ digits : ℕ → Fin p,
      chapterBasePStringRepresents p digits (representative digits) := by
    intro digits
    dsimp [representative]
    exact Classical.choose_spec (hall digits)
  have hinjective : Function.Injective representative := by
    intro digits₁ digits₂ heq
    apply hunique (representative digits₁) digits₁ digits₂
    · exact hrepresentative digits₁
    · simpa [heq] using hrepresentative digits₂
  have hsurjective : Function.Surjective
      (fun z : ℤ × P.primeCompl =>
        IsLocalization.mk' (chapterZLocalizedAtPrime p) z.1 z.2) :=
    IsLocalization.mk'_surjective P.primeCompl
  exact hnotcount
    (@Function.Injective.countable (ℕ → Fin p) (chapterZLocalizedAtPrime p)
      hsurjective.countable representative hinjective)

/-- The cardinality of the residue field. -/
def chapterResidueCardinality : ℕ := Nat.card (IsLocalRing.ResidueField A)

include hπ in
/-- Book §5.2: if `|k| = q`, then `|A/(π^n)| = q^n`. -/
theorem chapter_quotient_cardinality_pow
    [Finite (IsLocalRing.ResidueField A)] (n : ℕ) :
    Nat.card (A ⧸ (Ideal.span {π ^ n} : Ideal A)) =
      chapterResidueCardinality A ^ n := by
  classical
  rw [← chapter_maximalIdeal_pow_eq_uniformizer_span A π hπ n,
    ← Submodule.cardQuot_apply]
  calc
    Submodule.cardQuot (IsLocalRing.maximalIdeal A ^ n) =
        Submodule.cardQuot (IsLocalRing.maximalIdeal A) ^ n :=
      cardQuot_pow_of_prime
        (P := IsLocalRing.maximalIdeal A)
        (by
          rw [hπ.maximalIdeal_eq]
          exact fun h => hπ.ne_zero (Ideal.span_singleton_eq_bot.mp h))
    _ = Nat.card (IsLocalRing.ResidueField A) ^ n := by
      rw [Submodule.cardQuot_apply]
      rfl

/-- The image of the uniformizer in the truncated quotient. -/
def chapterQuotientUniformizer (n : ℕ) :
    A ⧸ (Ideal.span {π ^ n} : Ideal A) :=
  Ideal.Quotient.mk _ π

include hπ in
/-- Book §5.2: the truncated quotient is Artinian local. -/
-- The truncation index is explicitly positive, as is conventional for
-- quotients called truncated DVRs.
theorem chapter_quotient_is_artinian_local (n : ℕ) (hn : 0 < n) :
    IsArtinianRing (A ⧸ (Ideal.span {π ^ n} : Ideal A)) ∧
      IsLocalRing (A ⧸ (Ideal.span {π ^ n} : Ideal A)) := by
  classical
  let I : Ideal A := Ideal.span {π ^ n}
  let Q := A ⧸ I
  have hunit : ¬ IsUnit (π ^ n) := by
    intro h
    have hn0 : n = 0 :=
      (isUnit_pow_iff_of_not_isUnit hπ.not_isUnit).mp h
    exact (Nat.ne_of_gt hn) hn0
  have hItop : I ≠ ⊤ := by
    exact Ideal.span_singleton_ne_top hunit
  have hQnontrivial : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hItop
  have hQlocal : IsLocalRing Q :=
    letI : Nontrivial Q := hQnontrivial
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hnil :
      IsNilpotent (@IsLocalRing.maximalIdeal Q _ hQlocal) :=
    letI : Nontrivial Q := hQnontrivial
    letI : IsLocalRing Q := hQlocal
    by
      refine ⟨n, ?_⟩
      rw [← IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, ← Ideal.map_pow,
        hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      apply (Ideal.map_eq_bot_iff_le_ker _).2
      rw [Ideal.mk_ker]
  have hArt : IsArtinianRing Q :=
    letI : Nontrivial Q := hQnontrivial
    letI : IsLocalRing Q := hQlocal
    (isArtinianRing_iff_isNilpotent_maximalIdeal Q).2 hnil
  exact ⟨by simpa [I, Q] using hArt, by simpa [I, Q] using hQlocal⟩

include hπ in
/-- Book §5.2: all ideals of the truncated quotient are powers of `π̄`. -/
theorem chapter_quotient_ideals_are_uniformizer_powers (n : ℕ) :
    ∀ I : Ideal (A ⧸ (Ideal.span {π ^ n} : Ideal A)),
      ∃ i : Fin (n + 1),
        I = Ideal.span {(chapterQuotientUniformizer (A := A) π n) ^ (i : ℕ)} := by
  classical
  intro I
  let I₀ : Ideal A := Ideal.span {π ^ n}
  let q : A →+* (A ⧸ I₀) := Ideal.Quotient.mk I₀
  let J : Ideal A := I.comap q
  have hI₀J : I₀ ≤ J := by
    intro x hx
    change q x ∈ I
    have hqx : q x = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 hx
    rw [hqx]
    exact I.zero_mem
  have hJne : J ≠ ⊥ := by
    intro hJ
    have hmem : π ^ n ∈ J := by
      apply hI₀J
      exact Ideal.mem_span_singleton_self _
    rw [hJ] at hmem
    have hzero : π ^ n = 0 := by
      exact (Submodule.mem_bot A).1 hmem
    exact (pow_ne_zero n hπ.ne_zero) hzero
  obtain ⟨i, hi⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJne hπ
  have hdiv : π ^ i ∣ π ^ n := by
    apply Ideal.mem_span_singleton.mp
    rw [← hi]
    exact hI₀J (Ideal.mem_span_singleton_self _)
  have hin : i ≤ n := by
    have hval := (IsDiscreteValuationRing.addVal_le_iff_dvd).2 hdiv
    rw [hπ.addVal_pow, hπ.addVal_pow] at hval
    exact ENat.natCast_le_natCast.mp hval
  refine ⟨⟨i, Nat.lt_succ_of_le hin⟩, ?_⟩
  change I = Ideal.span {(q π) ^ i}
  calc
    I = Ideal.map q (I.comap q) :=
      (Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective I).symm
    _ = Ideal.map q J := rfl
    _ = Ideal.map q (Ideal.span {π ^ i}) := by rw [hi]
    _ = Ideal.span {q (π ^ i)} := by rw [Ideal.map_span]; simp
    _ = Ideal.span {(q π) ^ i} := by rw [map_pow]

include hπ in
/-- Book §5.2: `π̄` has nilpotence index exactly `n` for `n > 0`. -/
theorem chapter_quotient_uniformizer_nilpotence_index
    (n : ℕ) (hn : 0 < n) :
    (chapterQuotientUniformizer (A := A) π n) ^ n = 0 ∧
      (chapterQuotientUniformizer (A := A) π n) ^ (n - 1) ≠ 0 := by
  classical
  constructor
  · change (Ideal.Quotient.mk (Ideal.span {π ^ n}) π) ^ n = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  · intro hzero
    have hzero' :
        Ideal.Quotient.mk (Ideal.span {π ^ n}) (π ^ (n - 1)) = 0 := by
      simpa [chapterQuotientUniformizer, map_pow] using hzero
    have hmem : π ^ (n - 1) ∈ Ideal.span {π ^ n} :=
      (Ideal.Quotient.eq_zero_iff_mem).mp hzero'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    have hunit : IsUnit π := by
      have hpow : π ^ (n - 1) = c * π ^ n := hc.symm
      have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')
      have hpow' : π ^ (n - 1) = (c * π) * π ^ (n - 1) := by
        calc
          π ^ (n - 1) = c * π ^ n := hpow
          _ = c * (π * π ^ (n - 1)) := by
            rw [← pow_succ', hn']
          _ = (c * π) * π ^ (n - 1) := by ring
      have hone : (c * π) = 1 := by
        apply mul_right_cancel₀ (pow_ne_zero (n - 1) hπ.ne_zero)
        simpa [one_mul] using hpow'.symm
      exact IsUnit.of_mul_eq_one c (by simpa [mul_comm] using hone)
    exact hπ.not_isUnit hunit

end LeadingTermsAndDigits

section FractionalIdealsAndPrecision

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
variable (π : A) (hπ : Irreducible π)

/-- A principal fractional ideal generated by a field element. -/
def chapterPrincipalFractionalIdeal (x : K) :
    FractionalIdeal (nonZeroDivisors A) K :=
  FractionalIdeal.spanSingleton (nonZeroDivisors A) x

/-- Book §5.3: the valuation filtration extended to all integer indices. -/
def chapterFractionalFiltration (n : ℤ) :
    FractionalIdeal (nonZeroDivisors A) K :=
  FractionalIdeal.spanSingleton (nonZeroDivisors A)
    ((algebraMap A K π) ^ n)

include hπ in
/-- Book §5.3: nonnegative filtration levels recover the integral powers. -/
theorem chapter_fractional_filtration_natCast_eq (n : ℕ) :
    chapterFractionalFiltration (A := A) (K := K) π n =
      ((IsLocalRing.maximalIdeal A ^ n : Ideal A) :
        FractionalIdeal (nonZeroDivisors A) K) := by
  rw [chapterFractionalFiltration, zpow_natCast,
    ← map_pow, ← FractionalIdeal.coeIdeal_span_singleton]
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]

include hπ in
/-- Book §5.3: every nonzero fractional ideal has a unique integer level. -/
theorem chapter_nonzero_fractional_ideal_unique_level
    (I : FractionalIdeal (nonZeroDivisors A) K) (hI : I ≠ 0) :
    ∃! n : ℤ,
      I = chapterFractionalFiltration (A := A) (K := K) π n := by
  classical
  have hπK : algebraMap A K π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply IsFractionRing.injective A K
    simpa using h
  let g : K := Submodule.IsPrincipal.generator (I : Submodule A K)
  have hg : g ≠ 0 := by
    intro hg
    apply hI
    have hg' : Submodule.IsPrincipal.generator (I : Submodule A K) = 0 := by
      simpa [g] using hg
    rw [FractionalIdeal.eq_spanSingleton_of_principal I, hg',
      FractionalIdeal.spanSingleton_zero]
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hg
  have hgen : I = FractionalIdeal.spanSingleton (nonZeroDivisors A)
      ((algebraMap A K π) ^ n) := by
    have hgen0 : I = FractionalIdeal.spanSingleton (nonZeroDivisors A) g := by
      simpa [g] using FractionalIdeal.eq_spanSingleton_of_principal I
    calc
      I = FractionalIdeal.spanSingleton (nonZeroDivisors A) g := hgen0
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors A)
          (u • (algebraMap A K π) ^ n) := by rw [hu]
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors A)
          ((algebraMap A K π) ^ n) := by
        apply (FractionalIdeal.spanSingleton_eq_spanSingleton).2
        exact ⟨u⁻¹, by simp [smul_smul]⟩
  refine ⟨n, ?_, ?_⟩
  · simpa [chapterFractionalFiltration] using hgen
  · intro m hm
    have hpow :
        FractionalIdeal.spanSingleton (nonZeroDivisors A)
            ((algebraMap A K π) ^ n) =
          FractionalIdeal.spanSingleton (nonZeroDivisors A)
            ((algebraMap A K π) ^ m) := by
      simpa [chapterFractionalFiltration] using hgen.symm.trans hm
    obtain ⟨u', hu'⟩ :=
      (FractionalIdeal.spanSingleton_eq_spanSingleton).1 hpow
    let v : IsDedekindDomain.HeightOneSpectrum A :=
      { asIdeal := IsLocalRing.maximalIdeal A
        isPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
        ne_bot := by
          rw [hπ.maximalIdeal_eq]
          exact fun h => hπ.ne_zero (Ideal.span_singleton_eq_bot.mp h) }
    let w : Valuation K ℤᵐ⁰ := v.valuation K
    have hwπ : w (algebraMap A K π) = WithZero.exp (-1 : ℤ) := by
      dsimp [w]
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        v.intValuation_singleton hπ.ne_zero
          hπ.maximalIdeal_eq]
      rfl
    have hnm : n = m := by
      have huval : w (algebraMap A K (u' : A)) = 1 := by
        dsimp [w]
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          v.intValuation_eq_one_iff.mpr]
        exact (IsLocalRing.notMem_maximalIdeal).2 u'.isUnit
      have hval := congrArg (fun z : K => w z) hu'
      have hnmz : (-(n : ℤ)) = -(m : ℤ) := by
        have hpow : (WithZero.exp (-1 : ℤ)) ^ n =
            (WithZero.exp (-1 : ℤ)) ^ m := by
          simpa [Units.smul_def, Algebra.smul_def, huval, hwπ, map_zpow] using hval
        apply WithZero.exp_injective
        simpa [← WithZero.exp_zsmul] using hpow
      exact neg_injective hnmz
    exact hnm.symm

/- The actual group of nonzero fractional ideals; its operation is supplied
   below rather than replacing the ideals by an isomorphic copy of `ℤ`. -/
def chapterNonzeroFractionalIdealGroup : Type _ :=
  {I : FractionalIdeal (nonZeroDivisors A) K // I ≠ 0}

/-- The group operations are the multiplication and inverse of fractional ideals,
restricted to the nonzero ideals. -/
noncomputable instance chapterNonzeroFractionalIdealGroup.instGroup :
    Group (chapterNonzeroFractionalIdealGroup (A := A) (K := K)) where
  mul I J := ⟨I.1 * J.1, by
    exact mul_ne_zero I.2 J.2⟩
  one := ⟨1, by simp⟩
  inv I := ⟨I.1⁻¹, by
    exact inv_ne_zero I.2⟩
  mul_assoc := by
    intro a b c
    apply Subtype.ext
    exact mul_assoc _ _ _
  one_mul := by
    intro a
    apply Subtype.ext
    exact one_mul _
  mul_one := by
    intro a
    apply Subtype.ext
    exact mul_one _
  div I J := ⟨I.1 / J.1, by
    exact div_ne_zero I.2 J.2⟩
  div_eq_mul_inv := by
    intro a b
    apply Subtype.ext
    exact div_eq_mul_inv _ _
  inv_mul_cancel := by
    intro a
    apply Subtype.ext
    exact inv_mul_cancel₀ a.2

/-- The image of `Aˣ` in `Kˣ`. -/
def chapterRingUnitImage : Subgroup Kˣ :=
  (Units.map (algebraMap A K).toMonoidHom).range

/-- The quotient `Kˣ/Aˣ`. -/
abbrev chapterFieldUnitQuotient : Type _ :=
  Kˣ ⧸ chapterRingUnitImage (A := A) (K := K)

noncomputable def chapterNonzeroFractionalIdealGroupEquivInt' :
    chapterNonzeroFractionalIdealGroup (A := A) (K := K) ≃* Multiplicative ℤ := by
  classical
  have hπK : algebraMap A K π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply IsFractionRing.injective A K
    simpa using h
  let F : ℤ → chapterNonzeroFractionalIdealGroup (A := A) (K := K) := fun n =>
    ⟨chapterFractionalFiltration (A := A) (K := K) π n, by
      apply FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      exact zpow_ne_zero n hπK⟩
  let level : chapterNonzeroFractionalIdealGroup (A := A) (K := K) → ℤ := fun I =>
    Classical.choose (chapter_nonzero_fractional_ideal_unique_level
      (A := A) (K := K) π hπ I.1 I.2)
  have hlevel (I : chapterNonzeroFractionalIdealGroup (A := A) (K := K)) :
      I.1 = (F (level I)).1 := by
    exact (Classical.choose_spec (chapter_nonzero_fractional_ideal_unique_level
      (A := A) (K := K) π hπ I.1 I.2)
      ).1
  have hFmul (n m : ℤ) : F n * F m = F (n + m) := by
    apply Subtype.ext
    change FractionalIdeal.spanSingleton (nonZeroDivisors A) ((algebraMap A K π) ^ n) *
        FractionalIdeal.spanSingleton (nonZeroDivisors A) ((algebraMap A K π) ^ m) =
      FractionalIdeal.spanSingleton (nonZeroDivisors A)
        ((algebraMap A K π) ^ (n + m))
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, ← zpow_add₀ hπK]
  have hlevel_mul (I J : chapterNonzeroFractionalIdealGroup (A := A) (K := K)) :
      level (I * J) = level I + level J := by
    have huniq := chapter_nonzero_fractional_ideal_unique_level
      (A := A) (K := K) π hπ (I * J).1 (I * J).2
    apply huniq.unique (hlevel (I * J))
    change I.1 * J.1 = (F (level I + level J)).1
    rw [hlevel I, hlevel J]
    exact congrArg Subtype.val (hFmul (level I) (level J))
  have hlevel_F (n : ℤ) : level (F n) = n := by
    have huniq := chapter_nonzero_fractional_ideal_unique_level
      (A := A) (K := K) π hπ (F n).1 (F n).2
    apply huniq.unique (hlevel (F n))
    rfl
  exact
    { toFun := level
      invFun := fun n => F (Multiplicative.toAdd n)
      left_inv := by
        intro I
        apply Subtype.ext
        exact (hlevel I).symm
      right_inv := by
        intro n
        apply congrArg Multiplicative.ofAdd
        exact hlevel_F (Multiplicative.toAdd n)
      map_mul' := by
        intro I J
        exact congrArg Multiplicative.ofAdd (hlevel_mul I J) }

include hπ in
/-- Book §5.3: the nonzero fractional ideals form an infinite cyclic group. -/
theorem chapter_nonzero_fractional_ideal_group_is_infinite_cyclic :
    IsCyclic (chapterNonzeroFractionalIdealGroup (A := A) (K := K)) ∧
      Infinite (chapterNonzeroFractionalIdealGroup (A := A) (K := K)) := by
  let e := chapterNonzeroFractionalIdealGroupEquivInt' (A := A) (K := K) π hπ
  exact ⟨e.isCyclic.mpr inferInstance,
    Infinite.of_injective e.symm e.symm.injective⟩

include hπ in
/-- Book §5.3: the fractional-ideal group is another copy of `ℤ`. -/
theorem chapter_nonzero_fractional_ideal_group_equiv_int :
    Nonempty (chapterNonzeroFractionalIdealGroup (A := A) (K := K) ≃* Multiplicative ℤ) := by
  exact ⟨chapterNonzeroFractionalIdealGroupEquivInt' (A := A) (K := K) π hπ⟩

include hπ in
/-- Book §5.3, displayed quotient assertion `Kˣ/Aˣ ≅ ℤ`. -/
noncomputable def chapter_field_unit_quotient_equiv_int :
    chapterFieldUnitQuotient (A := A) (K := K) ≃* Multiplicative ℤ := by
  classical
  have hπK : algebraMap A K π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply IsFractionRing.injective A K
    simpa using h
  let φ : Kˣ →* chapterNonzeroFractionalIdealGroup (A := A) (K := K) :=
    MonoidHom.mk' (fun x =>
      ⟨FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K),
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero⟩) (by
      intro x y
      apply Subtype.ext
      change FractionalIdeal.spanSingleton (nonZeroDivisors A) ((x * y : K)) =
        FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K) *
          FractionalIdeal.spanSingleton (nonZeroDivisors A) (y : K)
      simpa only [Units.val_mul] using
        (FractionalIdeal.spanSingleton_mul_spanSingleton
          (S := nonZeroDivisors A) (x : K) (y : K)).symm)
  have hφ_apply (x : Kˣ) :
      (φ x).1 = FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K) := by
    rfl
  have hker : chapterRingUnitImage (A := A) (K := K) = φ.ker := by
    ext x
    constructor
    · intro hx
      rcases (MonoidHom.mem_range).1 hx with ⟨u, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have hspan :
          FractionalIdeal.spanSingleton (nonZeroDivisors A)
              ((Units.map (algebraMap A K).toMonoidHom u : Kˣ) : K) =
            FractionalIdeal.spanSingleton (nonZeroDivisors A) (1 : K) := by
        apply (FractionalIdeal.spanSingleton_eq_spanSingleton).2
        refine ⟨u⁻¹, ?_⟩
        simp [Units.smul_def, Algebra.smul_def]
      rw [hφ_apply]
      change FractionalIdeal.spanSingleton (nonZeroDivisors A)
          ((Units.map (algebraMap A K).toMonoidHom u : Kˣ) : K) =
        (1 : FractionalIdeal (nonZeroDivisors A) K)
      simpa only [FractionalIdeal.spanSingleton_one] using hspan
    · intro hx
      have hφ : φ x =
          (1 : chapterNonzeroFractionalIdealGroup (A := A) (K := K)) :=
        MonoidHom.mem_ker.1 hx
      have hx' : FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K) =
          (1 : FractionalIdeal (nonZeroDivisors A) K) := by
        have hxval := congrArg Subtype.val hφ
        rw [hφ_apply] at hxval
        change FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K) =
          (1 : FractionalIdeal (nonZeroDivisors A) K) at hxval
        exact hxval
      have hx'' : FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : K) =
          FractionalIdeal.spanSingleton (nonZeroDivisors A) (1 : K) := by
        simpa using hx'
      obtain ⟨u, hu⟩ :=
        (FractionalIdeal.spanSingleton_eq_spanSingleton).1 hx''
      have hu' : (algebraMap A K (u : A)) * (x : K) = 1 := by
        simpa [Units.smul_def, Algebra.smul_def] using hu
      have hu'' : ((Units.map (algebraMap A K).toMonoidHom u : Kˣ) : K) *
          (x : K) = 1 := by
        simpa using hu'
      have hxinv : (x : K) =
          ((Units.map (algebraMap A K).toMonoidHom u)⁻¹ : K) := by
        simpa only [Units.val_inv_eq_inv_val] using
          (Units.eq_inv_of_mul_eq_one_left hu'')
      apply (MonoidHom.mem_range).2
      refine ⟨u⁻¹, ?_⟩
      apply Units.ext
      simpa using hxinv.symm
  have hφsurj : Function.Surjective φ := by
    intro I
    obtain ⟨n, hn, _⟩ :=
      chapter_nonzero_fractional_ideal_unique_level
        (A := A) (K := K) π hπ I.1 I.2
    let uπ : Kˣ := Units.mk0 (algebraMap A K π) hπK
    refine ⟨uπ ^ n, ?_⟩
    apply Subtype.ext
    change FractionalIdeal.spanSingleton (nonZeroDivisors A)
        ((uπ ^ n : Kˣ) : K) = I.1
    rw [Units.val_zpow_eq_zpow_val]
    change FractionalIdeal.spanSingleton (nonZeroDivisors A)
        ((algebraMap A K π) ^ n) = I.1
    simpa [chapterFractionalFiltration] using hn.symm
  exact
    (QuotientGroup.liftEquiv (N := chapterRingUnitImage (A := A) (K := K))
      hφsurj hker).trans
      (chapterNonzeroFractionalIdealGroupEquivInt' (A := A) (K := K) π hπ)

/-- A unit of the fraction field associated with a DVR integer unit. -/
def chapterMappedRingUnit (u : Aˣ) : Kˣ :=
  Units.map (algebraMap A K).toMonoidHom u

include hπ in
/-- The unit corresponding to the image of the chosen uniformizer in `K`. -/
noncomputable def chapterUniformizerUnit (hπ : Irreducible π) : Kˣ :=
  Units.mk0 (algebraMap A K π) (by
    intro h
    apply hπ.ne_zero
    apply IsFractionRing.injective A K
    simpa using h)

/-- A discrete integer-valued valuation interface on `Kˣ`, normalized by `π`. -/
structure ChapterIntegerValuation (π : A) (hπ : Irreducible π) where
  value : Kˣ → ℤ
  map_one' : value 1 = 0
  map_mul' : ∀ x y : Kˣ, value (x * y) = value x + value y
  uniformizer_value' :
    value (chapterUniformizerUnit (A := A) (K := K) π hπ) = 1
  ring_unit_value' : ∀ u : Aˣ,
    value (chapterMappedRingUnit (A := A) (K := K) u) = 0
  factorization' : ∀ x : Kˣ, ∃ u : Aˣ,
    x = chapterMappedRingUnit (A := A) (K := K) u *
      (chapterUniformizerUnit (A := A) (K := K) π hπ) ^ value x

/-- Coercion from the chapter valuation interface to its integer-valued function. -/
instance chapterIntegerValuation.coeFun :
    CoeFun (ChapterIntegerValuation (A := A) (K := K) π hπ)
      (fun _ => Kˣ → ℤ) :=
  ⟨fun v => v.value⟩

/-- The integer valuation of a nonzero field element. -/
def chapterValuationValue (v : ChapterIntegerValuation (A := A) (K := K) π hπ)
    (x : K) (hx : x ≠ 0) : ℤ :=
  v.value (Units.mk0 x hx)

/-- Book §5.3: the DVR supplies the normalized integer valuation interface. -/
theorem chapter_exists_integer_valuation :
    Nonempty (ChapterIntegerValuation (A := A) (K := K) π hπ) := by
  classical
  let v : IsDedekindDomain.HeightOneSpectrum A :=
    { asIdeal := IsLocalRing.maximalIdeal A
      isPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
      ne_bot := by
        rw [hπ.maximalIdeal_eq]
        exact fun h => hπ.ne_zero (Ideal.span_singleton_eq_bot.mp h) }
  let w : Valuation K ℤᵐ⁰ := v.valuation K
  have hπK : algebraMap A K π ≠ 0 := by
    simpa using hπ.ne_zero
  have hwπ : w (algebraMap A K π) = WithZero.exp (-1 : ℤ) := by
    dsimp [w]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      v.intValuation_singleton hπ.ne_zero
        hπ.maximalIdeal_eq]
    rfl
  let val : Kˣ → ℤ := fun x => -WithZero.log (w (x : K))
  have hval_one : val 1 = 0 := by
    simp [val, w]
  have hval_mul : ∀ x y : Kˣ, val (x * y) = val x + val y := by
    intro x y
    have hx : w (x : K) ≠ 0 := (Valuation.ne_zero_iff w).2 (Units.ne_zero x)
    have hy : w (y : K) ≠ 0 := (Valuation.ne_zero_iff w).2 (Units.ne_zero y)
    change -WithZero.log (w ((x : K) * (y : K))) =
      -WithZero.log (w (x : K)) - WithZero.log (w (y : K))
    rw [map_mul, WithZero.log_mul hx hy]
    abel
  have hval_uniformizer :
      val (chapterUniformizerUnit (A := A) (K := K) π hπ) = 1 := by
    change -WithZero.log (w (algebraMap A K π)) = 1
    rw [hwπ]
    simp
  have hval_ring_unit : ∀ u : Aˣ,
      val (chapterMappedRingUnit (A := A) (K := K) u) = 0 := by
    intro u
    change -WithZero.log (w (algebraMap A K (u : A))) = 0
    dsimp [w]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      v.intValuation_eq_one_iff.mpr]
    · simp
    · exact (IsLocalRing.notMem_maximalIdeal).2 u.isUnit
  refine ⟨
    { value := val
      map_one' := hval_one
      map_mul' := hval_mul
      uniformizer_value' := hval_uniformizer
      ring_unit_value' := hval_ring_unit
      factorization' := ?_ }⟩
  intro x
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      hπ (Units.ne_zero x)
  have hval_x : val x = n := by
    change -WithZero.log (w (x : K)) = n
    rw [hu, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀]
    have huval : w (algebraMap A K (u : A)) = 1 := by
      dsimp [w]
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        v.intValuation_eq_one_iff.mpr]
      exact (IsLocalRing.notMem_maximalIdeal).2 u.isUnit
    rw [huval, one_mul, hwπ, WithZero.log_zpow]
    simp
  refine ⟨u, ?_⟩
  apply Units.ext
  simpa [hval_x, chapterMappedRingUnit, chapterUniformizerUnit,
    Units.smul_def, Algebra.smul_def] using hu

/-- Book §5.3, displayed precision-shift formula. -/
theorem chapter_fractional_filtration_shift
    (v : ChapterIntegerValuation (A := A) (K := K) π hπ)
    (x : K) (hx : x ≠ 0) (n : ℤ) :
    chapterPrincipalFractionalIdeal (A := A) (K := K) x *
        chapterFractionalFiltration (A := A) (K := K) π n =
    chapterFractionalFiltration (A := A) (K := K) π
        (n + chapterValuationValue (A := A) (K := K) π hπ v x hx) := by
  obtain ⟨u, hu⟩ := v.factorization' (Units.mk0 x hx)
  have hx' : x =
      (chapterMappedRingUnit (A := A) (K := K) u : K) *
        (chapterUniformizerUnit (A := A) (K := K) π hπ : K) ^
          chapterValuationValue (A := A) (K := K) π hπ v x hx := by
    change (Units.mk0 x hx : K) = _
    simpa [chapterValuationValue] using congrArg Units.val hu
  rw [chapterPrincipalFractionalIdeal, chapterFractionalFiltration,
    FractionalIdeal.spanSingleton_mul_spanSingleton]
  apply (FractionalIdeal.spanSingleton_eq_spanSingleton).2
  refine ⟨u⁻¹, ?_⟩
  calc
    u⁻¹ • (x * (algebraMap A K π) ^ n) =
        u⁻¹ • (((chapterMappedRingUnit (A := A) (K := K) u : K) *
          (chapterUniformizerUnit (A := A) (K := K) π hπ : K) ^
            chapterValuationValue (A := A) (K := K) π hπ v x hx) *
          (algebraMap A K π) ^ n) := by
      exact congrArg (fun z : K => u⁻¹ • (z * (algebraMap A K π) ^ n)) hx'
    _ = (algebraMap A K π) ^
          (n + chapterValuationValue (A := A) (K := K) π hπ v x hx) := by
      simp only [Units.smul_def, Algebra.smul_def, chapterMappedRingUnit,
        chapterUniformizerUnit, Units.val_mk0]
      change (algebraMap A K (↑(u⁻¹) : A)) *
          ((algebraMap A K (↑u : A)) *
            (algebraMap A K π) ^
              chapterValuationValue (A := A) (K := K) π hπ v x hx *
            (algebraMap A K π) ^ n) = _
      calc
        (algebraMap A K (↑(u⁻¹) : A)) *
              ((algebraMap A K (↑u : A)) *
                (algebraMap A K π) ^
                  chapterValuationValue (A := A) (K := K) π hπ v x hx *
                (algebraMap A K π) ^ n) =
            ((algebraMap A K (↑(u⁻¹) : A)) *
              (algebraMap A K (↑u : A))) *
                (algebraMap A K π) ^
                  chapterValuationValue (A := A) (K := K) π hπ v x hx *
                (algebraMap A K π) ^ n := by ring
        _ = (algebraMap A K π) ^
              chapterValuationValue (A := A) (K := K) π hπ v x hx *
            (algebraMap A K π) ^ n := by
          rw [← (algebraMap A K).map_mul]
          simp
        _ = (algebraMap A K π) ^
              (n + chapterValuationValue (A := A) (K := K) π hπ v x hx) := by
          rw [← zpow_add₀ (by simpa using hπ.ne_zero)]
          congr 1
          ring

/-- Book §5.3: units have value zero. -/
theorem chapter_mapped_ring_unit_has_value_zero
    (v : ChapterIntegerValuation (A := A) (K := K) π hπ) (u : Aˣ) :
    chapterValuationValue (A := A) (K := K) π hπ v
        (chapterMappedRingUnit (A := A) (K := K) u : K)
        (Units.ne_zero _) = 0 := by
  have hu : Units.mk0 (chapterMappedRingUnit (A := A) (K := K) u : K)
      (Units.ne_zero _) = chapterMappedRingUnit (A := A) (K := K) u := by
    apply Units.ext
    rfl
  change v.value (Units.mk0 (chapterMappedRingUnit (A := A) (K := K) u : K)
    (Units.ne_zero _)) = 0
  simpa [hu] using v.ring_unit_value' u

/-- Book §5.3: multiplication by a unit preserves precision. -/
theorem chapter_unit_preserves_precision
    (u : Aˣ) (n : ℤ) :
    chapterPrincipalFractionalIdeal (A := A) (K := K)
        (chapterMappedRingUnit (A := A) (K := K) u : K) *
        chapterFractionalFiltration (A := A) (K := K) π n =
      chapterFractionalFiltration (A := A) (K := K) π n := by
  rw [chapterPrincipalFractionalIdeal, chapterFractionalFiltration,
    FractionalIdeal.spanSingleton_mul_spanSingleton]
  apply (FractionalIdeal.spanSingleton_eq_spanSingleton).2
  refine ⟨u⁻¹, ?_⟩
  simp [Units.smul_def, Algebra.smul_def, chapterMappedRingUnit]

/-- Book §5.3: a nonzero maximal-ideal element gains positive precision. -/
theorem chapter_maximalIdeal_element_gains_precision
    (v : ChapterIntegerValuation (A := A) (K := K) π hπ)
    {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A)
    (haK : algebraMap A K a ≠ 0) (n : ℤ) :
    0 < chapterValuationValue (A := A) (K := K) π hπ v
        (algebraMap A K a) haK ∧
      n < n + chapterValuationValue (A := A) (K := K) π hπ v
        (algebraMap A K a) haK ∧
      chapterPrincipalFractionalIdeal (A := A) (K := K) (algebraMap A K a) *
          chapterFractionalFiltration (A := A) (K := K) π n =
        chapterFractionalFiltration (A := A) (K := K) π
          (n + chapterValuationValue (A := A) (K := K) π hπ v
            (algebraMap A K a) haK) := by
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    simp at haK
  obtain ⟨m, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  have hval : chapterValuationValue (A := A) (K := K) π hπ v
        (algebraMap A K a) haK = m := by
    have hunit : Units.mk0 (algebraMap A K a) haK =
        chapterMappedRingUnit (A := A) (K := K) u *
          (chapterUniformizerUnit (A := A) (K := K) π hπ) ^ m := by
      apply Units.ext
      simpa [chapterMappedRingUnit, chapterUniformizerUnit,
        Units.smul_def, Algebra.smul_def] using congrArg (algebraMap A K) hu
    have hpowval : ∀ k : ℕ, v.value
        ((chapterUniformizerUnit (A := A) (K := K) π hπ) ^ k) = (k : ℤ) := by
      intro k
      induction k with
      | zero => simp [v.map_one']
      | succ k ih =>
          rw [pow_succ, v.map_mul', ih, v.uniformizer_value']
          simp
    unfold chapterValuationValue
    rw [hunit, v.map_mul', v.ring_unit_value', hpowval m]
    simp
  have hnotunit : ¬ IsUnit a := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using ha
  have hmpos : 0 < m := by
    have hmne : m ≠ 0 := by
      intro hm
      apply hnotunit
      rw [hu, hm, pow_zero, mul_one]
      exact u.isUnit
    omega
  refine ⟨by simpa [hval] using hmpos, by omega, ?_⟩
  exact chapter_fractional_filtration_shift (A := A) (K := K) π hπ v
    (algebraMap A K a) haK n

/-- Book §5.3: a negative-valued element loses digits. -/
theorem chapter_negative_valued_element_loses_precision
    (v : ChapterIntegerValuation (A := A) (K := K) π hπ)
    {x : K} (hx : x ≠ 0)
    (hv : chapterValuationValue (A := A) (K := K) π hπ v x hx < 0) (n : ℤ) :
    n + chapterValuationValue (A := A) (K := K) π hπ v x hx < n ∧
      chapterPrincipalFractionalIdeal (A := A) (K := K) x *
          chapterFractionalFiltration (A := A) (K := K) π n =
        chapterFractionalFiltration (A := A) (K := K) π
          (n + chapterValuationValue (A := A) (K := K) π hπ v x hx) := by
  refine ⟨by omega, ?_⟩
  exact chapter_fractional_filtration_shift (A := A) (K := K) π hπ v x hx n

end FractionalIdealsAndPrecision

section DedekindLocalizationProjection

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The global exponent vector of a fractional ideal. -/
def chapterGlobalIdealExponent (v : HeightOneSpectrum R)
    (I : FractionalIdeal (nonZeroDivisors R) K) : ℤ :=
  FractionalIdeal.count K v I

/-- The full global exponent vector `v ↦ val_v(I)`. -/
def chapterGlobalIdealExponentVector
    (I : FractionalIdeal (nonZeroDivisors R) K) : HeightOneSpectrum R → ℤ :=
  fun v => chapterGlobalIdealExponent (R := R) (K := K) v I

/-- Localization of an integral ideal at a height-one prime. -/
def chapterLocalizeIdealAtPrime (v : HeightOneSpectrum R) (I : Ideal R) :
    Ideal (Localization.AtPrime v.asIdeal) :=
  I.map (algebraMap R (Localization.AtPrime v.asIdeal))

/-- The local exponent of an ideal after localization at a height-one prime.

This is defined independently of the global exponent: it says that the
localized ideal is a power of the local maximal ideal and records that power
as an integer. -/
def chapterLocalizedIdealExponentAtPrime (v : HeightOneSpectrum R)
    (J : Ideal (Localization.AtPrime v.asIdeal)) (n : ℤ) : Prop :=
  ∃ m : ℕ, n = (m : ℤ) ∧
    J = IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^ m

/-- Book §5.3: localization at `𝔭` projects the global exponent vector to its `𝔭` coordinate. -/
theorem chapter_localization_projects_global_exponent
    (v : HeightOneSpectrum R) (I : Ideal R) (hI : I ≠ ⊥) :
    chapterLocalizedIdealExponentAtPrime (R := R) v
        (chapterLocalizeIdealAtPrime (R := R) v I)
        (chapterGlobalIdealExponentVector (R := R) (K := K)
          (I : FractionalIdeal (nonZeroDivisors R) K) v) := by
  classical
  have hv0 : v.asIdeal ≠ ⊥ := v.ne_bot
  let hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal hv0
  obtain ⟨J, hcop, hfactor⟩ :=
    Ideal.eq_prime_pow_mul_coprime (hpm := hvmax) hI v.asIdeal
  have hJnot : ¬ J ≤ v.asIdeal := by
    intro hJ
    have htop : v.asIdeal = ⊤ := by
      calc
        v.asIdeal = v.asIdeal ⊔ J := (sup_eq_left.mpr hJ).symm
        _ = ⊤ := hcop
    exact hvmax.ne_top htop
  have hcount :
      chapterGlobalIdealExponentVector (R := R) (K := K)
          (I : FractionalIdeal (nonZeroDivisors R) K) v =
        (Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors I) : ℤ) := by
    unfold chapterGlobalIdealExponentVector chapterGlobalIdealExponent
    rw [FractionalIdeal.count_coe K v hI,
      Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]
  have hlocal :
      chapterLocalizeIdealAtPrime (R := R) v I =
        IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^
          Multiset.count v.asIdeal
            (UniqueFactorizationMonoid.normalizedFactors I) := by
    let m : ℕ := Multiset.count v.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors I)
    have hmap :
        I.map (algebraMap R (Localization.AtPrime v.asIdeal)) =
          IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^ m := by
      rw [hfactor, Ideal.map_mul, Ideal.map_pow,
        IsLocalization.AtPrime.map_eq_top_of_not_le
          (S := Localization.AtPrime v.asIdeal) (p := v.asIdeal) hJnot,
        Ideal.mul_top, Localization.AtPrime.map_eq_maximalIdeal]
    simpa [chapterLocalizeIdealAtPrime, m] using hmap
  refine ⟨Multiset.count v.asIdeal
    (UniqueFactorizationMonoid.normalizedFactors I), hcount, ?_⟩
  exact hlocal

/-- The projection statement written directly as `val_𝔭(I)`. -/
theorem chapter_localization_exponent_is_p_coordinate
    (v : HeightOneSpectrum R)
    (I : FractionalIdeal (nonZeroDivisors R) K) :
    chapterGlobalIdealExponentVector (R := R) (K := K) I v =
      chapterGlobalIdealExponent (R := R) (K := K) v I := by
  rfl

end DedekindLocalizationProjection

section RamificationShift

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [CommRing S] [IsDomain S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S]

/-- Book §5.3: ramification index as the length of the localized quotient. -/
theorem chapter_ramification_index_length_formula
  (q : Ideal S) [q.IsPrime] :
    let Sq := Localization.AtPrime q;
      q.ramificationIdx R =
      (Module.length Sq
        (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat := by
  exact Ideal.ramificationIdx_def q R

/-- Book §5.3: the ramification index is the shift between the two local filtrations. -/
theorem chapter_ramification_index_is_filtration_shift
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [Module.IsTorsionFree R S]
    (hp : p ≠ ⊥) :
    let Sq := Localization.AtPrime q;
    p.map (algebraMap R Sq) =
        IsLocalRing.maximalIdeal Sq ^ q.ramificationIdx R ∧
      ∀ n : ℕ,
        p.map (algebraMap R Sq) * IsLocalRing.maximalIdeal Sq ^ n =
          IsLocalRing.maximalIdeal Sq ^ (n + q.ramificationIdx R) := by
  classical
  dsimp
  have hpS : p.map (algebraMap R S) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp
  have hq0 : q ≠ ⊥ :=
    ne_bot_of_le_ne_bot hpS
      (Ideal.map_le_of_le_comap (q.over_def p).le)
  let hqmax : q.IsMaximal := (inferInstance : q.IsPrime).isMaximal hq0
  obtain ⟨I, hqI, hfactor⟩ :=
    Ideal.eq_prime_pow_mul_coprime (hpm := hqmax) hpS q
  replace hqI : ¬ I ≤ q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact (inferInstance : q.IsPrime).ne_top
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    p q hpS] at hfactor
  have hmap : p.map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ q.ramificationIdx R := by
    apply_fun (Ideal.map (algebraMap S (Localization.AtPrime q))) at hfactor
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_mul, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_top_of_not_le
        (S := Localization.AtPrime q) (p := q) hqI, Ideal.mul_top,
      Localization.AtPrime.map_eq_maximalIdeal] at hfactor
    exact hfactor
  refine ⟨hmap, ?_⟩
  intro n
  rw [hmap, ← pow_add, add_comm]

end RamificationShift

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter05
