import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter05

open scoped BigOperators DirectSum nonZeroDivisors WithZero

noncomputable section

/-!
# Chapter 5: The valuation filtration

This file is a statement-generation pass for Chapter 5 of *Valuations, DVRs, and
Completions*.  The declarations are deliberately self-contained: the DVR and
local-ring notions used below are Mathlib notions, while the few constructions
which are not exposed by Mathlib are recorded as chapter-local interfaces.
-/

/-! # Book 1, Chapter 5, Section 5.1: Successive Precision
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
    Ideal.quotEquivOfEq (show IsLocalRing.maximalIdeal A ^ 1 =
      IsLocalRing.maximalIdeal A by simp) (chapterReduction A 1 x) =
      chapterLeadingDigit A x := by
  simp [chapterReduction, chapterLeadingDigit]
  exact (IsLocalRing.residue_def x).symm

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

omit [IsDiscreteValuationRing A] in
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
theorem chapter_length_principal_quotient {x : A} (_hx : x ≠ 0) :
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

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter05
