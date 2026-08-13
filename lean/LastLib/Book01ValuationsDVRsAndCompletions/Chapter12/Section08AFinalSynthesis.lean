import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section05UniqueExtensionAndHenselianity
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

noncomputable section

open Function Ideal IsLocalRing Polynomial
open Filter Topology
open scoped BigOperators TensorProduct WithZero Polynomial

universe u

/-! # Chapter 12: Completion and finite extensions

This file is a statement-generation pass for §§12.1--12.8 of Book 1.  The
declarations deliberately record the interfaces and relationships used in the
chapter; proofs are postponed.
-/

/-! # Book 1, Chapter 12, Section 12.8: A Final Synthesis
-/

/-! ## 12.8. Synthesis and the final degree formula -/

/-- Total divisibility is the intrinsic characterization of a valuation ring. -/
theorem valuation_ring_total_divisibility_characterization
    {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] :
    ValuationRing A ↔ @Std.Total A (· ∣ ·) := by
  exact ValuationRing.iff_dvd_total (R := A)

/-- The finite-precision quotients of a DVR. -/
abbrev dvrPrecisionQuotient
    (A : Type*) [CommRing A] [IsLocalRing A]
    (n : ℕ) : Type _ :=
  A ⧸ (IsLocalRing.maximalIdeal A) ^ n

/-- Length recovers the order of a finite-precision DVR quotient. -/
theorem dvr_precision_length_recovers_order
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (n : ℕ) :
    Module.length A (dvrPrecisionQuotient A (n + 1)) = n + 1 := by
  simpa [dvrPrecisionQuotient] using
    (IsDiscreteValuationRing.length_quotient_pow_maximalIdeal A (n + 1))

/-- “Terms vanish” as a topological formulation of convergence of a series. -/
def termsVanishAtInfinity {K : Type*} [TopologicalSpace K] [Zero K]
    (u : ℕ → K) : Prop :=
  Filter.Tendsto u Filter.atTop (𝓝 0)

def seriesConverges {K : Type*} [TopologicalSpace K] [AddCommMonoid K]
    (u : ℕ → K) : Prop :=
  Summable u

/-- Complete nonarchimedean fields satisfy the series criterion. -/
theorem complete_nonarchimedean_series_criterion
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [Valued K Γ] [CompleteSpace K] [NonarchimedeanAddGroup K] :
    ∀ u : ℕ → K, seriesConverges u ↔ termsVanishAtInfinity u := by
  intro u
  change Summable u ↔ Filter.Tendsto u Filter.atTop (𝓝 0)
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  simp only [Nat.cofinite_eq_atTop]

/-- One Newton correction, used in the henselian/completion bridge. -/
def newtonStep {K : Type*} [Field K] (f : K[X]) (x : K) : K :=
  x - f.eval x / f.derivative.eval x

/-- Newton's step can be formed in a ring once the derivative unit is named. -/
def newtonStepInRing {A : Type*} [CommRing A] (f : A[X]) (x : A) (u : Aˣ) : A :=
  x - f.eval x * (↑(u⁻¹) : A)

/-- Newton corrections improve the precision quadratically under the simple-root hypotheses. -/
theorem newton_step_accelerates_precision
    {A : Type*} [CommRing A]
    (I : Ideal A) (f : A[X]) (x : A) (u : Aˣ) (n : ℕ)
    (hderivative : (u : A) = f.derivative.eval x)
    (hresidual : f.eval x ∈ I ^ n) :
    f.eval (newtonStepInRing f x u) ∈ I ^ (2 * n) := by
  let y : A := -(f.eval x * (↑(u⁻¹) : A))
  have hy : y ∈ I ^ n := by
    dsimp [y]
    rw [Ideal.neg_mem_iff]
    simpa [mul_comm] using (I ^ n).mul_mem_left (↑(u⁻¹) : A) hresidual
  have hy2 : y ^ 2 ∈ I ^ (2 * n) := by
    rw [show 2 * n = n + n by omega, pow_add]
    simpa [pow_two] using (Ideal.mul_mem_mul hy hy)
  have hlin : f.derivative.eval x * y + f.eval x = 0 := by
    dsimp [y]
    rw [← hderivative]
    calc
      ↑u * -(f.eval x * (↑(u⁻¹) : A)) + f.eval x =
          -(f.eval x * (↑u * (↑(u⁻¹) : A))) + f.eval x := by ring
      _ = 0 := by simp
  obtain ⟨c, hc⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add f x y
  have hxy : x + y = newtonStepInRing f x u := by
    simp [newtonStepInRing, y, sub_eq_add_neg]
  rw [← hxy, ← hc]
  rw [show c * y ^ 2 + f.derivative.eval x * y + f.eval x =
      c * y ^ 2 + (f.derivative.eval x * y + f.eval x) by ring]
  rw [hlin, add_zero]
  exact (I ^ (2 * n)).mul_mem_left c hy2

/-- The field-valued Newton definition satisfies its elementary cancellation identity. -/
theorem newton_step_identity
    {K : Type*} [Field K] (f : K[X]) (x : K)
    (hderivative : f.derivative.eval x ≠ 0) :
    newtonStep f x * f.derivative.eval x =
      x * f.derivative.eval x - f.eval x := by
  unfold newtonStep
  rw [sub_mul, div_mul_cancel₀ _ hderivative]

/-- Fundamental equality in the finite flat algebra formulation. -/
theorem final_sum_ramification_times_residue_degree
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsDomain R]
    [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S,
        q.1.ramificationIdx R * q.1.inertiaDeg R = Module.finrank R S := by
  exact Ideal.sum_ramification_inertia_eq_finrank p S

/-- The fraction-field reading of the same equality is `∑ e f = [L : K]`. -/
theorem final_fraction_field_degree_formula
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsDomain R]
    [Algebra (FractionRing R) (FractionRing S)]
    [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)]
    (hfrac : Module.finrank R S =
      Module.finrank (FractionRing R) (FractionRing S)) :
    ∑ q : p.primesOver S,
        q.1.ramificationIdx R * q.1.inertiaDeg R =
      Module.finrank (FractionRing R) (FractionRing S) := by
  calc
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R =
        Module.finrank R S := Ideal.sum_ramification_inertia_eq_finrank p S
    _ = Module.finrank (FractionRing R) (FractionRing S) := hfrac

/-- A factorization-henselian base has one valuation branch in an algebraic extension.
Completeness enters through `complete_nonarchimedean_field_is_henselian`, so
this synthesis theorem does not repeat a topology-to-algebra conversion. -/
theorem complete_or_henselian_base_has_one_branch
    {K Γ E : Type u} [Field K] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K E]
    (v : Valuation K Γ)
    [Algebra.IsAlgebraic K E]
    (hbase : Chapter09.HenselianFactorizationProperty v.valuationSubring) :
    ∃ W : HeterogeneousValuationExtension v E,
      ∀ W' : HeterogeneousValuationExtension v E,
        (letI : LinearOrderedCommGroupWithZero W.valueGroup := W.orderedValueGroup
         letI : LinearOrderedCommGroupWithZero W'.valueGroup := W'.orderedValueGroup
        W'.valuation.IsEquiv W.valuation) := by
  have hUnique : hasUniqueExtensionToEveryAlgebraicField v :=
    ((henselian_uniqueness_criterion v).out 0 1).mp hbase
  have hunique : hasUniqueValuationExtension v E := hUnique E
  rcases hunique with ⟨⟨W⟩, hW⟩
  refine ⟨W, ?_⟩
  intro W'
  exact hW W' W

/-- Concrete data for the final local arithmetic dictionary. -/
structure Chapter12LocalArithmeticDictionary
    {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [IsLocalRing A] [Algebra A K] [Algebra A B] [Algebra A L]
    [Algebra K L] [Algebra B L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (P : Ideal B) [P.IsPrime]
    (v : Valuation K ℤᵐ⁰) (w : Valuation L ℤᵐ⁰) where
  baseMaximalIdeal : Ideal A
  baseMaximalIdeal_eq : baseMaximalIdeal = IsLocalRing.maximalIdeal A
  extension : v.IsEquiv (w.comap (algebraMap K L))
  prime_isMaximal : P.IsMaximal
  branch_liesOver : P.LiesOver (IsLocalRing.maximalIdeal A)
  center : ∀ x : B, x ∈ P ↔ w (algebraMap B L x) < 1
  localizationMap : B →+* branchLocalization B P
  completionMap : branchLocalization B P →+* branchCompletion B P
  fractionFieldMap : branchCompletion B P →+* branchFractionField B P

/-- The final dictionary links valuation, ring, residue, precision, completion, and branches. -/
theorem local_arithmetic_dictionary
    {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [IsLocalRing A] [Algebra A K] [Algebra A B] [Algebra A L]
    [Algebra K L] [Algebra B L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (P : Ideal B) [P.IsPrime]
    (v : Valuation K ℤᵐ⁰) (w : Valuation L ℤᵐ⁰)
    (hext : v.IsEquiv (w.comap (algebraMap K L)))
    (hP : P.IsMaximal)
    (hP_liesOver : P.LiesOver (IsLocalRing.maximalIdeal A))
    (hcenter : ∀ x : B, x ∈ P ↔ w (algebraMap B L x) < 1) :
    Nonempty (Chapter12LocalArithmeticDictionary (A := A) (K := K) (B := B) (L := L) P v w) := by
  refine ⟨{
    baseMaximalIdeal := IsLocalRing.maximalIdeal A
    baseMaximalIdeal_eq := rfl
    extension := hext
    prime_isMaximal := hP
    branch_liesOver := hP_liesOver
    center := hcenter
    localizationMap := algebraMap B (branchLocalization B P)
    completionMap := algebraMap (branchLocalization B P) (branchCompletion B P)
    fractionFieldMap := algebraMap (branchCompletion B P) (branchFractionField B P)
  }⟩

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
