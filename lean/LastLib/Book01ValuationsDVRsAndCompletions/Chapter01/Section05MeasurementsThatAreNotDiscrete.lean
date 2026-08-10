import LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.Section04LocalizationsOfDedekindDomains

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter01

open scoped Polynomial RatFunc nonZeroDivisors
open Set Function Ideal
open scoped BigOperators

noncomputable section

/-! # Chapter 1: Measuring vanishing

This file is a statement-generation pass for Chapter 1 of *Valuations, DVRs, and
Completions*.  The declarations below follow Sections 1.1--1.5 in order. -/

/-! # Book 1, Chapter 1, Section 1.5: Measurements That Are Not Discrete
-/

/-! ## 1.5 Measurements that are not discrete -/

section PuiseuxValuation

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A denominator stage of the Puiseux tower is modeled by a Laurent series in
the variable `t^(1/n)`.  The stage embeddings, their nesting under divisibility,
and the valuation are packaged as an interface since Mathlib does not select
one concrete construction of the full Puiseux union. -/
structure PuiseuxValuationModel where
  stage : ∀ n : ℕ, 0 < n → LaurentSeries k →ₐ[k] K
  stage_injective : ∀ (n : ℕ) (hn : 0 < n), Function.Injective (stage n hn)
  stage_image_nested : ∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n), m ∣ n →
    ∀ f : LaurentSeries k, ∃ g : LaurentSeries k,
      stage n hn g = stage m hm f
  union : ∀ x : K, ∃ n : ℕ, ∃ hn : 0 < n, ∃ f : LaurentSeries k,
    stage n hn f = x
  valuation : AddValuation K (WithTop ℚ)
  stage_valuation : ∀ (n : ℕ) (hn : 0 < n) (f : LaurentSeries k), f ≠ 0 →
    valuation (stage n hn f) =
      (((f.order : ℚ) / (n : ℚ)) : WithTop ℚ)

/-- The lowest exponent in the `n`th stage lies in `(1/n)ℤ`. -/
def puiseuxStageExponent (n : ℕ) (hn : 0 < n) (f : LaurentSeries k) : ℚ :=
  (f.order : ℚ) / (n : ℚ)

/-- The `n`th Laurent-series stage has exponents in `1/n · ℤ`. -/
theorem puiseuxStageExponent_mem_one_div_n_z {n : ℕ} (hn : 0 < n)
    (f : LaurentSeries k) :
    puiseuxStageExponent n hn f ∈ Set.range (fun z : ℤ => (z : ℚ) / (n : ℚ)) := by
  exact ⟨f.order, rfl⟩

/-- Every rational exponent is realized by a nonzero single-term Laurent
series in a suitable stage. -/
theorem puiseuxStageExponent_surjective (q : ℚ) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ f : LaurentSeries k, f ≠ 0 ∧
      ((f.order : ℚ) / (n : ℚ)) = q := by
  let f : LaurentSeries k := HahnSeries.single q.num (1 : k)
  refine ⟨q.den, q.den_pos, f, ?_, ?_⟩
  · dsimp [f]
    exact HahnSeries.single_ne_zero one_ne_zero
  · dsimp [f]
    rw [HahnSeries.order_single one_ne_zero]
    exact q.num_div_den

/-- The valuation is well-defined on overlaps of the stages. -/
theorem puiseux_overlap_valuation_well_defined (M : PuiseuxValuationModel (k := k) (K := K))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {f g : LaurentSeries k}
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : M.stage m hm f = M.stage n hn g) :
    puiseuxStageExponent m hm f = puiseuxStageExponent n hn g := by
  change ((f.order : ℚ) / (m : ℚ)) = ((g.order : ℚ) / (n : ℚ))
  have hval := congrArg M.valuation hfg
  rw [M.stage_valuation m hm f hf, M.stage_valuation n hn g hg] at hval
  exact WithTop.coe_eq_coe.mp hval

/-- The value group of the Puiseux valuation is represented by the rationals. -/
def puiseuxValueSet (M : PuiseuxValuationModel (k := k) (K := K)) : Set ℚ :=
  {q | ∃ x : K, x ≠ 0 ∧ M.valuation x = (q : WithTop ℚ)}

/-- Every rational value occurs in the Puiseux tower. -/
theorem puiseuxValueSet_eq_univ (M : PuiseuxValuationModel (k := k) (K := K)) :
    puiseuxValueSet M = Set.univ := by
  ext q
  constructor
  · intro _
    exact Set.mem_univ q
  · intro _
    obtain ⟨n, hn, f, hf, hq⟩ := puiseuxStageExponent_surjective (k := k) q
    refine ⟨M.stage n hn f, ?_, ?_⟩
    · intro hzero
      apply hf
      apply M.stage_injective n hn
      simpa using hzero
    · simpa [M.stage_valuation n hn f hf] using hq

/-- Rank one is expressed here by the Archimedean ordering property. -/
def IsChapterRankOneOrderedGroup (Γ : Type*) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] : Prop :=
  ∀ a b : Γ, 0 < a → 0 < b → ∃ n : ℕ, a ≤ n • b

/-- Discreteness means that the positive cone has a least element. -/
def IsChapterDiscreteOrderedGroup (Γ : Type*) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] : Prop :=
  ∃ γ : Γ, 0 < γ ∧ ∀ δ : Γ, 0 < δ → γ ≤ δ

/-- The ordered group of rational values has rank one. -/
theorem rational_value_group_is_rank_one :
    IsChapterRankOneOrderedGroup ℚ := by
  intro a b ha hb
  obtain ⟨n, hn⟩ := exists_nat_ge (a / b)
  refine ⟨n, ?_⟩
  norm_num [nsmul_eq_mul]
  exact (div_le_iff₀ hb).mp hn

/-- The rational value group has no least positive element. -/
theorem rational_value_group_has_no_least_positive :
    ¬IsChapterDiscreteOrderedGroup ℚ := by
  rintro ⟨q, hq, hleast⟩
  let r : ℚ := q / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hrq : r < q := by
    dsimp [r]
    linarith
  exact (not_lt_of_ge (hleast r hr)) hrq

/-- Explicitly, every positive rational has a smaller positive rational. -/
theorem exists_smaller_positive_rational {q : ℚ} (hq : 0 < q) :
    ∃ r : ℚ, 0 < r ∧ r < q := by
  refine ⟨q / 2, by linarith, by linarith⟩

/-- The Puiseux valuation ring is the ring of nonnegative-valued elements. -/
def puiseuxValuationRing (M : PuiseuxValuationModel (k := k) (K := K)) :
    ValuationSubring K :=
  M.valuation.toValuation.valuationSubring

/-- The maximal ideal of the Puiseux valuation ring. -/
def puiseuxMaximalIdeal (M : PuiseuxValuationModel (k := k) (K := K)) :
    Ideal (puiseuxValuationRing M) :=
  IsLocalRing.maximalIdeal (puiseuxValuationRing M)

/-- Nonnegative additive valuation is equivalent to membership in the valuation
subring. -/
theorem puiseux_mem_valuationRing_iff {M : PuiseuxValuationModel (k := k) (K := K)}
    (x : K) :
    x ∈ puiseuxValuationRing M ↔ (0 : WithTop ℚ) ≤ M.valuation x := by
  change M.valuation.toValuation x ≤ 1 ↔ _
  change OrderDual.toDual (M.valuation x) ≤
    OrderDual.toDual (0 : WithTop ℚ) ↔ _
  exact OrderDual.toDual_le_toDual

/-- Positive-valued elements are exactly the maximal ideal of the Puiseux ring. -/
theorem puiseux_mem_maximalIdeal_iff_positive
    (M : PuiseuxValuationModel (k := k) (K := K))
    (x : puiseuxValuationRing M) :
    x ∈ puiseuxMaximalIdeal M ↔
      (0 : WithTop ℚ) < M.valuation (x : K) := by
  change x ∈ IsLocalRing.maximalIdeal (puiseuxValuationRing M) ↔ _
  rw [ValuationSubring.valuation_lt_one_iff]
  calc
    (puiseuxValuationRing M).valuation (x : K) < 1 ↔
        M.valuation.toValuation (x : K) < 1 :=
      (Valuation.isEquiv_valuation_valuationSubring
        M.valuation.toValuation).lt_one_iff_lt_one.symm
    _ ↔ (0 : WithTop ℚ) < M.valuation (x : K) := by
      change OrderDual.toDual (M.valuation (x : K)) <
        OrderDual.toDual (0 : WithTop ℚ) ↔ _
      exact OrderDual.toDual_lt_toDual

/-- Given a positive value, a smaller positive rational value is realized by an
element of the tower. -/
theorem puiseux_exists_strictly_smaller_positive_element
    (M : PuiseuxValuationModel (k := k) (K := K))
    {a : puiseuxValuationRing M}
    (ha : (0 : WithTop ℚ) < M.valuation (a : K)) :
    ∃ b : puiseuxValuationRing M,
      (0 : WithTop ℚ) < M.valuation (b : K) ∧
        M.valuation (b : K) < M.valuation (a : K) := by
  by_cases htop : M.valuation (a : K) = ⊤
  · obtain ⟨n, hn, f, hf, hq⟩ := puiseuxStageExponent_surjective (k := k) 1
    have hval : M.valuation (M.stage n hn f) = (1 : WithTop ℚ) := by
      rw [M.stage_valuation n hn f hf]
      simpa using hq
    have hmem : M.stage n hn f ∈ puiseuxValuationRing M :=
      (puiseux_mem_valuationRing_iff (M := M) _).2 (by
        rw [hval]
        norm_num)
    refine ⟨⟨M.stage n hn f, hmem⟩, ?_, ?_⟩
    · rw [hval]
      norm_num
    · rw [hval, htop]
      exact WithTop.coe_lt_top (1 : ℚ)
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp htop
    have hqpos : 0 < q := by
      apply WithTop.coe_lt_coe.mp
      simpa [hq] using ha
    obtain ⟨r, hr, hrq⟩ := exists_smaller_positive_rational hqpos
    obtain ⟨n, hn, f, hf, hrf⟩ := puiseuxStageExponent_surjective (k := k) r
    have hval : M.valuation (M.stage n hn f) = (r : WithTop ℚ) := by
      rw [M.stage_valuation n hn f hf]
      simpa using hrf
    have hmem : M.stage n hn f ∈ puiseuxValuationRing M :=
      (puiseux_mem_valuationRing_iff (M := M) _).2 (by
        rw [hval]
        exact WithTop.coe_nonneg.mpr (le_of_lt hr))
    refine ⟨⟨M.stage n hn f, hmem⟩, ?_, ?_⟩
    · rw [hval]
      exact WithTop.coe_pos.mpr hr
    · rw [hval, ← hq]
      exact WithTop.coe_lt_coe.mpr hrq

/-- The strict-divisibility phenomenon behind the nonprincipal maximal ideal:
for a positive-valued `a`, a smaller positive-valued `b` satisfies
`a ∈ (b)` but `b ∉ (a)`. -/
theorem puiseux_strict_divisibility_in_maximalIdeal
    (M : PuiseuxValuationModel (k := k) (K := K))
    {a : puiseuxValuationRing M}
    (ha : (0 : WithTop ℚ) < M.valuation (a : K)) :
    ∃ b : puiseuxValuationRing M,
      (0 : WithTop ℚ) < M.valuation (b : K) ∧
        M.valuation (b : K) < M.valuation (a : K) ∧
        a ∈ Ideal.span ({b} : Set (puiseuxValuationRing M)) ∧
        b ∉ Ideal.span ({a} : Set (puiseuxValuationRing M)) := by
  obtain ⟨b, hbpos, hba⟩ := puiseux_exists_strictly_smaller_positive_element M ha
  have hvle : (puiseuxValuationRing M).valuation (a : K) ≤
      (puiseuxValuationRing M).valuation (b : K) := by
    have hmul : M.valuation.toValuation (a : K) ≤
        M.valuation.toValuation (b : K) := by
      change Multiplicative.ofAdd (OrderDual.toDual (M.valuation (a : K))) ≤
        Multiplicative.ofAdd (OrderDual.toDual (M.valuation (b : K)))
      simpa only [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual] using hba.le
    exact (Valuation.isEquiv_valuation_valuationSubring
      M.valuation.toValuation).le_iff_le.mp hmul
  obtain ⟨c, hc⟩ := (puiseuxValuationRing M).valuation_le_iff (a : K) (b : K) |>.1 hvle
  have hamem : a ∈ Ideal.span ({b} : Set (puiseuxValuationRing M)) := by
    apply Ideal.mem_span_singleton'.2
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hc
  refine ⟨b, hbpos, hba, hamem, ?_⟩
  intro hbmem
  obtain ⟨c, hcb⟩ := Ideal.mem_span_singleton'.1 hbmem
  have hcpos : (0 : WithTop ℚ) ≤ M.valuation (c : K) :=
    (puiseux_mem_valuationRing_iff (M := M) _).1 c.property
  have hval : M.valuation (b : K) =
      M.valuation (c : K) + M.valuation (a : K) := by
    have hcb' : (c : K) * (a : K) = (b : K) := congrArg Subtype.val hcb
    calc
      M.valuation (b : K) = M.valuation ((c : K) * (a : K)) := by rw [hcb']
      _ = M.valuation (c : K) + M.valuation (a : K) := M.valuation.map_mul _ _
  have havb : M.valuation (a : K) ≤ M.valuation (b : K) := by
    calc
      M.valuation (a : K) = 0 + M.valuation (a : K) := by simp
      _ ≤ M.valuation (c : K) + M.valuation (a : K) :=
        add_le_add_left hcpos (M.valuation (a : K))
      _ = M.valuation (b : K) := hval.symm
  exact (not_lt_of_ge havb) hba

/-- The positive maximal ideal is not generated by one element. -/
theorem puiseux_maximalIdeal_not_principal
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ¬∃ π : puiseuxValuationRing M,
      puiseuxMaximalIdeal M = Ideal.span ({π} : Set (puiseuxValuationRing M)) := by
  rintro ⟨π, hπ⟩
  have hπmem : π ∈ puiseuxMaximalIdeal M := by
    rw [hπ]
    exact Ideal.mem_span_singleton_self π
  have hπpos : (0 : WithTop ℚ) < M.valuation (π : K) :=
    (puiseux_mem_maximalIdeal_iff_positive M π).1 hπmem
  obtain ⟨b, hbpos, _, _, hbnot⟩ :=
    puiseux_strict_divisibility_in_maximalIdeal M hπpos
  have hbmem : b ∈ puiseuxMaximalIdeal M :=
    (puiseux_mem_maximalIdeal_iff_positive M b).2 hbpos
  exact hbnot (hπ ▸ hbmem)

/-- The Puiseux valuation ring is nevertheless a valuation ring. -/
theorem puiseux_valuationRing_is_valuationRing
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ValuationRing (puiseuxValuationRing M) := by
  exact inferInstance

/-- The Puiseux valuation ring is not a discrete valuation ring. -/
theorem puiseux_valuationRing_not_discrete_valuation_ring
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ¬IsDiscreteValuationRing (puiseuxValuationRing M) := by
  intro hD
  letI : IsDiscreteValuationRing (puiseuxValuationRing M) := hD
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (puiseuxValuationRing M)
  apply puiseux_maximalIdeal_not_principal M
  exact ⟨π, hπ.maximalIdeal_eq⟩

/-- The same strict chain prevents the Puiseux valuation ring from being
Noetherian. -/
theorem puiseux_valuationRing_not_noetherian
    (M : PuiseuxValuationModel (k := k) (K := K)) :
    ¬IsNoetherianRing (puiseuxValuationRing M) := by
  intro hN
  letI : IsNoetherianRing (puiseuxValuationRing M) := hN
  letI : IsPrincipalIdealRing (puiseuxValuationRing M) :=
    ((IsBezout.TFAE (R := puiseuxValuationRing M)).out 0 1).mp hN
  obtain ⟨π, hπ⟩ := IsPrincipalIdealRing.principal (puiseuxMaximalIdeal M)
  exact puiseux_maximalIdeal_not_principal M ⟨π, hπ⟩

/-- Rank one and discreteness are different properties: the Puiseux value group
is Archimedean but has no least positive value. -/
theorem puiseux_rank_one_but_not_discrete :
    IsChapterRankOneOrderedGroup ℚ ∧
      ¬IsChapterDiscreteOrderedGroup ℚ := by
  exact ⟨rational_value_group_is_rank_one,
    rational_value_group_has_no_least_positive⟩

end PuiseuxValuation

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter01
