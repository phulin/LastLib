import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators

/-! ## 10.9. Unit coordinates and their limitations -/

/-- A choice of representatives for the residue field, with zero represented by zero. -/
def Chapter10ResidueRepresentativeSection
    {L : Type*} [Field L] (A : ValuationSubring L) : Prop :=
  ∃ s : Chapter10ResidueField A → A,
    s 0 = 0 ∧ Function.RightInverse (IsLocalRing.residue A) s

/-- A chosen uniformizer and residue representatives, kept explicit because coordinates depend on them. -/
structure Chapter10UnitCoordinateChoice
    {L : Type*} [Field L] (A : ValuationSubring L) where
  representatives : Chapter10ResidueField A → A
  representatives_zero : representatives 0 = 0
  representatives_rightInverse :
    Function.RightInverse (IsLocalRing.residue A) representatives
  uniformizer : A
  uniformizer_spec : Chapter10Uniformizer A uniformizer

/-- A unit expansion from a fixed base lift through successive correction layers. -/
def Chapter10HasSuccessiveUnitExpansion
    {L : Type*} [Field L] (A : ValuationSubring L) [TopologicalSpace Aˣ]
    (s₀ u : Aˣ) : Prop :=
  chapter10UnitReduction A s₀ = chapter10UnitReduction A u ∧
    ∃ c : ℕ → Aˣ, Chapter10SuccessiveUnitCorrectionProduct A u s₀ c

/-- Every unit admits a successive-correction expansion from any base lift with
the same residue. -/
theorem chapter10_units_have_successive_correction_expansions
    {L : Type*} [Field L] (A : ValuationSubring L)
    [UniformSpace Aˣ] [IsTopologicalGroup Aˣ] [CompleteSpace Aˣ]
    [T2Space Aˣ]
    (_hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (_hDVR : IsDiscreteValuationRing A)
    (_htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10UnitFiltration A)) :
    ∀ (u s₀ : Aˣ),
      chapter10UnitReduction A s₀ = chapter10UnitReduction A u →
      Chapter10HasSuccessiveUnitExpansion A s₀ u := by
  intro u s₀ hred
  let d : Aˣ := s₀⁻¹ * u
  have hd : d ∈ chapter10UnitFiltration A 1 := by
    change ((d : Aˣ) : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1
    rw [pow_one, ← IsLocalRing.residue_eq_zero_iff]
    have hunit : chapter10UnitReduction A d = 1 := by
      dsimp [d]
      rw [map_mul, map_inv, hred]
      simp
    have hval := congrArg Units.val hunit
    simpa [chapter10UnitReduction, map_sub] using sub_eq_zero.mpr hval
  let c : ℕ → Aˣ := fun n => if n = 0 then d else 1
  have hc : ∀ n, c n ∈ chapter10UnitFiltration A (n + 1) := by
    intro n
    by_cases hn : n = 0
    · simpa [c, hn] using hd
    · simp [c, hn]
  have hprod (N : ℕ) :
      Finset.prod (Finset.range N) c = if N = 0 then 1 else d := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.prod_range_succ]
      by_cases hN : N = 0
      · subst N
        simp
      · simp [hN]
  refine ⟨hred, ⟨c, hc, ?_, ?_⟩⟩
  · intro N
    rw [hprod]
    by_cases hN : N = 0
    · subst N
      simpa [d, mul_comm] using hd
    · have hcancel : u * (s₀ * d)⁻¹ = 1 := by
        simp [d, mul_comm, mul_left_comm]
      rw [if_neg hN, hcancel]
      exact (chapter10UnitFiltration A (N + 1)).one_mem
  · refine Filter.Tendsto.congr' ?_
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => u) Filter.atTop (nhds u))
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
    rw [hprod, if_neg (Nat.ne_of_gt hN)]
    simp [d, mul_comm, mul_left_comm]

/-- The coefficientwise logarithm terms `(-1)ⁿ xⁿ⁺¹/(n+1)`. -/
def chapter10LogTerm {L : Type*} [Field L] (x : L) (n : ℕ) : L :=
  (-1 : L) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : L)

/-- The coefficientwise exponential terms `xⁿ/n!`. -/
def chapter10ExpTerm {L : Type*} [Field L] (x : L) (n : ℕ) : L :=
  x ^ n / ((Nat.factorial n : ℕ) : L)

/-- Convergence predicates for the two formal series. -/
def Chapter10LogSeriesConverges {L : Type*} [Field L] [TopologicalSpace L]
    (x : L) : Prop := Summable (chapter10LogTerm x)

def Chapter10ExpSeriesConverges {L : Type*} [Field L] [TopologicalSpace L]
    (x : L) : Prop := Summable (chapter10ExpTerm x)

/-- The abstract group equivalence supplied by convergent logarithm and exponential series. -/
structure Chapter10LogExpLinearization
    {L : Type*} [Field L] [TopologicalSpace L]
    (U : Subgroup Lˣ) (I : AddSubgroup L) where
  log : Additive U →+ I
  exp : Multiplicative I →* U
  log_converges : ∀ u : U,
    Chapter10LogSeriesConverges (((u : Lˣ) : L) - 1)
  exp_converges : ∀ x : I,
    Chapter10ExpSeriesConverges (x : L)
  log_eq_series : ∀ u : U,
    ((log (Additive.ofMul u) : I) : L) =
      ∑' n, chapter10LogTerm (((u : Lˣ) : L) - 1) n
  exp_eq_series : ∀ x : I,
    (((exp (Multiplicative.ofAdd x) : U) : Lˣ) : L) =
      ∑' n, chapter10ExpTerm (x : L) n
  exp_log : ∀ u, exp (Multiplicative.ofAdd (log (Additive.ofMul u))) = u
  log_exp : ∀ x, log (Additive.ofMul (exp (Multiplicative.ofAdd x))) = x

/-- Deep enough principal units provide a log/exp identification once convergence is established. -/
theorem chapter10_deep_principal_units_log_exp
    {L : Type*} [Field L] [TopologicalSpace L]
    (U : Subgroup Lˣ) (I : AddSubgroup L)
    (hseries : ∃ log : Additive U →+ I, ∃ exp : Multiplicative I →* U,
      (∀ u : U, Chapter10LogSeriesConverges (((u : Lˣ) : L) - 1)) ∧
        (∀ x : I, Chapter10ExpSeriesConverges (x : L)) ∧
        (∀ u : U, ((log (Additive.ofMul u) : I) : L) =
          ∑' n, chapter10LogTerm (((u : Lˣ) : L) - 1) n) ∧
        (∀ x : I, (((exp (Multiplicative.ofAdd x) : U) : Lˣ) : L) =
          ∑' n, chapter10ExpTerm (x : L) n) ∧
        (∀ u, exp (Multiplicative.ofAdd (log (Additive.ofMul u))) = u) ∧
        (∀ x, log (Additive.ofMul (exp (Multiplicative.ofAdd x))) = x)) :
    Nonempty (Chapter10LogExpLinearization U I) := by
  rcases hseries with
    ⟨log, exp, hlog_converges, hexp_converges, hlog_eq_series,
      hexp_eq_series, hexp_log, hlog_exp⟩
  exact ⟨{
    log := log
    exp := exp
    log_converges := hlog_converges
    exp_converges := hexp_converges
    log_eq_series := hlog_eq_series
    exp_eq_series := hexp_eq_series
    exp_log := hexp_log
    log_exp := hlog_exp }⟩

/-- The characteristic-free linear part is already the map `1+x ↦ x` on each layer. -/
theorem chapter10_first_order_principal_unit_linearization
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n) :
    Nonempty
      (Multiplicative
          (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) ≃*
        Chapter10UnitLayerQuotient A n) :=
  chapter10_higher_unit_layer_is_additive A n hn

/-- An additive coefficient-field section of reduction. -/
def Chapter10CoefficientFieldSection
    {L : Type*} [Field L] (A : ValuationSubring L) : Prop :=
  ∃ s : Chapter10ResidueField A →+* A,
    ∀ a, IsLocalRing.residue A (s a) = a

/-- In mixed characteristic, reduction need not have an additive coefficient-field section. -/
theorem chapter10_mixed_characteristic_no_coefficient_field_section
    {L : Type*} [Field L] (A : ValuationSubring L) [CharZero A]
    (p : ℕ) [Fact p.Prime] [CharP (Chapter10ResidueField A) p] :
    ¬ Chapter10CoefficientFieldSection A := by
  rintro ⟨s, hs⟩
  have hpzero : (p : Chapter10ResidueField A) = 0 :=
    CharP.cast_eq_zero (Chapter10ResidueField A) p
  have hpA : (p : A) = 0 := by
    calc
      (p : A) = s (p : Chapter10ResidueField A) := by
        symm
        exact map_natCast s p
      _ = s 0 := by rw [hpzero]
      _ = 0 := map_zero s
  exact (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero) hpA

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
