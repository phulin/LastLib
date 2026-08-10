import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section03ThePadicIntegersAndNumbers

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter08

open Polynomial IsLocalRing
open Filter
open scoped BigOperators LaurentSeries Topology PowerSeries.WithPiTopology

noncomputable section

/-!
# Chapter 8: Inverse limits and digit expansions

This file is deliberately a statement-generation pass. The declarations use Mathlib's
AdicCompletion, ideal quotients, PadicInt, Padic, PowerSeries, and LaurentSeries
where those interfaces match the book. A few predicates package the adic convergence and
digit notation used in the prose.
-/

/-! # Book 1, Chapter 8, Section 8.4: Formal Power Series
-/

/-! ### 8.4 Formal power series -/

abbrev Chapter08FormalPowerSeries (k : Type*) [Semiring k] := PowerSeries k
abbrev Chapter08FormalLaurentSeries (k : Type*) [Field k] := LaurentSeries k

/-- The truncation inverse limit for the polynomial variable X. -/
abbrev Chapter08FormalPowerSeriesInverseLimit (k : Type*) [Field k] :=
  Chapter08CompatibleFamily (MvPolynomial PUnit.{1} k)
    (MvPolynomial.idealOfVars PUnit.{1} k)

theorem chapter08_power_series_inverse_limit
    (k : Type*) [Field k] :
    Nonempty (PowerSeries k ≃+* Chapter08FormalPowerSeriesInverseLimit k) := by
  classical
    obtain ⟨e, he⟩ :=
    chapter08_inverse_limit_ring_equiv
      (MvPolynomial.idealOfVars PUnit.{1} k)
  let c := MvPowerSeries.toAdicCompletionAlgEquiv PUnit.{1} k
  exact ⟨c.toRingEquiv.trans e⟩

/-- Constants give the canonical coefficient-field embedding into formal power series. -/
def Chapter08PowerSeriesConstants (k : Type*) [Semiring k] : k →+* PowerSeries k :=
  PowerSeries.C

theorem chapter08_power_series_constants_injective
    (k : Type*) [Field k] :
    Function.Injective (Chapter08PowerSeriesConstants k) := by
  exact PowerSeries.C_injective

theorem chapter08_power_series_is_fraction_field_of_power_series
    (k : Type*) [Field k] :
    IsFractionRing (PowerSeries k) (Chapter08FormalLaurentSeries k) := by
  infer_instance

theorem chapter08_formal_laurent_series_are_complete
    (k : Type*) [Field k] : CompleteSpace (Chapter08FormalLaurentSeries k) := by
  infer_instance

/-- Coefficientwise Cauchy data for a Laurent-series sequence. -/
def Chapter08LaurentCoefficientwiseCauchy
    {k : Type*} [Field k] (u : ℕ → Chapter08FormalLaurentSeries k) : Prop :=
  ∀ d : ℤ, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    (u m).coeff d = (u n).coeff d

/-- A common lower bound on the exponents occurring in a sequence of Laurent series. -/
def Chapter08CommonLaurentLowerBound
    {k : Type*} [Field k] (u : ℕ → Chapter08FormalLaurentSeries k) : Prop :=
  ∃ L : ℤ, ∀ n : ℕ, ∀ d : ℤ, d < L → (u n).coeff d = 0

-- The coefficientwise construction gives a common lower-bounded Laurent series limit. -/
theorem chapter08_laurent_series_cauchy_coefficient_construction
    (k : Type*) [Field k] (u : ℕ → Chapter08FormalLaurentSeries k)
    (_hu : Chapter08LaurentCoefficientwiseCauchy u)
    (_hL : Chapter08CommonLaurentLowerBound u)
    (hC : CauchySeq u) :
    ∃ x : Chapter08FormalLaurentSeries k,
      (∀ d : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (u n).coeff d = x.coeff d) ∧
        Tendsto u atTop (𝓝 x) := by
  classical
  let hℱ : Cauchy (atTop.map u) := hC
  let x : Chapter08FormalLaurentSeries k := LaurentSeries.Cauchy.limit hℱ
  refine ⟨x, ?_, ?_⟩
  · intro d
    have heq := LaurentSeries.Cauchy.coeff_eventually_equal hℱ (D := d + 1)
    have heq' : ∀ᶠ n in atTop, ∀ d', d' < d + 1 →
        x.coeff d' = (u n).coeff d' := by
      change u ⁻¹' {f : Chapter08FormalLaurentSeries k |
        ∀ d', d' < d + 1 → x.coeff d' = f.coeff d'} ∈ atTop
      exact heq
    rcases (eventually_atTop.1 heq') with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    exact (hN n hn d (by omega)).symm
  · intro U hU
    have h := LaurentSeries.Cauchy.eventually_mem_nhds hℱ hU
    change u ⁻¹' U ∈ atTop
    exact h

/-! The filtration analogy Z_p ↔ k[[t]], Q_p ↔ k((t)), p ↔ t. -/
theorem chapter08_padic_formal_series_filtration_analogy
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] :
    IsDiscreteValuationRing (Chapter08PadicIntegers p) ∧
      IsDiscreteValuationRing (PowerSeries k) ∧
      CompleteSpace (Chapter08PadicIntegers p) ∧
      CompleteSpace (Chapter08FormalLaurentSeries k) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem chapter08_formal_power_series_residue_field_is_constants
    (k : Type*) [Field k] :
    Nonempty (IsLocalRing.ResidueField (PowerSeries k) ≃+* k) := by
  exact ⟨PowerSeries.residueFieldOfPowerSeries⟩

theorem chapter08_power_series_preserves_characteristic
    (k : Type*) [Field k] (q : ℕ) [CharP k q] : CharP (PowerSeries k) q := by
  exact charP_of_injective_ringHom PowerSeries.C_injective q

theorem chapter08_padic_numbers_have_characteristic_zero
    (p : ℕ) [Fact p.Prime] : CharZero (Chapter08PadicNumbers p) := by
  infer_instance

theorem chapter08_no_Fp_embedding_in_characteristic_zero
    {A : Type*} [Ring A] [CharZero A] (p : ℕ) [Fact p.Prime] :
    ¬ ∃ f : ZMod p →+* A, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hp : (p : A) = 0 := by
    calc
      (p : A) = f (p : ZMod p) := by rw [map_natCast]
      _ = f 0 := by rw [ZMod.natCast_self]
      _ = 0 := map_zero f
  exact (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero) hp

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter08
