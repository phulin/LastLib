import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section04RamificationIndexAndResidueDegree
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.FieldTheory.Separable
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

universe u10K u10L u10Γ

open scoped BigOperators TensorProduct WithZero PowerSeries
open Polynomial

noncomputable section

/-!
# Chapter 10: Extensions of valuations

This file is a statement-generation formalization of Sections 10.1--10.7 of
Book 1.  The declarations deliberately keep the valuation-theoretic data
explicit: this makes the extension, residue, and ramification assertions
usable independently of the other generated chapters.
-/

/-! # Book 1, Chapter 10, Section 10.7: Concrete Finite Extensions
-/

/-! ## 10.7. Concrete finite extensions -/

/-- A compact profile for the examples in this section. -/
structure Chapter10FiniteExtensionProfile where
  degree : ℕ
  ramificationIndex : ℕ
  residueDegree : ℕ

/-- A numerical profile records the invariants of a specified finite branch. -/
def Chapter10ProfileRealizedByData
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL] [FiniteDimensional K L]
    {v : Valuation K ΓK} {w : Valuation L ΓL}
    {h : v.IsEquiv (w.comap (algebraMap K L))}
    (d : Chapter10HeterogeneousExtensionData v w h)
    (p : Chapter10FiniteExtensionProfile) : Prop :=
  p.degree = Module.finrank K L ∧
  p.ramificationIndex = d.ramificationIndex ∧
    p.residueDegree = d.residueDegree

/-- The profile of a totally ramified extension. -/
def Chapter10TotallyRamified (p : Chapter10FiniteExtensionProfile) : Prop :=
  p.ramificationIndex = p.degree ∧ p.residueDegree = 1

/-- The numerical part of an unramified profile.

This predicate deliberately does not assert separability of the residue
extension; `Chapter10UnramifiedBranch` is the branch-level predicate below.
-/
def Chapter10Unramified (p : Chapter10FiniteExtensionProfile) : Prop :=
  p.ramificationIndex = 1 ∧ p.residueDegree = p.degree

/-- The equal-characteristic relation t = uⁿ. -/
def Chapter10PowerParameterRelation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (t : K) (u : L) (n : ℕ) : Prop :=
  algebraMap K L t = u ^ n

/-- Scaling of the normalized value on the base field. -/
def Chapter10ValueScaling
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (n : ℕ) : Prop :=
  ∀ x : K, x ≠ 0 → vL (algebraMap K L x) = n • vK x

/-- Separability of the residue-field extension attached to a valuation branch. -/
def Chapter10ResidueExtensionIsSeparable
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    [Valuation.HasExtension v w] : Prop :=
  ∀ x : Chapter10ResidueField w, IsSeparable (Chapter10ResidueField v) x

/-- The intrinsic unramified condition for a specified valuation branch. -/
def Chapter10UnramifiedBranch
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL] [FiniteDimensional K L]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (h : v.IsEquiv (w.comap (algebraMap K L)))
    (d : Chapter10HeterogeneousExtensionData v w h) : Prop := by
  letI : Valuation.HasExtension v w := ⟨h⟩
  exact d.ramificationIndex = 1 ∧ Chapter10ResidueExtensionIsSeparable v w

/-- The Laurent-series valuation used in the equal-characteristic model. -/
def Chapter10LaurentSeriesValuation (k : Type*) [Field k] :
    Valuation (LaurentSeries k) ℤᵐ⁰ :=
  Valued.v

/-- Value of a power of the Laurent-series parameter. -/
theorem chapter10_laurent_series_parameter_value
    {k : Type*} [Field k] (n : ℕ) :
    Chapter10LaurentSeriesValuation k
        (((PowerSeries.X : PowerSeries k) : LaurentSeries k) ^ n) =
      WithZero.exp (-(n : ℤ)) := by
  exact LaurentSeries.valuation_X_pow k n

/-- The power polynomial is separable exactly away from the residue
characteristic divisors of its exponent. -/
theorem chapter10_power_polynomial_separable_iff
    {K : Type*} [Field K] {p n : ℕ} [CharP K p]
    (a : K) (hn : 0 < n) (ha : a ≠ 0) :
    (X ^ n - C a : K[X]).Separable ↔ ¬ p ∣ n := by
  rw [X_pow_sub_C_separable_iff hn ha]
  exact not_congr (CharP.cast_eq_zero_iff K p n)

/-- The extension k((u))/k((t)) with t = uⁿ has e = n and f = 1. -/
theorem chapter10_equal_characteristic_totally_ramified_profile
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L]
    [FiniteDimensional K L]
    (t : K) (u : L) (n : ℕ)
    (hn : 0 < n)
    (hparameter : Chapter10PowerParameterRelation t u n)
    (hirreducible : Irreducible (X ^ n - C t : K[X]))
    (hdegree : Module.finrank K L = n)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvK : Chapter10DiscreteAddValuation vK)
    (hvL : Chapter10DiscreteAddValuation vL)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (ht : vK t = 1) (hu : vL u = 1) :
    ∃ d : Chapter10HeterogeneousExtensionData vK vL hext,
      ∃ p : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d p ∧
          p.degree = n ∧ p.ramificationIndex = n ∧ p.residueDegree = 1 ∧
          Chapter10TotallyRamified p := by
  sorry

/-- Constant-field extensions have e = 1 and residue degree equal to the field degree. -/
theorem chapter10_constant_field_extension_profile
    {k k' : Type*} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    (n : ℕ) (hn : n = Module.finrank k k')
    (_hseparable : Algebra.IsSeparable k k') :
    ∃ p : Chapter10FiniteExtensionProfile,
      p.degree = n ∧ p.ramificationIndex = 1 ∧
        p.residueDegree = Module.finrank k k' ∧ Chapter10Unramified p := by
  subst n
  let d := Module.finrank k k'
  refine ⟨{ degree := d, ramificationIndex := 1, residueDegree := d }, rfl, rfl, rfl, ?_⟩
  exact ⟨rfl, rfl⟩

/-- Combining a constant extension and a totally ramified extension gives ef. -/
theorem chapter10_combined_equal_characteristic_profile
    {e f : ℕ} (he : 0 < e) (hf : 0 < f) :
    ∃ p : Chapter10FiniteExtensionProfile,
      p.degree = e * f ∧ p.ramificationIndex = e ∧
        p.residueDegree = f := by
  have _ := he
  have _ := hf
  exact ⟨{ degree := e * f, ramificationIndex := e, residueDegree := f }, rfl, rfl, rfl⟩

/-- A local polynomial criterion spelling out the Eisenstein coefficient conditions. -/
def Chapter10EisensteinAtUniformizer {A : Type*} [CommRing A]
    (P : A[X]) (π : A) : Prop :=
  P.Monic ∧ P.natDegree ≠ 0 ∧
    (∀ i < P.natDegree, π ∣ P.coeff i) ∧
    ¬ π ^ 2 ∣ P.constantCoeff

/-- Eisenstein irreducibility. -/
theorem chapter10_eisenstein_irreducible
    {A : Type*} [CommRing A] [IsDomain A]
    (P : A[X]) (π : A) (hπ : Prime π)
    (hE : Chapter10EisensteinAtUniformizer P π) :
    Irreducible P := by
  rcases hE with ⟨hmonic, hdegree, hcoeff, hconstant⟩
  let p : Ideal A := Ideal.span ({π} : Set A)
  have hp : p.IsPrime := Ideal.isPrime_span_singleton_of_prime hπ
  have hleading : P.leadingCoeff ∉ p := by
    rw [hmonic.leadingCoeff]
    exact (Ideal.ne_top_iff_one p).mp hp.ne_top
  have hcoeff' : ∀ i < P.natDegree, P.coeff i ∈ p := by
    intro i hi
    exact Ideal.mem_span_singleton.mpr (hcoeff i hi)
  have hconstant' : P.coeff 0 ∉ p ^ 2 := by
    intro h
    apply hconstant
    rw [Ideal.span_singleton_pow] at h
    exact Ideal.mem_span_singleton.mp h
  have hdegree' : 0 < P.degree := by
    exact Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdegree)
  apply Polynomial.irreducible_of_eisenstein_criterion hp hleading
    (fun i hi => hcoeff' i (Polynomial.coe_lt_degree.mp hi)) hdegree' hconstant'
  exact hmonic.isPrimitive

/-- The minimal-value comparison for an Eisenstein root. -/
theorem chapter10_eisenstein_root_value_comparison
    {A L : Type*} [CommRing A] [IsDomain A] [Field L]
    [Algebra A L]
    (vL : AddValuation L (WithTop ℤ))
    (P : A[X]) (π : A) (α : L) (n : ℕ)
    (hroot : Polynomial.eval₂ (algebraMap A L) α P = 0)
    (hdegree : P.natDegree = n)
    (hE : Chapter10EisensteinAtUniformizer P π)
    (hπ : 0 < vL (algebraMap A L π))
    (hconstant : vL (algebraMap A L P.constantCoeff) =
      vL (algebraMap A L π))
    (hcoeff : ∀ i < n,
      vL (algebraMap A L (P.coeff i)) ≥ vL (algebraMap A L π)) :
    n • vL α = vL (algebraMap A L π) := by
  rcases hE with ⟨hmonic, hdegree0, _hcoeffdiv, _hconstantdiv⟩
  have hn : 0 < n := by
    rw [← hdegree]
    exact Nat.pos_of_ne_zero hdegree0
  have hdeg_lt : P.natDegree < n + 1 := by
    rw [hdegree]
    exact Nat.lt_succ_self n
  let term : ℕ → L := fun i =>
    algebraMap A L (P.coeff i) * α ^ i
  have hsum : (∑ i ∈ Finset.range (n + 1), term i) = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range' (algebraMap A L) hdeg_lt α]
    exact hroot
  have hcoeff_n : P.coeff n = 1 := by
    rw [← hdegree]
    exact hmonic.leadingCoeff
  by_cases hc_top : vL (algebraMap A L π) = ⊤
  · have hterm_low : ∀ i < n, term i = 0 := by
      intro i hi
      dsimp [term]
      have hi_top : vL (algebraMap A L (P.coeff i)) = ⊤ := by
        apply top_unique
        simpa [hc_top] using hcoeff i hi
      rw [(AddValuation.top_iff vL).mp hi_top]
      simp
    have hsum' := hsum
    rw [Finset.sum_range_succ] at hsum'
    have hsum_low : (∑ i ∈ Finset.range n, term i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hterm_low i (Finset.mem_range.mp hi)
    rw [hsum_low, zero_add] at hsum'
    have hpow : α ^ n = 0 := by
      simpa [term, hcoeff_n] using hsum'
    have hα : α = 0 := (pow_eq_zero_iff hn.ne').mp hpow
    rw [hα, AddValuation.map_zero, hc_top]
    rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨k, rfl⟩
    simp [succ_nsmul]
  · have hπtop : vL (algebraMap A L π) ≠ ⊤ := hc_top
    have hα0 : α ≠ 0 := by
      intro hα0
      have hroot0 : Polynomial.eval₂ (algebraMap A L) 0 P = 0 := by
        simpa [hα0] using hroot
      have hconstL : algebraMap A L P.constantCoeff = 0 := by
        simpa using hroot0
      have hconstVal : vL (algebraMap A L P.constantCoeff) = ⊤ := by
        rw [hconstL, AddValuation.map_zero]
      have hπ_top : vL (algebraMap A L π) = ⊤ := by
        calc
          vL (algebraMap A L π) = vL (algebraMap A L P.constantCoeff) :=
            hconstant.symm
          _ = ⊤ := hconstVal
      exact hπtop hπ_top
    have hαtop : vL α ≠ ⊤ := (AddValuation.ne_top_iff vL).mpr hα0
    have hterm_val (i : ℕ) :
        vL (term i) = vL (algebraMap A L (P.coeff i)) + i • vL α := by
      simp [term, AddValuation.map_mul, AddValuation.map_pow]
    have hterm_n : term n = α ^ n := by
      dsimp [term]
      rw [hcoeff_n]
      simp
    have hterm_n_val : vL (term n) = n • vL α := by
      rw [hterm_n, AddValuation.map_pow]
    have hsmul_top (k : ℕ) : k • vL α ≠ ⊤ := by
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hαtop
      rw [← ha, ← WithTop.coe_nsmul]
      exact WithTop.coe_ne_top
    have hterm_n_top : vL (term n) ≠ ⊤ := by
      rw [hterm_n_val]
      exact hsmul_top n
    have hterm_zero_val : vL (term 0) = vL (algebraMap A L π) := by
      rw [hterm_val]
      simpa [hconstant, add_zero]
    have hterm_zero_top : vL (term 0) ≠ ⊤ := by
      rw [hterm_zero_val]
      exact hπtop
    have hunique_min {j : ℕ} (hj : j ∈ Finset.range (n + 1))
        (hstrict : ∀ i ∈ Finset.range (n + 1) \ {j},
          vL (term j) < vL (term i))
        (hjtop : vL (term j) ≠ ⊤) : False := by
      have hv := (AddValuation.toValuation vL).map_sum_eq_of_lt hj (by
        intro i hi
        have hdual : OrderDual.toDual (vL (term i)) <
            OrderDual.toDual (vL (term j)) :=
          OrderDual.toDual_lt_toDual.mpr (hstrict i hi)
        simpa only [AddValuation.toValuation_apply] using
          (Multiplicative.ofAdd_lt.mpr hdual)
        : ∀ i ∈ Finset.range (n + 1) \ {j},
            AddValuation.toValuation vL (term i) <
              AddValuation.toValuation vL (term j))
      simp only [AddValuation.toValuation_apply] at hv
      change OrderDual.toDual (vL (∑ i ∈ Finset.range (n + 1), term i)) =
        OrderDual.toDual (vL (term j)) at hv
      have hv' : vL (∑ i ∈ Finset.range (n + 1), term i) = vL (term j) := by
        simpa using hv
      rw [hsum, AddValuation.map_zero] at hv'
      exact hjtop hv'.symm
    have hαpos : 0 < vL α := by
      by_contra hαpos
      have hαnonpos : vL α ≤ 0 := le_of_not_gt hαpos
      apply hunique_min (j := n) (Finset.mem_range.mpr (Nat.lt_succ_self n)) ?_
        hterm_n_top
      intro i hi
      have hi_lt : i < n := by
        have hi_le : i ≤ n := by
          have hi_succ : i < n + 1 :=
            Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
          omega
        exact Nat.lt_of_le_of_ne hi_le (by
          intro hin
          exact (Finset.mem_sdiff.mp hi).2 (by simp [hin]))
      have hni : i ≤ n := Nat.le_of_lt hi_lt
      have hna : n • vL α ≤ i • vL α := by
        rw [← Nat.add_sub_of_le hni, add_nsmul]
        exact add_le_of_nonpos_right (nsmul_nonpos hαnonpos _)
      have hia0 : i • vL α <
          vL (algebraMap A L π) + i • vL α := by
        have hi_top : i • vL α ≠ ⊤ := hsmul_top i
        simpa using WithTop.add_lt_add_right hi_top hπ
      have hci := hcoeff i hi_lt
      have hia : i • vL α <
          vL (algebraMap A L (P.coeff i)) + i • vL α :=
        hia0.trans_le (by
          have h := add_le_add_left hci (i • vL α)
          simpa [add_comm] using h)
      calc
        vL (term n) = n • vL α := hterm_n_val
        _ < vL (algebraMap A L (P.coeff i)) + i • vL α := hna.trans_lt hia
        _ = vL (term i) := (hterm_val i).symm
    have hEq : n • vL α = vL (algebraMap A L π) := by
      rcases lt_trichotomy (n • vL α) (vL (algebraMap A L π)) with hlt | heq | hgt
      · exfalso
        apply hunique_min (j := n) (Finset.mem_range.mpr (Nat.lt_succ_self n)) ?_
          hterm_n_top
        intro i hi
        have hi_lt : i < n := by
          have hi_le : i ≤ n := by
            have hi_succ : i < n + 1 :=
              Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
            omega
          exact Nat.lt_of_le_of_ne hi_le (by
            intro hin
            exact (Finset.mem_sdiff.mp hi).2 (by simp [hin]))
        have hia : (0 : WithTop ℤ) ≤ i • vL α :=
          nsmul_nonneg (le_of_lt hαpos) i
        have hci := hcoeff i hi_lt
        calc
          vL (term n) = n • vL α := hterm_n_val
          _ < vL (algebraMap A L π) := hlt
          _ ≤ vL (algebraMap A L (P.coeff i)) := hci
          _ ≤ vL (algebraMap A L (P.coeff i)) + i • vL α :=
            le_add_of_nonneg_right hia
          _ = vL (term i) := (hterm_val i).symm
      · exact heq
      · exfalso
        apply hunique_min (j := 0) (Finset.mem_range.mpr (Nat.zero_lt_succ n)) ?_
          hterm_zero_top
        intro i hi
        have hi_pos : 0 < i := by
          have hi_ne : i ≠ 0 := by simpa using (Finset.mem_sdiff.mp hi).2
          exact Nat.pos_of_ne_zero hi_ne
        by_cases hi_n : i = n
        · subst i
          rw [hterm_n_val, hterm_zero_val]
          exact hgt
        · have hi_lt : i < n := by
            have hi_le : i ≤ n := by
              have hi_succ : i < n + 1 :=
                Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
              omega
            exact Nat.lt_of_le_of_ne hi_le hi_n
          have hia : (0 : WithTop ℤ) < i • vL α := by
            exact nsmul_pos hαpos hi_pos.ne'
          have hci := hcoeff i hi_lt
          have hia0 : vL (algebraMap A L π) <
              vL (algebraMap A L π) + i • vL α := by
            simpa using WithTop.add_lt_add_left hπtop hia
          calc
            vL (term 0) = vL (algebraMap A L π) := hterm_zero_val
            _ < vL (algebraMap A L π) + i • vL α := hia0
            _ ≤ vL (algebraMap A L (P.coeff i)) + i • vL α := by
              have h := add_le_add_left hci (i • vL α)
              simpa [add_comm] using h
            _ = vL (term i) := (hterm_val i).symm
    exact hEq

/-- Eisenstein extensions are totally ramified of the polynomial degree. -/
theorem chapter10_eisenstein_totally_ramified_profile
    {A K L : Type*} [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    (P : A[X]) (π : A) (α : L)
    (hE : Chapter10EisensteinAtUniformizer P π)
    (hroot : Polynomial.eval₂ (algebraMap A L) α P = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = P.natDegree)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvK : Chapter10DiscreteAddValuation vK)
    (hvL : Chapter10DiscreteAddValuation vL)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hA : vK.Integers A)
    (hπ : vK (algebraMap A K π) = 1)
    (hscale : Chapter10ValueScaling vK vL P.natDegree) :
    ∃ d : Chapter10HeterogeneousExtensionData vK vL hext,
      ∃ p : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d p ∧
          p.degree = P.natDegree ∧ p.ramificationIndex = P.natDegree ∧
          p.residueDegree = 1 ∧ Chapter10TotallyRamified p := by
  sorry

/-- A polynomial has irreducible separable reduction through a chosen residue map. -/
def Chapter10IrreducibleSeparableReduction
    {A k : Type*} [CommRing A] [Field k]
    (res : A →+* k) (P : A[X]) (f : ℕ) : Prop :=
  let Q := P.map res
  P.Monic ∧ Q.Monic ∧ Q.natDegree = f ∧ Irreducible Q ∧ Q.Separable

/-- Irreducible separable reduction gives an unramified extension. -/
theorem chapter10_unramified_lift_profile
    {A K L k ΓK ΓL : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field k]
    [Algebra A K] [IsFractionRing A K]
    [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (res : A →+* k) (P : A[X]) (f : ℕ)
    (hred : Chapter10IrreducibleSeparableReduction res P f)
    (hres : ∃ e : IsLocalRing.ResidueField A ≃+* k,
      e.toRingHom.comp (IsLocalRing.residue A) = res)
    (α : L)
    (hroot : Polynomial.eval₂ (algebraMap A L) α P = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = f)
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (hA : v.Integers A)
    (hext : v.IsEquiv (w.comap (algebraMap K L))) :
    ∃ d : Chapter10HeterogeneousExtensionData v w hext,
      ∃ p : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d p ∧
          Irreducible P ∧
          p.degree = f ∧ p.ramificationIndex = 1 ∧
          p.residueDegree = f ∧ Chapter10Unramified p ∧
          Chapter10UnramifiedBranch v w hext d ∧
            (P.map res).Separable := by
  sorry

/-- The p-adic uniformizer has normalized valuation one. -/
theorem chapter10_padic_uniformizer_value
    {p : ℕ} [Fact p.Prime] :
    Padic.valuation (p : ℚ_[p]) = 1 := by
  exact Padic.valuation_p

/-- The standard p-adic integers are the bounded elements for the additive
p-adic valuation. -/
theorem chapter10_padic_integers_are_add_valuation_integers
    {p : ℕ} [Fact p.Prime] :
    (Padic.addValuation (p := p)).Integers (ℤ_[p]) := by
  sorry

/-- The p-adic Eisenstein setup is the preceding theorem with π = p. -/
theorem chapter10_padic_eisenstein_profile
    {p : ℕ} [Fact p.Prime] {L : Type*} [Field L]
    [Algebra ℤ_[p] L] [Algebra ℚ_[p] L]
    [IsScalarTower ℤ_[p] ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L]
    (P : (ℤ_[p])[X]) (α : L)
    (hE : Chapter10EisensteinAtUniformizer P (p : ℤ_[p]))
    (hroot : Polynomial.eval₂ (algebraMap ℤ_[p] L) α P = 0)
    (hgen : Algebra.adjoin ℚ_[p] ({α} : Set L) = ⊤)
    (hdegree : Module.finrank ℚ_[p] L = P.natDegree)
    (vL : AddValuation L (WithTop ℤ))
    (hvL : Chapter10DiscreteAddValuation vL)
    (hext : (Padic.addValuation (p := p)).IsEquiv
      (vL.comap (algebraMap ℚ_[p] L)))
    (hscale : Chapter10ValueScaling (Padic.addValuation (p := p)) vL P.natDegree) :
    ∃ d : Chapter10HeterogeneousExtensionData
        (Padic.addValuation (p := p)) vL hext,
      ∃ q : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d q ∧
          q.degree = P.natDegree ∧ q.ramificationIndex = P.natDegree ∧
          q.residueDegree = 1 ∧ Chapter10TotallyRamified q := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hvK : Chapter10DiscreteAddValuation (Padic.addValuation (p := p)) := by
    refine ⟨(p : ℚ_[p]), hp0, ?_, ?_⟩
    · simpa using (Padic.addValuation.apply hp0).trans
        (by
          convert chapter10_padic_uniformizer_value (p := p) using 1; simp)
    · intro x hx
      refine ⟨x.valuation, ?_⟩
      exact Padic.addValuation.apply hx
  have hπ : Padic.addValuation (p := p)
      (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) = 1 := by
    simpa using (Padic.addValuation.apply hp0).trans
      (by
        convert chapter10_padic_uniformizer_value (p := p) using 1; simp)
  have hA : (Padic.addValuation (p := p)).Integers (ℤ_[p]) :=
    chapter10_padic_integers_are_add_valuation_integers (p := p)
  exact chapter10_eisenstein_totally_ramified_profile
    (A := ℤ_[p]) (K := ℚ_[p]) (L := L) P (p : ℤ_[p]) α
    hE hroot hgen hdegree (Padic.addValuation (p := p)) vL hvK hvL hext hA hπ hscale

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
