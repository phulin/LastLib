import LastLib.Book03RamificationTheory.Chapter07.Section05ExactTraceIdeals

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open Polynomial
open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.6. Tame and wild derivative bounds -/

/- SOURCE_ISSUE (7.6): The source promotes the Eisenstein/monogenic
   calculation to an extension-level equivalence `d = e - 1` from residue
   separability alone.  A defectless (for example perfect-residue) hypothesis,
   together with the indicated monogenic decomposition, is needed; otherwise
   retain only the bound for the displayed presentation. -/

/-- The `j`th derivative term evaluated at a chosen uniformizer. -/
def chapter07DerivativeTerm
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (j : ℕ) (a : K) (π : L) : L :=
  algebraMap K L ((j : K) * a) * π ^ (j - 1)

theorem chapter07_derivative_term_zero_of_zero_coefficient
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (j : ℕ) (π : L) :
    chapter07DerivativeTerm K L j 0 π = 0 := by
  simp [chapter07DerivativeTerm]

theorem chapter07_derivative_eval_expansion
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (f : K[X]) (π : L) (n : ℕ) (hdegree : f.natDegree = n) :
    aeval π f.derivative =
      Finset.sum (Finset.range n) (fun j =>
        chapter07DerivativeTerm K L (j + 1) (f.coeff (j + 1)) π) := by
  sorry

theorem chapter07_leading_derivative_term_value
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) (π : L)
    (he : (e : K) ≠ 0)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = (e : WithTop ℤ) * vK x)
    (hπ : vL π = (1 : WithTop ℤ)) :
    vL (chapter07DerivativeTerm K L e 1 π) =
      (e : WithTop ℤ) * vK (e : K) + (e : WithTop ℤ) - 1 := by
  sorry

theorem chapter07_other_derivative_term_value_lower_bound
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e j : ℕ) (a : K) (π : L)
    (hj : 1 ≤ j) (hjdegree : j < e)
    (ha : vK a ≥ (1 : WithTop ℤ))
    (hjvalue : vK (j : K) ≥ (0 : WithTop ℤ))
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = (e : WithTop ℤ) * vK x)
    (hπ : vL π = (1 : WithTop ℤ)) :
    vL (chapter07DerivativeTerm K L j a π) ≥
      (e : WithTop ℤ) + (j : WithTop ℤ) - 1 := by
  sorry

def chapter07DifferentExponentValuation
    {L : Type*} [Ring L]
    (vL : AddValuation L (WithTop ℤ)) (z : L) (d : ℕ) : Prop :=
  vL z = (d : WithTop ℤ)

theorem chapter07_different_exponent_value_iff
    (L : Type*) [Field L] (vL : AddValuation L (WithTop ℤ))
    (z : L) (d : ℕ) :
    chapter07DifferentExponentValuation vL z d ↔
      vL z = (d : WithTop ℤ) := Iff.rfl

theorem chapter07_sum_of_eisenstein_derivative_terms_ge_baseline
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) (terms : Fin e → L)
    (hterms : ∀ j : Fin e, vL (terms j) ≥
      (e : WithTop ℤ) - 1) :
    vL (∑ j, terms j) ≥ (e : WithTop ℤ) - 1 := by
  sorry

theorem chapter07_different_exponent_ge_e_sub_one
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (e d : ℕ) (z : L)
    (hvalue : chapter07DifferentExponentValuation vL z d)
    (hbaseline : vL z ≥ (e : WithTop ℤ) - 1) :
    e - 1 ≤ d := by
  sorry

/- Tame and wild are recorded only after the residue characteristic has been
   named. -/
def chapter07TameAtResidueCharacteristic (e p : ℕ) : Prop :=
  Nat.Coprime e p

def chapter07WildAtResidueCharacteristic (e p : ℕ) : Prop :=
  ¬chapter07TameAtResidueCharacteristic e p

theorem chapter07_wild_iff_prime_dvd
    (e p : ℕ) [Fact (Nat.Prime p)] :
    chapter07WildAtResidueCharacteristic e p ↔ p ∣ e := by
  sorry

theorem chapter07_tame_leading_term_has_value_e_sub_one
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) (π : L)
    (he : (e : K) ≠ 0) (heunit : vK (e : K) = 0)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = (e : WithTop ℤ) * vK x)
    (hπ : vL π = (1 : WithTop ℤ)) :
    vL (chapter07DerivativeTerm K L e 1 π) =
      (e : WithTop ℤ) - 1 := by
  sorry

theorem chapter07_tame_different_exponent_eq_e_sub_one
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e d : ℕ) (π : L) (z : L)
    (hvalue : chapter07DifferentExponentValuation vL z d)
    (hπ : vL π = (1 : WithTop ℤ))
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = (e : WithTop ℤ) * vK x)
    (he : (e : K) ≠ 0) (heunit : vK (e : K) = 0)
    (hderivative_leading : z = chapter07DerivativeTerm K L e 1 π) :
    d = e - 1 := by
  sorry

theorem chapter07_tame_iff_different_baseline
    (e p d : ℕ) [Fact (Nat.Prime p)] (he : 0 < e)
    (htame : chapter07TameAtResidueCharacteristic e p → d = e - 1)
    (hwild : p ∣ e → e ≤ d) (hbaseline : e - 1 ≤ d) :
    chapter07TameAtResidueCharacteristic e p ↔ d = e - 1 := by
  sorry

/- In equal characteristic p, the leading derivative term disappears when
   p divides the ramification degree. -/
theorem chapter07_equal_characteristic_wild_leading_term_zero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (p e : ℕ) [CharP K p] [Fact (Nat.Prime p)]
    (hdiv : p ∣ e) (π : L) :
    chapter07DerivativeTerm K L e 1 π = 0 := by
  sorry

/- In mixed characteristic the leading term is at least `2e - 1` after the
   normalized valuation is transferred upstairs. -/
theorem chapter07_mixed_characteristic_wild_leading_term_lower_bound
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [CharZero K] (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (p e : ℕ) [Fact (Nat.Prime p)] (π : L)
    (hdiv : p ∣ e)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = (e : WithTop ℤ) * vK x)
    (hπ : vL π = (1 : WithTop ℤ))
    (he : (e : K) ≠ 0) (hevalue : vK (e : K) ≥ (1 : WithTop ℤ)) :
    vL (chapter07DerivativeTerm K L e 1 π) ≥
      2 * (e : WithTop ℤ) - 1 := by
  sorry

theorem chapter07_wild_nonleading_derivative_terms_ge_e
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e j : ℕ) (a : K) (π : L)
    (hj : 1 ≤ j) (hjdegree : j < e)
    (ha : vK a ≥ (1 : WithTop ℤ))
    (hjvalue : vK (j : K) ≥ (0 : WithTop ℤ))
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = (e : WithTop ℤ) * vK x)
    (hπ : vL π = (1 : WithTop ℤ)) :
    vL (chapter07DerivativeTerm K L j a π) ≥ (e : WithTop ℤ) := by
  sorry

theorem chapter07_wild_different_exponent_ge_e
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (e d : ℕ) (z : L)
    (hvalue : chapter07DifferentExponentValuation vL z d)
    (hwild_terms : vL z ≥ (e : WithTop ℤ)) :
    e ≤ d := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter07
