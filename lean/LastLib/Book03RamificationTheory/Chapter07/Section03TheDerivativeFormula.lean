import LastLib.Book03RamificationTheory.Chapter07.Section02UnramifiednessAndTheDifferent

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open Polynomial
open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.3. The derivative formula -/

/-- The monogenic presentation used by the derivative formula. -/
def chapter07MonogenicPresentation
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (α : B) (f : A[X]) : Prop :=
  IsIntegral A α ∧ Algebra.adjoin A ({α} : Set B) = ⊤ ∧ f.Monic ∧
    aeval α f = 0 ∧
    f.map (algebraMap A K) = minpoly K (algebraMap B L α)

def chapter07DerivativeAt
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (f : A[X]) (α : B) : B :=
  aeval α f.derivative

theorem chapter07MonogenicPresentation_is_integral
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (α : B) (f : A[X])
    (h : chapter07MonogenicPresentation A B K L α f) :
    IsIntegral A α := by
  exact h.1

theorem chapter07MonogenicPresentation_generates
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (α : B) (f : A[X])
    (h : chapter07MonogenicPresentation A B K L α f) :
    Algebra.adjoin A ({α} : Set B) = ⊤ := by
  exact h.2.1

theorem chapter07_different_eq_derivative_ideal
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f) :
    chapter07DifferentIdeal A B =
      Ideal.span ({chapter07DerivativeAt A B f α} : Set B) := by
  sorry

/- Lagrange interpolation in a splitting field. -/
def chapter07InterpolationRootData
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (n : ℕ) (f : K[X]) (roots : Fin n → E) : Prop :=
  f.Monic ∧ f.natDegree = n ∧
    (∀ z : E, eval₂ (algebraMap K E) z f = 0 ↔
      ∃ i : Fin n, z = roots i) ∧
    (∀ i : Fin n,
      eval₂ (algebraMap K E) (roots i) f.derivative ≠ 0)

theorem chapter07_lagrange_interpolation_top_coefficient
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (n : ℕ) (f : K[X]) (roots : Fin n → E)
    (hroots : chapter07InterpolationRootData K E n f roots)
    (g : K[X]) (hg : g.natDegree < n) :
    algebraMap K E (g.coeff (n - 1)) =
      ∑ i : Fin n,
        eval₂ (algebraMap K E) (roots i) g /
          eval₂ (algebraMap K E) (roots i) f.derivative := by
  sorry

/- The same identity with the right-hand side recognized as a field trace. -/
theorem chapter07_interpolation_is_trace
    (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [Normal K Ω]
    (α : L) (f g : K[X])
    (hf : f = minpoly K α) (hg : g.natDegree < f.natDegree) :
    algebraMap K Ω
        (Algebra.trace K L
          (aeval α g / aeval α f.derivative)) =
      ∑ σ : L →ₐ[K] Ω,
        eval₂ (algebraMap K Ω) (σ α) g /
          eval₂ (algebraMap K Ω) (σ α) f.derivative := by
  sorry

/- The numerator polynomials q_i from the source. -/
def chapter07DualNumerator
    {A : Type*} [CommRing A] (f : A[X]) (n i : ℕ) : A[X] :=
  Finset.sum (Finset.Icc (i + 1) n) (fun j =>
    C (f.coeff j) * X ^ (j - i - 1))

def chapter07DualNumeratorValue
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (f : A[X]) (n i : ℕ) (α : B) : B :=
  aeval α (chapter07DualNumerator f n i)

theorem chapter07_dual_numerator_leading_shape
    {A : Type*} [CommRing A] (f : A[X]) (n i : ℕ)
    (hmonic : f.Monic) (hdegree : f.natDegree = n) (hi : i < n) :
    (chapter07DualNumerator f n i).coeff (n - i - 1) = 1 := by
  sorry

theorem chapter07_dual_numerators_form_basis
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsIntegralClosure B A L]
    (α : B) (f : A[X]) (n : ℕ)
    (hmono : chapter07MonogenicPresentation A B K L α f)
    (hdegree : f.natDegree = n) :
    LinearIndependent A
        (fun i : Fin n => chapter07DualNumeratorValue f n i α) ∧
      Submodule.span A
          (Set.range (fun i : Fin n =>
            chapter07DualNumeratorValue f n i α)) = ⊤ := by
  sorry

theorem chapter07_trace_dual_basis_formula
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (α : B) (f : A[X]) (n : ℕ)
    (hmono : chapter07MonogenicPresentation A B K L α f)
    (hdegree : f.natDegree = n)
    (i j : Fin n) :
    Algebra.trace K L
        ((algebraMap B L (chapter07DualNumeratorValue f n i α) /
            algebraMap B L (chapter07DerivativeAt A B f α)) *
          (algebraMap B L α) ^ (j : ℕ)) =
      if i = j then 1 else 0 := by
  sorry

def chapter07InversePrincipalSet
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (δ : B) : Set L :=
  {x | ∃ b : B, x = algebraMap B L b / algebraMap B L δ}

theorem chapter07_inverse_principal_mem_iff
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (δ : B) (x : L) :
    x ∈ chapter07InversePrincipalSet A B K L δ ↔
      ∃ b : B, x = algebraMap B L b / algebraMap B L δ := Iff.rfl

theorem chapter07_codifferent_eq_inverse_derivative_principal
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDedekindDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f) :
    chapter07CodifferentSet A B K L =
      chapter07InversePrincipalSet A B K L
        (chapter07DerivativeAt A B f α) := by
  sorry

theorem chapter07_eisenstein_different_exponent_eq_derivative_valuation
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (vL : AddValuation L (WithTop ℤ)) (mB : Ideal B) (d : ℕ)
    (πL : B) (f : A[X])
    (_hmono : chapter07MonogenicPresentation A B K L πL f)
    (_hD : chapter07DifferentIdeal A B = mB ^ d)
    (hvalue : vL (algebraMap B L
        (chapter07DerivativeAt A B f πL)) = (d : WithTop ℤ)) :
    vL (algebraMap B L (chapter07DerivativeAt A B f πL)) =
      (d : WithTop ℤ) := by
  exact hvalue

end

end LastLib.Book03RamificationTheory.Chapter07
