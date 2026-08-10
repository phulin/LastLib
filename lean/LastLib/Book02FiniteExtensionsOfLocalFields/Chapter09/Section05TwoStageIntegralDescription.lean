import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section04ImperfectResidueFields

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09

open scoped BigOperators Polynomial
open Ideal IsLocalRing Polynomial

noncomputable section

/-! ## Book 2, Chapter 9.5: a two-stage integral description -/

/-- The explicit set of monomials theta^j pi_L^i appearing in the integral basis. -/
def chapter09ExplicitIntegralBasis
    (K₀ L : Type*) [Field K₀] [Field L] [Algebra K₀ L]
    (θ : K₀) (πL : L) (f e : ℕ) : Set L :=
  {x | ∃ j : Fin f, ∃ i : Fin e,
    x = algebraMap K₀ L (θ ^ (j : ℕ)) * πL ^ (i : ℕ)}

/-- A presentation of the two integral stages.  The first polynomial is
unramified because its derivative is a unit; the second is Eisenstein and has
the ramification degree.  The coordinate fields record both uniqueness claims
from the source, and basis makes the final displayed set a genuine linear
basis. -/
structure Chapter09TwoStageIntegralDescription
    (A B K K₀ L : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [IsLocalRing A]
    [Field K] [Field K₀] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K K₀] [Algebra A K₀]
    [Algebra K₀ L] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K K₀] [IsScalarTower K K₀ L]
    [IsScalarTower A K L] [IsScalarTower A K₀ L] [IsScalarTower A B L]
    [IsLocalHom (algebraMap A B)] [IsFractionRing B L]
    [IsDomain B] [IsLocalRing B] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing A] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B] [IsIntegralClosure B A L]
    [FiniteDimensional K K₀] [FiniteDimensional K₀ L] [IsLocalRing K₀]
    (θ : K₀) (πL : L) (e f : ℕ) where
  O₀ : Subalgebra A K₀
  O₁ : Subalgebra A L
  O₀_eq_adjoin : O₀ = Algebra.adjoin A ({θ} : Set K₀)
  O₁_eq_adjoin : O₁ = Algebra.adjoin A
    ({algebraMap K₀ L θ, πL} : Set L)
  integral_ring_eq : Set.range (algebraMap B L) = (O₁ : Set L)
  theta_mem_O₀ : θ ∈ O₀
  piL_mem_O₁ : πL ∈ O₁
  O₁_local : IsLocalRing O₁
  O₁_dvr : IsDiscreteValuationRing O₁
  piL_generates_maximal_ideal :
    Ideal.span ({⟨πL, piL_mem_O₁⟩} : Set O₁) = IsLocalRing.maximalIdeal O₁
  O₀_local : IsLocalRing O₀
  pi₀ : O₀
  pi₀_generates_maximal_ideal :
    Ideal.span ({pi₀} : Set O₀) = IsLocalRing.maximalIdeal O₀
  first_polynomial : A[X]
  first_polynomial_monic : first_polynomial.Monic
  first_polynomial_root :
    aeval θ first_polynomial = 0
  first_derivative_is_unit :
    IsUnit (eval₂ (algebraMap A K₀) θ
      (Polynomial.derivative first_polynomial))
  first_derivative_is_unit_in_O₀ :
    IsUnit (eval₂ (algebraMap A O₀) ⟨θ, theta_mem_O₀⟩
      (Polynomial.derivative first_polynomial))
  first_degree : first_polynomial.natDegree = f
  second_polynomial : O₀[X]
  second_polynomial_monic : second_polynomial.Monic
  second_polynomial_root :
    eval₂ ((algebraMap K₀ L).comp (algebraMap O₀ K₀)) πL second_polynomial = 0
  second_polynomial_eisenstein :
    letI : IsLocalRing O₀ := O₀_local
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt pi₀ second_polynomial
  second_degree : second_polynomial.natDegree = e
  coordinate_expansion :
    ∀ x : L, x ∈ O₁ → ∃! c : Fin e → K₀,
      (∀ i, c i ∈ O₀) ∧
        x = ∑ i, algebraMap K₀ L (c i) * πL ^ (i : ℕ)
  coefficient_expansion :
    ∀ c : K₀, c ∈ O₀ → ∃! d : Fin f → A,
      c = ∑ j, algebraMap A K₀ (d j) * θ ^ (j : ℕ)
  field_degree : Module.finrank K L = e * f
  basis : Module.Basis (Fin f × Fin e) A B
  basis_apply :
    ∀ ji, algebraMap B L (basis ji) =
      algebraMap K₀ L (θ ^ (ji.1 : ℕ)) * πL ^ (ji.2 : ℕ)
  basis_in_O₁ :
    ∀ ji, algebraMap B L (basis ji) ∈ O₁

/-- The coordinate statements and the explicit monomial set extracted from a
two-stage presentation. -/
theorem chapter09_two_stage_coordinates
    (A B K K₀ L : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [IsLocalRing A]
    [Field K] [Field K₀] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K K₀] [Algebra A K₀]
    [Algebra K₀ L] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K K₀] [IsScalarTower K K₀ L]
    [IsScalarTower A K L] [IsScalarTower A K₀ L] [IsScalarTower A B L]
    [IsLocalHom (algebraMap A B)] [IsFractionRing B L]
    [IsDomain B] [IsLocalRing B] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing A] [Module.Finite A B]
    [Module.IsTorsionFree A B] [FaithfulSMul A B] [IsIntegralClosure B A L]
    [FiniteDimensional K K₀] [FiniteDimensional K₀ L] [IsLocalRing K₀]
    (θ : K₀) (πL : L) (e f : ℕ)
    (d : Chapter09TwoStageIntegralDescription A B K K₀ L θ πL e f) :
    (∀ x : L, x ∈ d.O₁ → ∃! c : Fin e → K₀,
      (∀ i, c i ∈ d.O₀) ∧
        x = ∑ i, algebraMap K₀ L (c i) * πL ^ (i : ℕ)) ∧
    (∀ c : K₀, c ∈ d.O₀ → ∃! q : Fin f → A,
      c = ∑ j, algebraMap A K₀ (q j) * θ ^ (j : ℕ)) ∧
    ∀ ji, algebraMap B L (d.basis ji) ∈
      chapter09ExplicitIntegralBasis K₀ L θ πL f e := by
  refine ⟨d.coordinate_expansion, d.coefficient_expansion, ?_⟩
  intro ji
  exact ⟨ji.1, ji.2, d.basis_apply ji⟩

/-- Existence interface for the two-stage integral description under the
separable-residue hypothesis.  The local-field and finite-dimensional
hypotheses are explicit so later proof passes can identify the abstract
presentation with the valuation rings of K₀ and L. -/
theorem chapter09_two_stage_integral_description_exists
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B] [IsLocalRing A] [IsLocalRing B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsLocalHom (algebraMap A B)] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FaithfulSMul A B] [IsIntegralClosure B A L]
    [Module.Finite (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)]
    [Chapter09FiniteLocalExtension A B K L]
    (d : Chapter09Corollary92Data A B K L)
    [FiniteDimensional K d.K₀] [FiniteDimensional d.K₀ L]
    [Algebra A d.K₀]
    [IsScalarTower A K d.K₀]
    [IsScalarTower A d.K₀ L]
    (hseparable : Algebra.IsSeparable (chapter09BaseResidueField A)
      (chapter09ExtensionResidueField B)) :
    ∃ (θ : d.K₀) (πL : L) (e f : ℕ),
      Nonempty (Chapter09TwoStageIntegralDescription A B K d.K₀ L
        θ πL e f) := by
  sorry

/-- The coordinate basis has e*f vectors, realizing the multiplicative
degree allocation at the level of coordinates. -/
theorem chapter09_two_stage_basis_cardinality
    (e f : ℕ) :
    Fintype.card (Fin f × Fin e) = f * e := by
  simp [Fintype.card_prod]

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09
