import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section04AnExampleOfSplittingAfterCompletion

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

/-! # Book 1, Chapter 12, Section 12.5: Unique Extension and Henselianity
-/

/-! ## 12.5. Henselian uniqueness -/


/-- Uniqueness for every algebraic extension. -/
def hasUniqueExtensionToEveryAlgebraicField
    {K Γ : Type u} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra K E] [Algebra.IsAlgebraic K E],
    hasUniqueValuationExtension v E

/-- Uniqueness to the fixed algebraic closure. -/
def hasUniqueExtensionToAlgebraicClosure
    {K Γ : Type u} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : Prop :=
  hasUniqueValuationExtension v (AlgebraicClosure K)

/-- Locality of the integral closure in every finite field extension. -/
def allFiniteIntegralClosuresAreLocal
    {K Γ : Type u} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra K E] [Module.Finite K E]
    [Algebra v.valuationSubring E]
    [IsScalarTower v.valuationSubring K E],
    IsLocalRing (integralClosure v.valuationSubring E)

/-- A finite product of local rings, allowing the factors to vary with the index. -/
structure Chapter12FiniteLocalProductData (C : Type u) [CommRing C] where
  index : Type u
  [finite_index : Fintype index]
  factor : index → Type u
  [factor_ring : ∀ i, CommRing (factor i)]
  [factor_local : ∀ i, IsLocalRing (factor i)]
  equivalence : Nonempty (C ≃+* (∀ i, factor i))

def IsFiniteProductOfLocalRings (C : Type u) [CommRing C] : Prop :=
  Nonempty (Chapter12FiniteLocalProductData C)

/-- Every finite commutative algebra is a product of local rings. -/
def allFiniteAlgebrasAreLocalProducts
    (A : Type u) [CommRing A] : Prop :=
  ∀ (C : Type u) [CommRing C] [Algebra A C] [Module.Finite A C],
    IsFiniteProductOfLocalRings C

/-- The extension of the base maximal ideal to a finite algebra. -/
def baseMaximalIdealExtension
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C] [IsLocalRing A] : Ideal C :=
  (IsLocalRing.maximalIdeal A).map (algebraMap A C)

/-- Reduction of an idempotent modulo the extended maximal ideal. -/
def idempotentReduction
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C] [IsLocalRing A]
    (e : IdempotentElement C) :
    IdempotentElement (C ⧸ baseMaximalIdealExtension A C) :=
  ⟨Ideal.Quotient.mk _ e.1, by
    change Ideal.Quotient.mk _ (e.1 * e.1) = Ideal.Quotient.mk _ e.1
    rw [e.2]⟩

/-- Idempotents lift uniquely over a henselian local base. -/
theorem henselian_idempotent_lifting
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C]
    [Module.Finite A C] [HenselianLocalRing A] :
    Function.Bijective (idempotentReduction A C) := by
  sorry

/-- An idempotent in the Jacobson radical is zero. -/
theorem idempotent_in_jacobson_is_zero
    {C : Type*} [CommRing C] (z : C)
    (hz : z * z = z) (hzJ : z ∈ Ideal.jacobson (⊥ : Ideal C)) :
    z = 0 := by
  classical
  by_cases hC : Nontrivial C
  · let _ : Nontrivial C := hC
    have hu : IsUnit (1 - z) := by
      convert (Ideal.mem_jacobson_bot.mp hzJ) (-1) using 1; ring
    have hprod : z * (1 - z) = 0 := by
      rw [mul_sub, mul_one, hz, sub_self]
    exact hu.mul_right_cancel (by simpa using hprod)
  · let _ : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    exact Subsingleton.elim z 0


/-- The complementary projector argument produces orthogonal primitive idempotents. -/
theorem henselian_finite_algebra_has_orthogonal_idempotents
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C]
    [Module.Finite A C] [HenselianLocalRing A] :
    ∃ n : ℕ, 0 < n ∧ ∃ e : Fin n → IdempotentElement C,
      (∀ i j, i ≠ j → (e i).1 * (e j).1 = 0) ∧
      (∑ i, (e i).1) = 1 ∧
      (∀ i (z : C), z * z = z → z * (e i).1 = z →
        z = 0 ∨ z = (e i).1) := by
  sorry

/-- Henselian finite algebras split into local factors. -/
theorem henselian_finite_algebra_is_local_product
    (A C : Type*) [CommRing A] [CommRing C] [Algebra A C]
    [Module.Finite A C] [HenselianLocalRing A] :
    IsFiniteProductOfLocalRings C := by
  sorry

/-- The center of an extension valuation on an integral closure. -/
def extendedValuationCenter
    {E Γ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation E Γ) (C : Type*) [CommRing C] [Algebra C E] : Set C :=
  {x | w (algebraMap C E x) < 1}

/-- Integral elements over a valuation ring lie in every extending valuation ring. -/
theorem integral_closure_lies_in_extension_valuation_ring
    {A E Γ : Type*} [CommRing A] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra A E]
    (w : Valuation E Γ) (x : integralClosure A E)
    (hintegers : w.Integers A)
    (hx : IsIntegral A (algebraMap (integralClosure A E) E x)) :
    w (algebraMap (integralClosure A E) E x) ≤ 1 := by
  exact hintegers.isIntegral_iff_v_le_one.mp hx

/-- Maximal ideals of integral closures are the centers of extended valuations. -/
theorem integral_closure_maximal_ideals_are_valuation_centers
    {K E Γ : Type*} [Field K] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K E]
    (v : Valuation K Γ) (w : Valuation E Γ) [v.HasExtension w]
    [Algebra v.valuationSubring E]
    [IsScalarTower v.valuationSubring K E]
    [IsLocalRing (integralClosure v.valuationSubring E)] :
    extendedValuationCenter w (integralClosure v.valuationSubring E) =
      (IsLocalRing.maximalIdeal (integralClosure v.valuationSubring E) :
        Set (integralClosure v.valuationSubring E)) := by
  sorry

/-- The extension-center correspondence has both the valuation and maximal-ideal directions. -/
theorem integral_closure_extension_center_correspondence
    {K E Γ : Type u} [Field K] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K E]
    [Algebra.IsAlgebraic K E]
    (v : Valuation K Γ)
    [Algebra v.valuationSubring E]
    [IsScalarTower v.valuationSubring K E] :
    (∀ (W : HeterogeneousValuationExtension v E),
      ∃ P : Ideal (integralClosure v.valuationSubring E),
        P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal v.valuationSubring) ∧
          (P : Set (integralClosure v.valuationSubring E)) =
            heterogeneousValuationCenter v W) ∧
      (∀ (P : Ideal (integralClosure v.valuationSubring E)),
        P.IsMaximal → P.LiesOver (IsLocalRing.maximalIdeal v.valuationSubring) →
          ∃ W : HeterogeneousValuationExtension v E,
              (P : Set (integralClosure v.valuationSubring E)) =
                heterogeneousValuationCenter v W) := by
  sorry


/-- Two extensions to a finite field remain distinct after extension to an algebraic closure. -/
theorem distinct_finite_extensions_remain_distinct_in_algebraic_closure
    {K E Γ : Type u} [Field K] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K E] [Algebra.IsAlgebraic K E]
    (v : Valuation K Γ)
    (w₁ w₂ : HeterogeneousValuationExtension v E)
    (hne : ¬ (letI : LinearOrderedCommGroupWithZero w₁.valueGroup :=
        w₁.orderedValueGroup
      letI : LinearOrderedCommGroupWithZero w₂.valueGroup :=
        w₂.orderedValueGroup
      w₁.valuation.IsEquiv w₂.valuation))
    (ι : E →ₐ[K] AlgebraicClosure K) :
    ∃ W₁ W₂ : HeterogeneousValuationExtension v (AlgebraicClosure K),
      (letI : LinearOrderedCommGroupWithZero w₁.valueGroup :=
          w₁.orderedValueGroup
       letI : LinearOrderedCommGroupWithZero W₁.valueGroup :=
          W₁.orderedValueGroup
       w₁.valuation.IsEquiv (W₁.valuation.comap ι.toRingHom)) ∧
      (letI : LinearOrderedCommGroupWithZero w₂.valueGroup :=
          w₂.orderedValueGroup
       letI : LinearOrderedCommGroupWithZero W₂.valueGroup :=
          W₂.orderedValueGroup
       w₂.valuation.IsEquiv (W₂.valuation.comap ι.toRingHom)) ∧
      (letI : LinearOrderedCommGroupWithZero W₁.valueGroup :=
          W₁.orderedValueGroup
       letI : LinearOrderedCommGroupWithZero W₂.valueGroup :=
          W₂.orderedValueGroup
       ¬ W₁.valuation.IsEquiv W₂.valuation) := by
  sorry

/-- The four conditions in Theorem 12.2 are equivalent. -/
theorem henselian_uniqueness_criterion
    {K Γ : Type u} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    List.TFAE
      [HenselianLocalRing v.valuationSubring,
       hasUniqueExtensionToEveryAlgebraicField v,
       hasUniqueExtensionToAlgebraicClosure v,
       allFiniteIntegralClosuresAreLocal v] := by
  sorry

/-- Completeness supplies the henselian property for a complete valued field. -/
theorem complete_nonarchimedean_field_is_henselian
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [Valued K Γ] [CompleteSpace K] :
    HenselianLocalRing (Valued.v (R := K)).valuationSubring := by
  sorry

/-- Henselianity alone is the weaker condition used for uniqueness statements. -/
def HenselianButNotAdicallyComplete
    (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  HenselianLocalRing R ∧ ¬ IsAdicComplete (IsLocalRing.maximalIdeal R) R

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
