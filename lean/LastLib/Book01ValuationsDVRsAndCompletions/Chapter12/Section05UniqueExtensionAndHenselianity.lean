import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section03IntegralElementsAreBounded
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section06AlgebraicConsequences

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

/-- Valuation extensions with a fixed target value group.  This auxiliary
interface is used by Book 2's branch bookkeeping. -/
def ValuationExtension
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (E : Type*) [Field E] [Algebra K E] : Type _ :=
  {w : Valuation E Γ // v.IsEquiv (w.comap (algebraMap K E))}

/-- The canonical heterogeneous extension type introduced in Chapter 10. -/
abbrev HeterogeneousValuationExtension
    {K Γ : Type u} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (E : Type u) [Field E] [Algebra K E] :=
  Chapter10.Chapter10HeterogeneousValuationExtension E v

/-- The prime center in the integral closure determined by an extension. -/
def heterogeneousValuationCenter
    {K E Γ : Type u} [Field K] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K E]
    (v : Valuation K Γ) [Algebra v.valuationSubring E]
    (W : HeterogeneousValuationExtension v E) :
    Set (integralClosure v.valuationSubring E) :=
  {x | letI : LinearOrderedCommGroupWithZero W.valueGroup := W.orderedValueGroup
    W.valuation (algebraMap (integralClosure v.valuationSubring E) E x) < 1}

/-- Uniqueness of the canonical Chapter 10 extension object. -/
abbrev hasUniqueValuationExtension
    {K Γ : Type u} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (E : Type u) [Field E] [Algebra K E] : Prop :=
  Chapter10.Chapter10HasUniqueValuationExtension (L := E) v


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
    (hintegers : w.Integers A) :
    w (algebraMap (integralClosure A E) E x) ≤ 1 := by
  exact hintegers.isIntegral_iff_v_le_one.mp x.property

/-- Maximal ideals of integral closures are the centers of extended valuations. -/
theorem integral_closure_maximal_ideals_are_valuation_centers
    {K E Γ : Type*} [Field K] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K E]
    [Algebra.IsAlgebraic K E]
    (v : Valuation K Γ) (w : Valuation E Γ) [v.HasExtension w]
    [Algebra v.valuationSubring E]
    [IsScalarTower v.valuationSubring K E]
    [IsLocalRing (integralClosure v.valuationSubring E)] :
    extendedValuationCenter w (integralClosure v.valuationSubring E) =
      (IsLocalRing.maximalIdeal (integralClosure v.valuationSubring E) :
        Set (integralClosure v.valuationSubring E)) := by
  let C := integralClosure v.valuationSubring E
  have bounded (x : C) : w (x : E) ≤ 1 := by
    have hxint : IsIntegral v.valuationSubring (x : E) := by
      exact x.property
    have hxtop : IsIntegral w.valuationSubring (x : E) := by
      refine IsIntegral.map_of_comp_eq
        (algebraMap v.valuationSubring w.valuationSubring) (RingHom.id E) ?_ hxint
      ext a
      change algebraMap w.valuationSubring E
          (algebraMap v.valuationSubring w.valuationSubring a) =
        algebraMap v.valuationSubring E a
      change ((algebraMap v.valuationSubring w.valuationSubring a :
          w.valuationSubring) : E) = algebraMap v.valuationSubring E a
      calc
        ((algebraMap v.valuationSubring w.valuationSubring a :
            w.valuationSubring) : E) = algebraMap K E (a : K) :=
          Valuation.HasExtension.coe_algebraMap_valuationSubring_eq v w a
        _ = algebraMap v.valuationSubring E a := by
          rw [IsScalarTower.algebraMap_apply v.valuationSubring K E]
          rfl
    have hxmem : (x : E) ∈ w.valuationSubring := by
      change (x : E) ∈ w.valuationSubring.toSubring
      exact LocalSubring.mem_of_isMax_of_isIntegral
        (R := w.valuationSubring.toLocalSubring)
        w.valuationSubring.isMax_toLocalSubring hxtop
    exact hxmem
  let P : Ideal C :=
    { carrier := {x | w (x : E) < 1}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        exact (w.map_add _ _).trans_lt (max_lt hx hy)
      smul_mem' := by
        intro x y hy
        change w ((x : E) * (y : E)) < 1
        rw [mul_comm]
        rw [map_mul]
        exact Left.mul_lt_one_of_lt_of_le hy (bounded x) }
  have hPprime : P.IsPrime := by
    rw [Ideal.isPrime_iff]
    constructor
    · intro htop
      have hone : (1 : C) ∈ P := by rw [htop]; trivial
      change w (1 : E) < 1 at hone
      simp at hone
    · intro x y hxy
      by_cases hx : x ∈ P
      · exact Or.inl hx
      · right
        by_contra hy
        have hxle : w (x : E) ≤ 1 := bounded x
        have hyle : w (y : E) ≤ 1 := bounded y
        have hxeq : w (x : E) = 1 := le_antisymm hxle (le_of_not_gt hx)
        have hyeq : w (y : E) = 1 := le_antisymm hyle (le_of_not_gt hy)
        change w ((x : E) * (y : E)) < 1 at hxy
        rw [map_mul, hxeq, hyeq, one_mul] at hxy
        exact (lt_irrefl 1) hxy
  have hPprime' : P.IsPrime := hPprime
  have hcomap : P.comap (algebraMap v.valuationSubring C) =
      IsLocalRing.maximalIdeal v.valuationSubring := by
    ext a
    have hcomp : algebraMap C E (algebraMap v.valuationSubring C a) =
        algebraMap v.valuationSubring E a := by
      rw [IsScalarTower.algebraMap_apply v.valuationSubring C E]
    change w (algebraMap C E (algebraMap v.valuationSubring C a)) < 1 ↔
      a ∈ IsLocalRing.maximalIdeal v.valuationSubring
    rw [hcomp]
    have hmap : algebraMap v.valuationSubring E a =
        algebraMap K E (a : K) := by
      rw [IsScalarTower.algebraMap_apply v.valuationSubring K E]
      rfl
    rw [hmap]
    rw [Valuation.HasExtension.val_map_lt_one_iff v w]
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa using
      (Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one
        (x := (a : K))
  have hPmax : P.IsMaximal := by
    exact @Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ _ _ _ _ _ P hPprime'
      (hcomap.symm ▸ IsLocalRing.maximalIdeal.isMaximal _)
  have hPeq : P = IsLocalRing.maximalIdeal C := IsLocalRing.eq_maximalIdeal hPmax
  have hPeqSet := congrArg (fun I : Ideal C => (I : Set C)) hPeq
  simpa [P, C, extendedValuationCenter] using hPeqSet

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
                heterogeneousValuationCenter v W) ∧
      (∀ W₁ W₂ : HeterogeneousValuationExtension v E,
        heterogeneousValuationCenter v W₁ = heterogeneousValuationCenter v W₂ →
          (letI : LinearOrderedCommGroupWithZero W₁.valueGroup :=
             W₁.orderedValueGroup
           letI : LinearOrderedCommGroupWithZero W₂.valueGroup :=
             W₂.orderedValueGroup
           W₁.valuation.IsEquiv W₂.valuation)) := by
  sorry


/-- Two extensions to a finite field remain distinct after extension to an algebraic closure. -/
theorem distinct_finite_extensions_remain_distinct_in_algebraic_closure
    {K E Γ : Type u} [Field K] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K E]
    [FiniteDimensional K E]
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
  let : Algebra E (AlgebraicClosure K) := ι.toRingHom.toAlgebra
  let : IsScalarTower K E (AlgebraicClosure K) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap K (AlgebraicClosure K) x =
      ι (algebraMap K E x)
    exact (ι.commutes x).symm
  obtain ⟨U₁⟩ :=
    Chapter10.chapter10_valuation_extension_exists_as_heterogeneous
      (L := AlgebraicClosure K) w₁.valuation
  obtain ⟨U₂⟩ :=
    Chapter10.chapter10_valuation_extension_exists_as_heterogeneous
      (L := AlgebraicClosure K) w₂.valuation
  have hcomp₁ :
      U₁.valuation.comap (algebraMap K (AlgebraicClosure K)) =
        (U₁.valuation.comap (algebraMap E (AlgebraicClosure K))).comap
          (algebraMap K E) := by
    ext x
    change U₁.valuation (algebraMap K (AlgebraicClosure K) x) =
      U₁.valuation (algebraMap E (AlgebraicClosure K) (algebraMap K E x))
    rw [← IsScalarTower.algebraMap_apply K E (AlgebraicClosure K)]
  have hcomp₂ :
      U₂.valuation.comap (algebraMap K (AlgebraicClosure K)) =
        (U₂.valuation.comap (algebraMap E (AlgebraicClosure K))).comap
          (algebraMap K E) := by
    ext x
    change U₂.valuation (algebraMap K (AlgebraicClosure K) x) =
      U₂.valuation (algebraMap E (AlgebraicClosure K) (algebraMap K E x))
    rw [← IsScalarTower.algebraMap_apply K E (AlgebraicClosure K)]
  let W₁ : HeterogeneousValuationExtension v (AlgebraicClosure K) :=
    { valueGroup := U₁.valueGroup
      orderedValueGroup := U₁.orderedValueGroup
      valuation := U₁.valuation
      isExtension := by
        rw [hcomp₁]
        exact w₁.isExtension.trans
          (U₁.isExtension.comap (algebraMap K E)) }
  let W₂ : HeterogeneousValuationExtension v (AlgebraicClosure K) :=
    { valueGroup := U₂.valueGroup
      orderedValueGroup := U₂.orderedValueGroup
      valuation := U₂.valuation
      isExtension := by
        rw [hcomp₂]
        exact w₂.isExtension.trans
          (U₂.isExtension.comap (algebraMap K E)) }
  have h₁ :
      w₁.valuation.IsEquiv
        (U₁.valuation.comap (algebraMap E (AlgebraicClosure K))) :=
    U₁.isExtension
  have h₂ :
      w₂.valuation.IsEquiv
        (U₂.valuation.comap (algebraMap E (AlgebraicClosure K))) :=
    U₂.isExtension
  refine ⟨W₁, W₂, ?_, ?_, ?_⟩
  · exact h₁
  · exact h₂
  · intro hEq
    apply hne
    have hEq' :
        (U₁.valuation.comap (algebraMap E (AlgebraicClosure K))).IsEquiv
          (U₂.valuation.comap (algebraMap E (AlgebraicClosure K))) := by
      exact hEq.comap (ι.toRingHom)
    exact h₁.trans (hEq'.trans h₂.symm)

/-- The four conditions in Theorem 12.2 are equivalent. -/
theorem henselian_uniqueness_criterion
    {K Γ : Type u} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    List.TFAE
      [Chapter09.HenselianFactorizationProperty v.valuationSubring,
       hasUniqueExtensionToEveryAlgebraicField v,
       hasUniqueExtensionToAlgebraicClosure v,
       allFiniteIntegralClosuresAreLocal v] := by
  sorry

/-- Completeness supplies the henselian property for a complete valued field. -/
theorem complete_nonarchimedean_field_is_henselian
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Valuation.RankOne v]
    (hcomplete : @CompleteSpace K (Valued.mk' v).toUniformSpace) :
    Chapter09.HenselianFactorizationProperty v.valuationSubring := by
  exact Chapter09.complete_valued_field_is_henselian v hcomplete

/-- Henselianity alone is the weaker condition used for uniqueness statements. -/
def HenselianButNotAdicallyComplete
    (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  Chapter09.HenselianFactorizationProperty R ∧
    ¬ IsAdicComplete (IsLocalRing.maximalIdeal R) R

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
