import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section03IntegralElementsAreBounded
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section06FiniteExtensionsOfCompleteFields
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
  constructor
  · intro W
    let C := integralClosure v.valuationSubring E
    have bounded (x : C) : W.valuation (x : E) ≤ 1 := by
      have hxint : IsIntegral v.valuationSubring (x : E) := x.property
      let f : v.valuationSubring →+* W.valuation.valuationSubring :=
        RingHom.codRestrict (algebraMap v.valuationSubring E)
          W.valuation.valuationSubring (by
            intro a
            rw [Valuation.mem_valuationSubring_iff]
            have ha_v : v (algebraMap v.valuationSubring K a) ≤ 1 :=
              (Valuation.valuationSubring.integers v).map_le_one a
            have ha' :=
              (W.isExtension.le_one_iff_le_one
                (x := algebraMap v.valuationSubring K a)).mp ha_v
            change W.valuation
                (algebraMap K E (algebraMap v.valuationSubring K a)) ≤ 1 at ha'
            simpa [IsScalarTower.algebraMap_apply v.valuationSubring K E] using ha')
      have hcomp :
          (algebraMap W.valuation.valuationSubring E).comp f =
            (RingHom.id E).comp (algebraMap v.valuationSubring E) := by
        ext a
        simp [f]
      have hxW : IsIntegral W.valuation.valuationSubring ((x : E)) := by
        simpa using
          (IsIntegral.map_of_comp_eq f (RingHom.id E) hcomp hxint)
      have hxmem : (x : E) ∈ W.valuation.valuationSubring := by
        change (x : E) ∈ W.valuation.valuationSubring.toSubring
        exact LocalSubring.mem_of_isMax_of_isIntegral
          (R := W.valuation.valuationSubring.toLocalSubring)
          W.valuation.valuationSubring.isMax_toLocalSubring hxW
      exact (Valuation.mem_valuationSubring_iff W.valuation (x : E)).mp hxmem
    let P : Ideal C :=
      { carrier := {x | W.valuation (x : E) < 1}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy
          exact (W.valuation.map_add _ _).trans_lt (max_lt hx hy)
        smul_mem' := by
          intro x y hy
          change W.valuation ((x : E) * (y : E)) < 1
          rw [mul_comm, map_mul]
          exact Left.mul_lt_one_of_lt_of_le hy (bounded x) }
    have hPprime : P.IsPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      · intro htop
        have hone : (1 : C) ∈ P := by rw [htop]; trivial
        change W.valuation (1 : E) < 1 at hone
        simp at hone
      · intro x y hxy
        by_cases hx : x ∈ P
        · exact Or.inl hx
        · right
          by_contra hy
          have hxle : W.valuation (x : E) ≤ 1 := bounded x
          have hyle : W.valuation (y : E) ≤ 1 := bounded y
          have hxeq : W.valuation (x : E) = 1 :=
            le_antisymm hxle (le_of_not_gt hx)
          have hyeq : W.valuation (y : E) = 1 :=
            le_antisymm hyle (le_of_not_gt hy)
          change W.valuation ((x : E) * (y : E)) < 1 at hxy
          rw [map_mul, hxeq, hyeq, one_mul] at hxy
          exact (lt_irrefl 1) hxy
    have hcomap : P.comap (algebraMap v.valuationSubring C) =
        IsLocalRing.maximalIdeal v.valuationSubring := by
      ext a
      have hcomp : algebraMap C E (algebraMap v.valuationSubring C a) =
          algebraMap v.valuationSubring E a := by
        rw [IsScalarTower.algebraMap_apply v.valuationSubring C E]
      change W.valuation (algebraMap C E (algebraMap v.valuationSubring C a)) < 1 ↔
        a ∈ IsLocalRing.maximalIdeal v.valuationSubring
      rw [hcomp]
      have hmap : algebraMap v.valuationSubring E a =
          algebraMap K E (a : K) := by
        rw [IsScalarTower.algebraMap_apply v.valuationSubring K E]
        rfl
      rw [hmap]
      have hW : W.valuation (algebraMap K E (a : K)) < 1 ↔ v (a : K) < 1 :=
        (W.isExtension.lt_one_iff_lt_one (x := (a : K))).symm
      rw [hW]
      rw [ValuationSubring.valuation_lt_one_iff]
      exact
        (Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one
          (x := (a : K))
    have hPmax : P.IsMaximal := by
      exact @Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ _ _ _ _ _ P hPprime
        (hcomap.symm ▸ IsLocalRing.maximalIdeal.isMaximal _)
    refine ⟨P, hPmax, ?_, ?_⟩
    · exact ⟨hcomap.symm⟩
    · ext x
      rfl
  · constructor
    · intro P hPmax hPlies
      let C := integralClosure v.valuationSubring E
      have hPover : P.comap (algebraMap v.valuationSubring C) =
          IsLocalRing.maximalIdeal v.valuationSubring := hPlies.over.symm
      let f : C →+* E := algebraMap C E
      have hf : Function.Injective f :=
        IsIntegralClosure.algebraMap_injective C v.valuationSubring E
      let R : Subring E := f.range
      let e : C ≃+* R :=
        RingEquiv.ofBijective f.rangeRestrict
          ⟨fun x y hxy =>
              hf (congrArg (fun z : R => (z : E)) hxy), f.rangeRestrict_surjective⟩
      let I : Ideal R := Ideal.map e.toRingHom P
      let : P.IsPrime := hPmax.isPrime
      let : I.IsPrime := Ideal.map_isPrime_of_equiv e
      let A_P : LocalSubring E := LocalSubring.ofPrime R I
      obtain ⟨V, hV⟩ := A_P.exists_le_valuationSubring
      have hcontract : ∀ x : K,
          algebraMap K E x ∈ V.toSubring ↔ x ∈ v.valuationSubring.toSubring := by
        intro x
        constructor
        · intro hxV
          by_contra hx
          have hx0 : x ≠ 0 := by
            intro hx0
            apply hx
            simp [hx0]
          have hxinv : x⁻¹ ∈ v.valuationSubring.toSubring :=
            (v.valuationSubring.mem_or_inv_mem x).resolve_left hx
          obtain ⟨a, ha⟩ :=
            (Valuation.valuationSubring.integers v).exists_of_le_one
              ((Valuation.mem_valuationSubring_iff v x⁻¹).mp hxinv)
          have hana : ¬ IsUnit a := by
            intro hua
            obtain ⟨a', ha'⟩ := isUnit_iff_exists_inv.mp hua
            have ha'K : algebraMap v.valuationSubring K a *
                algebraMap v.valuationSubring K a' = 1 := by
              simpa only [map_mul, map_one] using
                congrArg (algebraMap v.valuationSubring K) ha'
            have hmul : x⁻¹ * algebraMap v.valuationSubring K a' = 1 := by
              simpa [ha] using ha'K
            have hax : algebraMap v.valuationSubring K a' = x := by
              have hmul' := congrArg (fun z : K => x * z) hmul
              simpa [mul_assoc, hx0] using hmul'
            apply hx
            change v x ≤ 1
            rw [← hax]
            exact (Valuation.valuationSubring.integers v).map_le_one a'
          have hamax : a ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            exact hana
          have haP' : a ∈ P.comap (algebraMap v.valuationSubring C) := by
            rw [hPover]
            exact hamax
          have haP : algebraMap v.valuationSubring C a ∈ P :=
            Ideal.mem_comap.mp haP'
          have hI : e (algebraMap v.valuationSubring C a) ∈ I :=
            Ideal.mem_map_of_mem e.toRingHom haP
          have hAPmax : algebraMap R A_P.toSubring
                (e (algebraMap v.valuationSubring C a)) ∈
              IsLocalRing.maximalIdeal A_P.toSubring :=
            (IsLocalization.AtPrime.to_map_mem_maximal_iff
              A_P.toSubring I _).2 hI
          let : IsLocalRing V.toLocalSubring.toSubring := V.toLocalSubring.isLocalRing
          let : IsLocalHom (Subring.inclusion hV.1) := hV.2
          have hVmax : Subring.inclusion hV.1
                (algebraMap R A_P.toSubring
                  (e (algebraMap v.valuationSubring C a))) ∈
              IsLocalRing.maximalIdeal V.toLocalSubring.toSubring := by
            rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff,
              ← IsLocalRing.mem_maximalIdeal]
            exact hAPmax
          let z : V.toLocalSubring.toSubring :=
            Subring.inclusion hV.1
              (algebraMap R A_P.toSubring
                (e (algebraMap v.valuationSubring C a)))
          have hz : (z : E) = (algebraMap K E x)⁻¹ := by
            change algebraMap C E (algebraMap v.valuationSubring C a) = _
            calc
              algebraMap C E (algebraMap v.valuationSubring C a) =
                  algebraMap v.valuationSubring E a :=
                (IsScalarTower.algebraMap_apply v.valuationSubring C E a).symm
              _ = algebraMap K E (algebraMap v.valuationSubring K a) :=
                IsScalarTower.algebraMap_apply v.valuationSubring K E a
              _ = algebraMap K E (x⁻¹) := by rw [ha]
              _ = (algebraMap K E x)⁻¹ := by rw [map_inv₀]
          have hzmax : z ∈ IsLocalRing.maximalIdeal V.toLocalSubring.toSubring := by
            simpa [z] using hVmax
          have hznonunit : ¬ IsUnit z := by
            rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
            exact hzmax
          have hx0E : algebraMap K E x ≠ 0 := by
            intro hzero
            apply hx0
            exact (FaithfulSMul.algebraMap_injective K E) (by simpa using hzero)
          let y' : V.toLocalSubring.toSubring := ⟨algebraMap K E x, hxV⟩
          have hunit : IsUnit z := by
            apply isUnit_iff_exists_inv.mpr
            refine ⟨y', ?_⟩
            apply Subtype.ext
            change (z : E) * (algebraMap K E x) = 1
            rw [hz]
            exact inv_mul_cancel₀ hx0E
          exact hznonunit hunit
        · intro hx
          obtain ⟨a, ha⟩ :=
            (Valuation.valuationSubring.integers v).exists_of_le_one
              ((Valuation.mem_valuationSubring_iff v x).mp hx)
          have hr : algebraMap C E (algebraMap v.valuationSubring C a) ∈ R :=
            ⟨algebraMap v.valuationSubring C a, rfl⟩
          have hAP : algebraMap C E (algebraMap v.valuationSubring C a) ∈ A_P.toSubring :=
            LocalSubring.le_ofPrime R I hr
          have hV' : algebraMap C E (algebraMap v.valuationSubring C a) ∈ V.toSubring :=
            hV.1 hAP
          have heq : algebraMap K E x =
              algebraMap C E (algebraMap v.valuationSubring C a) := by
            calc
              algebraMap K E x = algebraMap K E (algebraMap v.valuationSubring K a) := by
                rw [ha]
              _ = algebraMap v.valuationSubring E a :=
                (IsScalarTower.algebraMap_apply v.valuationSubring K E a).symm
              _ = algebraMap C E (algebraMap v.valuationSubring C a) :=
                IsScalarTower.algebraMap_apply v.valuationSubring C E a
          rw [heq]
          exact hV'
      have hwext : v.IsEquiv (V.valuation.comap (algebraMap K E)) :=
        Chapter10.chapter10_contracts_to_is_equiv v V hcontract
      let W' : HeterogeneousValuationExtension v E :=
        { valueGroup := V.ValueGroup
          valuation := V.valuation
          isExtension := hwext }
      refine ⟨W', ?_⟩
      ext b
      change b ∈ P ↔ W'.valuation (algebraMap C E b) < 1
      change b ∈ P ↔ V.valuation (algebraMap C E b) < 1
      let r : R := e b
      let z : A_P.toSubring := algebraMap R A_P.toSubring r
      let zV : V.toLocalSubring.toSubring := Subring.inclusion hV.1 z
      have hzunit : IsUnit zV ↔ IsUnit z := by
        let : IsLocalRing V.toLocalSubring.toSubring := V.toLocalSubring.isLocalRing
        let : IsLocalHom (Subring.inclusion hV.1) := hV.2
        exact isUnit_map_iff (Subring.inclusion hV.1) z
      let eV : V ≃+* V.toLocalSubring.toSubring :=
        { toFun := fun a => ⟨a, a.property⟩
          invFun := fun a => ⟨a, a.property⟩
          left_inv := by intro a; rfl
          right_inv := by intro a; rfl
          map_add' := by intros; rfl
          map_mul' := by intros; rfl }
      have hraw : V.valuation (algebraMap C E b) < 1 ↔ ¬ IsUnit zV := by
        let aV : V := ⟨algebraMap C E b, by
          change algebraMap C E b ∈ V.toLocalSubring.toSubring
          exact zV.property⟩
        have haV : V.valuation (algebraMap C E b) < 1 ↔ ¬ IsUnit aV := by
          rw [show algebraMap C E b = (aV : E) by rfl,
            ← V.mem_nonunits_iff,
            V.coe_mem_nonunits_iff,
            IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        have heV : eV aV = zV := by
          apply Subtype.ext
          rfl
        calc
          V.valuation (algebraMap C E b) < 1 ↔ ¬ IsUnit aV := haV
          _ ↔ ¬ IsUnit (eV aV) := by
            constructor
            · intro h hu
              exact h (hu.map eV.toRingHom)
            · intro h hu
              exact h (hu.map eV.symm.toRingHom)
          _ ↔ ¬ IsUnit zV := by rw [heV]
      rw [hraw, hzunit]
      have hnon : ¬ IsUnit z ↔ e b ∈ I := by
        have hzprime : IsUnit z ↔ e b ∈ I.primeCompl := by
          simpa [z, r, A_P] using
            (IsLocalization.AtPrime.isUnit_to_map_iff
              (LocalSubring.ofPrime R I).toSubring I (e b))
        rw [hzprime, Ideal.mem_primeCompl_iff]
        simp only [not_not]
      have heI : e b ∈ I ↔ b ∈ P := by
        constructor
        · intro hb
          rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hb with
            ⟨c, hc, hcb⟩
          exact e.injective hcb ▸ hc
        · intro hb
          exact Ideal.mem_map_of_mem e.toRingHom hb
      exact (hnon.trans heI).symm
    · intro W₁ W₂ hEq
      apply Valuation.isEquiv_of_val_le_one
      intro x
      obtain ⟨F, hxF, hF⟩ :=
        Chapter10.chapter10_algebraic_element_in_finite_subextension
          (K := K) (L := E) (Algebra.IsAlgebraic.isAlgebraic x)
      let : FiniteDimensional K F := hF
      let : Algebra v.valuationSubring F :=
        (algebraMap K F).comp (algebraMap v.valuationSubring K) |>.toAlgebra
      let : IsScalarTower v.valuationSubring K F := by
        apply IsScalarTower.of_algebraMap_eq'
        ext a
        rfl
      let : IsScalarTower v.valuationSubring F E := by
        apply IsScalarTower.of_algebraMap_eq'
        ext a
        rw [IsScalarTower.algebraMap_apply v.valuationSubring K E]
        change algebraMap K E (algebraMap v.valuationSubring K a) =
          algebraMap F E (algebraMap K F (algebraMap v.valuationSubring K a))
        rw [IsScalarTower.algebraMap_apply K F E]
      let w₁F : Valuation F W₁.valueGroup :=
        W₁.valuation.comap (algebraMap F E)
      let w₂F : Valuation F W₂.valueGroup :=
        W₂.valuation.comap (algebraMap F E)
      have h₁F : v.IsEquiv (w₁F.comap (algebraMap K F)) := by
        apply Valuation.isEquiv_of_val_le_one
        intro y
        change v y ≤ 1 ↔
          W₁.valuation (algebraMap F E (algebraMap K F y)) ≤ 1
        rw [← IsScalarTower.algebraMap_apply K F E]
        exact W₁.isExtension.le_one_iff_le_one
      have h₂F : v.IsEquiv (w₂F.comap (algebraMap K F)) := by
        apply Valuation.isEquiv_of_val_le_one
        intro y
        change v y ≤ 1 ↔
          W₂.valuation (algebraMap F E (algebraMap K F y)) ≤ 1
        rw [← IsScalarTower.algebraMap_apply K F E]
        exact W₂.isExtension.le_one_iff_le_one
      let W₁F : HeterogeneousValuationExtension v F :=
        { valueGroup := W₁.valueGroup
          valuation := w₁F
          isExtension := h₁F }
      let W₂F : HeterogeneousValuationExtension v F :=
        { valueGroup := W₂.valueGroup
          valuation := w₂F
          isExtension := h₂F }
      let C := integralClosure v.valuationSubring F
      let i : F →ₐ[v.valuationSubring] E :=
        IsScalarTower.toAlgHom v.valuationSubring F E
      let iC : C →ₐ[v.valuationSubring]
          (integralClosure v.valuationSubring E) := i.mapIntegralClosure
      have hcenter :
          Chapter10.chapter10_extension_center
              (A := v.valuationSubring) (B := C) (K := K) (L := F)
              v (Valuation.valuationSubring.integers v) W₁F =
            Chapter10.chapter10_extension_center
              (A := v.valuationSubring) (B := C) (K := K) (L := F)
              v (Valuation.valuationSubring.integers v) W₂F := by
        ext b
        simp only [Chapter10.chapter10_extension_center, Ideal.mem_comap,
          Valuation.mem_maximalIdeal_iff]
        let bE : integralClosure v.valuationSubring E := iC b
        have hbE := Set.ext_iff.mp hEq bE
        change W₁.valuation
              (algebraMap F E (algebraMap C F b)) < 1 ↔
            W₂.valuation
              (algebraMap F E (algebraMap C F b)) < 1
        have hbE' : W₁.valuation (bE : E) < 1 ↔
            W₂.valuation (bE : E) < 1 := by
          simpa [heterogeneousValuationCenter, Subalgebra.algebraMap_eq] using hbE
        have hbE_coe : (bE : E) = (b : E) := by
          change (iC b : E) = (b : E)
          rfl
        simpa [hbE_coe] using hbE'
      have hmap :
          Chapter10.chapter10_extension_center_map
              (A := v.valuationSubring) (B := C) (K := K) (L := F)
              v (Valuation.valuationSubring.integers v)
              (Quotient.mk _ W₁F) =
            Chapter10.chapter10_extension_center_map
              (A := v.valuationSubring) (B := C) (K := K) (L := F)
              v (Valuation.valuationSubring.integers v)
              (Quotient.mk _ W₂F) := by
        apply Subtype.ext
        simpa only [Chapter10.chapter10_extension_center_map,
          Quotient.lift_mk] using hcenter
      have hq :
          Quotient.mk (Chapter10.Chapter10ValuationExtensionSetoid (L := F) v) W₁F =
            Quotient.mk (Chapter10.Chapter10ValuationExtensionSetoid (L := F) v) W₂F := by
        apply
          (Chapter10.chapter10_extension_center_map_injective
            (A := v.valuationSubring) (B := C) (K := K) (L := F) v
            (Valuation.valuationSubring.integers v))
        exact hmap
      have hFEquiv : w₁F.IsEquiv w₂F := by
        exact Quotient.exact hq
      have hpoint := hFEquiv (⟨x, hxF⟩ : F) (1 : F)
      simpa [w₁F, w₂F] using hpoint


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

/-- The finite normalization locality interface in the standard Mathlib
    henselian-local-ring language.  This is the direct bridge used by later
    chapters when the base valuation ring is presented with
    `HenselianLocalRing`, rather than with Chapter 9's factorization predicate.
    The finiteness hypothesis is retained explicitly because it is the
    hypothesis under which the finite normalization is being considered. -/
theorem henselian_local_ring_integral_closure_is_local
    {A K L : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [HenselianLocalRing A]
    (_hfinite : Module.Finite A (integralClosure A L)) :
    IsLocalRing (integralClosure A L) := by
  let vA := ValuationRing.valuation A K
  let hA : vA.Integers A :=
    { hom_inj := IsFractionRing.injective A K
      map_le_one := by
        intro a
        rw [← Valuation.mem_integer_iff, ValuationRing.range_algebraMap_eq]
        exact ⟨a, rfl⟩
      exists_of_le_one := by
        intro x hx
        rw [← Valuation.mem_integer_iff, ValuationRing.range_algebraMap_eq] at hx
        rcases hx with ⟨a, ha⟩
        exact ⟨a, ha⟩ }
  let : IsIntegrallyClosed A := hA.isIntegrallyClosed
  let alg : A →+* vA.valuationSubring :=
    (algebraMap A K).codRestrict vA.valuationSubring
      (fun a => hA.map_le_one a)
  have halg_bij : Function.Bijective alg := by
    constructor
    · intro a b hab
      apply hA.hom_inj
      exact congrArg Subtype.val hab
    · intro x
      obtain ⟨a, ha⟩ := hA.exists_of_le_one x.property
      refine ⟨a, Subtype.ext ?_⟩
      exact ha
  let e : A ≃+* vA.valuationSubring := RingEquiv.ofBijective alg halg_bij
  let : IsLocalRing vA.valuationSubring := e.isLocalRing
  have hmaxmap :
      (IsLocalRing.maximalIdeal A).map e.toRingHom =
        IsLocalRing.maximalIdeal vA.valuationSubring :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  have hmaxmap_symm :
      (IsLocalRing.maximalIdeal vA.valuationSubring).map e.symm.toRingHom =
        IsLocalRing.maximalIdeal A :=
    IsLocalRing.map_ringEquiv_maximalIdeal e.symm
  let : HenselianLocalRing vA.valuationSubring := by
    refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
    intro f hf a₀ hfa hunit
    let fA := f.map e.symm.toRingHom
    have hfA : fA.Monic := hf.map e.symm.toRingHom
    have hmap_eval' :
        fA.eval (e.symm a₀) = e.symm (f.eval a₀) := by
      simpa [fA] using
        (Polynomial.eval_map_apply (p := f) e.symm.toRingHom a₀)
    have hmap_eval : e (fA.eval (e.symm a₀)) = f.eval a₀ := by
      rw [hmap_eval']
      simp
    have hfaA : fA.eval (e.symm a₀) ∈ IsLocalRing.maximalIdeal A := by
      have hfa' := Ideal.mem_map_of_mem e.symm.toRingHom hfa
      rw [hmaxmap_symm] at hfa'
      have hfa'' : e.symm (f.eval a₀) ∈ IsLocalRing.maximalIdeal A := by
        simpa using hfa'
      rw [← hmap_eval] at hfa''
      simpa using hfa''
    have hunitA : IsUnit (fA.derivative.eval (e.symm a₀)) := by
      have hder' :
          fA.derivative.eval (e.symm a₀) =
            e.symm (f.derivative.eval a₀) := by
        dsimp [fA]
        rw [Polynomial.derivative_map]
        exact Polynomial.eval_map_apply (p := f.derivative) e.symm.toRingHom a₀
      have hunit' := hunit.map e.symm.toRingHom
      change IsUnit (e.symm (f.derivative.eval a₀)) at hunit'
      rw [← hder'] at hunit'
      exact hunit'
    obtain ⟨aA, haA, hdiffA⟩ :=
      HenselianLocalRing.is_henselian fA hfA (e.symm a₀) hfaA hunitA
    refine ⟨e aA, ?_, ?_⟩
    · have hrootmap : e (fA.eval aA) = f.eval (e aA) := by
        have hroot' :
            fA.eval aA = e.symm (f.eval (e aA)) := by
          simpa [fA] using
            (Polynomial.eval_map_apply (p := f) e.symm.toRingHom (e aA))
        rw [hroot']
        simp
      change f.eval (e aA) = 0
      rw [← hrootmap, haA]
      simp
    · have hdiff' := Ideal.mem_map_of_mem e.toRingHom hdiffA
      rw [hmaxmap] at hdiff'
      simpa [map_sub] using hdiff'
  have hH : Chapter10.Chapter10IsHenselianValuedField vA := by
    exact Chapter09.mathlib_henselian_valuation_ring_implies_factorization
      (A := A) (K := K)
  let C := integralClosure A L
  have hunique : Chapter10.Chapter10HasUniquePrimeAbove (A := A) (B := C) := by
    exact Chapter10.chapter10_henselian_valuation_ring_has_unique_prime_above
      (A := A) (B := C) (K := K) (L := L) vA hA hH
  have hmap_inj : Function.Injective (algebraMap A C) := by
    intro a b hab
    apply hA.hom_inj
    apply FaithfulSMul.algebraMap_injective K L
    rw [← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply A K L]
    have habL := congrArg (fun x : C => (x : L)) hab
    change algebraMap C L (algebraMap A C a) =
        algebraMap C L (algebraMap A C b) at habL
    rw [← IsScalarTower.algebraMap_apply A C L,
      ← IsScalarTower.algebraMap_apply A C L] at habL
    exact habL
  let : FaithfulSMul A C :=
    (faithfulSMul_iff_algebraMap_injective A C).mpr hmap_inj
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := A) (S := C) (IsLocalRing.maximalIdeal A)
  have hPabove : Chapter10.Chapter10PrimeAboveMaximal (A := A) (B := C) P :=
    ⟨hPmax.isPrime, hPover.over.symm⟩
  refine IsLocalRing.of_unique_max_ideal ⟨P, hPmax, ?_⟩
  intro Q hQmax
  have hQcomapmax :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (R := A) (S := C) Q
  have hQabove : Chapter10.Chapter10PrimeAboveMaximal (A := A) (B := C) Q :=
    ⟨hQmax.isPrime, IsLocalRing.eq_maximalIdeal hQcomapmax⟩
  obtain ⟨P₀, hP₀, hPuniq⟩ := hunique
  exact (hPuniq Q hQabove).trans (hPuniq P hPabove).symm

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
