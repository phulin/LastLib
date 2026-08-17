import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section04CoefficientFieldsInEqualCharacteristicPrime
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.Basic

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Filter Ideal IsLocalRing Polynomial

noncomputable section

/-! # Book 1, Chapter 13, Section 13.5: Cohen rings: existence -/

universe u v w

/-- A `p`-lift of a residue field, without a completeness requirement. -/
def Chapter13IsPLift
    (D : Type u) [CommRing D] [IsLocalRing D]
    (k : Type v) [Field k] (p : ℕ) : Prop :=
  (∃ hdom : IsDomain D, @IsDiscreteValuationRing D _ hdom) ∧
    IsLocalRing.maximalIdeal D = Ideal.span {(p : D)} ∧
      Nonempty ((D ⧸ IsLocalRing.maximalIdeal D) ≃+* k)

/-- A complete `p`-lift, i.e. a Cohen ring. -/
def Chapter13IsCohenRing
    (C : Type u) [CommRing C] [IsLocalRing C]
    (k : Type v) [Field k] (p : ℕ) : Prop :=
  Chapter13IsPLift C k p ∧
    IsAdicComplete (IsLocalRing.maximalIdeal C) C

/-- A package for a Cohen ring when its carrier and class structures are witnesses. -/
structure Chapter13CohenRingWitness (k : Type u) [Field k] (p : ℕ) where
  carrier : Type v
  [commRing : CommRing carrier]
  [localRing : IsLocalRing carrier]
  property : Chapter13IsCohenRing carrier k p

/-- A package for a simple extension of `p`-lifts. -/
structure Chapter13PLiftExtensionData
    (D : Type u) [CommRing D] [IsLocalRing D]
    (k' k'' : Type v) [Field k'] [Field k''] (p : ℕ)
    (E : Type w) where
  [commRing : CommRing E]
  [localRing : IsLocalRing E]
  target : Chapter13IsPLift E k'' p
  map : D →+* E
  injective : Function.Injective map
  maxIdeal_map :
    Ideal.map map (IsLocalRing.maximalIdeal D) = IsLocalRing.maximalIdeal E
  source_residue :
    (D ⧸ IsLocalRing.maximalIdeal D) ≃+* k'
  target_residue :
    (E ⧸ IsLocalRing.maximalIdeal E) ≃+* k''
  residue_map : k' →+* k''
  residue_map_injective : Function.Injective residue_map
  residue_compatibility :
    ∀ d : D,
      target_residue (Ideal.Quotient.mk (IsLocalRing.maximalIdeal E) (map d)) =
        residue_map (source_residue (Ideal.Quotient.mk (IsLocalRing.maximalIdeal D) d))

/-- The carrier used for the transcendental successor step. -/
noncomputable def Chapter13TranscendentalPLiftCarrier
    (D : Type u) [CommRing D] (p : ℕ)
    (hprime : (Ideal.span {(p : Polynomial D)}).IsPrime) : Type u := by
  letI : (Ideal.span {(p : Polynomial D)}).IsPrime := hprime
  exact Localization.AtPrime (Ideal.span {(p : Polynomial D)})

/-- The quotient carrier used for an algebraic successor step. -/
abbrev Chapter13AlgebraicPLiftCarrier
    (D : Type u) [CommRing D] (f : Polynomial D) : Type u :=
  Polynomial D ⧸ Ideal.span {f}

/-- Completing a `p`-lift produces a Cohen ring and preserves all finite quotients. -/
theorem chapter13_complete_p_lift
    {D : Type u} [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    {k : Type v} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hD : Chapter13IsPLift D k p) :
    Chapter13IsCohenRing (AdicCompletion (IsLocalRing.maximalIdeal D) D) k p ∧
      Function.Injective
        (algebraMap D (AdicCompletion (IsLocalRing.maximalIdeal D) D)) ∧
      ∀ n : ℕ, Nonempty
        ((D ⧸ (IsLocalRing.maximalIdeal D) ^ n) ≃+*
          (AdicCompletion (IsLocalRing.maximalIdeal D) D ⧸
            (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal D) D)) ^ n)) := by
  sorry

/-- Transcendental adjoining preserves the `p`-lift property by localization at `p`. -/
theorem chapter13_transcendental_simple_p_lift_extension
    {D : Type u} [CommRing D] [IsLocalRing D]
    {k' k'' : Type v} [Field k'] [Field k''] [Algebra k' k'']
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k' p] [CharP k'' p]
    (hD : Chapter13IsPLift D k' p)
    (x : k'') (hgen : Algebra.adjoin k' ({x} : Set k'') = ⊤)
    (htrans : Transcendental k' x)
    (hprime : (Ideal.span {(p : Polynomial D)}).IsPrime) :
    Nonempty (Chapter13PLiftExtensionData D k' k'' p
      (Chapter13TranscendentalPLiftCarrier D p hprime)) := by
  sorry

/-- Algebraic adjoining preserves the `p`-lift property by a monic polynomial quotient. -/
theorem chapter13_algebraic_simple_p_lift_extension
    {D : Type u} [CommRing D] [IsLocalRing D]
    {k' k'' : Type v} [Field k'] [Field k''] [Algebra k' k'']
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k' p] [CharP k'' p]
    (hD : Chapter13IsPLift D k' p)
    (x : k'') (hgen : Algebra.adjoin k' ({x} : Set k'') = ⊤)
    (halg : IsAlgebraic k' x)
    (e : (D ⧸ IsLocalRing.maximalIdeal D) ≃+* k')
    (f : Polynomial D) (hf : f.Monic)
    (hf_residue :
      Polynomial.map
          (e.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal D))) f =
        minpoly k' x) :
    Nonempty (Chapter13PLiftExtensionData D k' k'' p
      (Chapter13AlgebraicPLiftCarrier D f)) := by
  sorry

/-- A directed compatible family of `p`-lifts whose union is a common carrier. -/
structure Chapter13IncreasingPLiftChain
    (ι : Type u) (D : Type v) [CommRing D]
    (k : Type v) [Field k] (p : ℕ) where
  stage : ι → Subring D
  stage_local : ∀ i, IsLocalRing (stage i)
  stage_is_p_lift : ∀ i,
    @Chapter13IsPLift (stage i) _ (stage_local i) k _ p
  residue_equiv : ∀ i,
    (stage i ⧸ @IsLocalRing.maximalIdeal (stage i) _ (stage_local i)) ≃+* k
  directed : ∀ i j, ∃ l, stage i ≤ stage l ∧ stage j ≤ stage l
  union_is_top : ⋃ i, (stage i : Set D) = Set.univ
  maxIdeal_compatibility :
    ∀ i j (hij : stage i ≤ stage j),
      Ideal.map (Subring.inclusion hij)
          (@IsLocalRing.maximalIdeal (stage i) _ (stage_local i)) =
        @IsLocalRing.maximalIdeal (stage j) _ (stage_local j)
  residue_compatibility :
    ∀ i j (hij : stage i ≤ stage j) (d : stage i),
      residue_equiv j
          (Ideal.Quotient.mk (@IsLocalRing.maximalIdeal (stage j) _ (stage_local j))
            (Subring.inclusion hij d)) =
        residue_equiv i
          (Ideal.Quotient.mk (@IsLocalRing.maximalIdeal (stage i) _ (stage_local i)) d)

/-- Increasing unions of compatible `p`-lifts are again `p`-lifts. -/
theorem chapter13_increasing_union_p_lifts
    {ι : Type u} {D k : Type v} [CommRing D] [IsLocalRing D] [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (chain : Chapter13IncreasingPLiftChain ι D k p) :
    Chapter13IsPLift D k p := by
  sorry

/-- Every field of characteristic `p` has a Cohen ring. -/
theorem chapter13_cohen_ring_exists
    (k : Type u) [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p] :
    Nonempty (Chapter13CohenRingWitness k p) := by
  sorry

/-- The standard Cohen ring of the prime field is the ring of `p`-adic integers. -/
theorem chapter13_padic_integers_are_cohen
    (p : ℕ) [Fact (Nat.Prime p)] :
    Chapter13IsCohenRing (PadicInt p) (ZMod p) p := by
  sorry

/-- A ramified complete DVR is not a Cohen ring for its residue field. -/
theorem chapter13_ramified_dvr_is_not_cohen
    {C : Type u} [CommRing C] [IsLocalRing C]
    {k : Type v} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hC : Chapter13IsPLift C k p)
    (hramified : IsLocalRing.maximalIdeal C ≠ Ideal.span {(p : C)}) :
    ¬Chapter13IsCohenRing C k p := by
  sorry

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
