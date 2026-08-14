import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section04HenselianLocalRings
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Unbundled.FiniteExtension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

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

/-! # Book 1, Chapter 10, Section 10.1: The Extension Problem
-/

/-! ## 10.1. The extension problem -/

/-- The valuation ring attached to a valuation. -/
def Chapter10ValuationRing {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) : Subring K :=
  v.valuationSubring.toSubring

/-- A valuation extension, expressed using Mathlib's equivalence notion. -/
def Chapter10ValuationExtension {K L Γ₀ Δ₀ : Type*}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Δ₀]
    (v : Valuation K Γ₀) (w : Valuation L Δ₀) : Prop :=
  Valuation.HasExtension v w

/-- A valuation extension may use a genuinely different ordered value group.
This is the canonical heterogeneous extension type for the rest of Book 1. -/
structure Chapter10HeterogeneousValuationExtension
    {K : Type u10K} (L : Type u10L) {ΓK : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) where
  valueGroup : Type (max (max u10K u10L) u10Γ)
  [orderedValueGroup : LinearOrderedCommGroupWithZero valueGroup]
  valuation : Valuation L valueGroup
  isExtension : vK.IsEquiv (valuation.comap (algebraMap K L))

instance {K : Type u10K} {L : Type u10L} {ΓK : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    {vK : Valuation K ΓK}
    (W : Chapter10HeterogeneousValuationExtension L vK) :
    LinearOrderedCommGroupWithZero W.valueGroup :=
  W.orderedValueGroup

/-- Equivalence of extensions is equivalence of their valuations, not equality
of chosen value groups or normalizations. -/
def Chapter10ValuationExtensionsEquivalent
    {K : Type u10K} {L : Type u10L} {ΓK : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK)
    (W₁ W₂ : Chapter10HeterogeneousValuationExtension L vK) : Prop :=
  W₁.valuation.IsEquiv W₂.valuation

def Chapter10ValuationExtensionSetoid
    {K : Type u10K} {L : Type u10L} {ΓK : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) :
    Setoid (Chapter10HeterogeneousValuationExtension L vK) where
  r := Chapter10ValuationExtensionsEquivalent vK
  iseqv := by
    constructor
    · intro W
      exact fun _ _ => Iff.rfl
    · intro W₁ W₂ h
      exact fun x y => Iff.symm (h x y)
    · intro W₁ W₂ W₃ h₁₂ h₂₃
      exact fun x y => Iff.trans (h₁₂ x y) (h₂₃ x y)

abbrev Chapter10ValuationExtensionClass
    {K : Type u10K} {L : Type u10L} {ΓK : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) :=
  Quotient (Chapter10ValuationExtensionSetoid (L := L) vK)

/-- A prime of an integral extension centered over the base maximal ideal. -/
def Chapter10PrimeAboveMaximal
    {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] (P : Ideal B) : Prop :=
  P.IsPrime ∧ P.comap (algebraMap A B) = IsLocalRing.maximalIdeal A

/-- Valuation branches and primes above the base maximal ideal correspond. -/
def Chapter10ExtensionPrimeCorrespondence
    {A B : Type*} {K : Type u10K} {L : Type u10L} {ΓK : Type u10Γ}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [IsIntegrallyClosed A]
    [Field K] [Field L] [CommRing B] [Algebra A B] [Algebra B L]
    [Algebra A L]
    [IsScalarTower A B L] [IsIntegralClosure B A L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L]
    [IsScalarTower A K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) (_hA : vK.Integers A) : Prop :=
  Nonempty
    (Chapter10ValuationExtensionClass (L := L) vK ≃
      {P : Ideal B // Chapter10PrimeAboveMaximal (A := A) (B := B) P})

def Chapter10HasUniqueValuationExtension
    {K : Type u10K} {L : Type u10L} {ΓK : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) : Prop :=
  Nonempty (Chapter10HeterogeneousValuationExtension L vK) ∧
    ∀ W₁ W₂ : Chapter10HeterogeneousValuationExtension L vK,
      Chapter10ValuationExtensionsEquivalent vK W₁ W₂

def Chapter10HasUniquePrimeAbove
    {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] : Prop :=
  ∃! P : Ideal B, Chapter10PrimeAboveMaximal (A := A) (B := B) P

/-- A valued field is henselian in the factorization sense fixed in Chapter 9. -/
def Chapter10IsHenselianValuedField
    {K : Type u10K} {ΓK : Type u10Γ} [Field K]
    [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) : Prop :=
  Chapter09.HenselianFactorizationProperty vK.valuationSubring

/-! A valuation on an extension is allowed to use its own ordered value group. -/

structure Chapter10ValuationOnField (L : Type*) [Field L] where
  valueGroup : Type*
  [orderedValueGroup : LinearOrderedCommGroupWithZero valueGroup]
  valuation : Valuation L valueGroup

instance {L : Type*} [Field L] (w : Chapter10ValuationOnField L) :
    LinearOrderedCommGroupWithZero w.valueGroup := w.orderedValueGroup


/-- Contraction of a valuation ring on L to the prescribed ring on K. -/
def Chapter10ContractsTo {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : Subring K) (W : Subring L) : Prop :=
  ∀ x : K, algebraMap K L x ∈ W ↔ x ∈ V

/-- Elements bounded by every valuation in a specified family. -/
def Chapter10BoundedAtValuations {L : Type*} [Field L]
    (E : Set (Chapter10ValuationOnField L)) : Set L :=
  {x | ∀ w, w ∈ E → x ∈ w.valuation.valuationSubring}

/-- The integral closure, named locally for traceability. -/
def Chapter10IntegralClosure (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Subalgebra R S :=
  integralClosure R S

/-- The set of elements integral over a base ring. -/
def Chapter10IntegralElements (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Set S :=
  {x | IsIntegral R x}

/-- A valuation-ring criterion used in the maximal-domination argument. -/
def Chapter10ValuationRingCriterion {L : Type*} [Field L]
    (R : Subring L) : Prop :=
  ∀ x : L, x ≠ 0 → x ∈ R ∨ x⁻¹ ∈ R

/-!
The maximal-domination proof uses pairs consisting of an overring and a prime
whose contraction is the maximal ideal of the original valuation ring.
-/

structure Chapter10DominationPair {K L : Type*} [Field K] [Field L]
    [Algebra K L] (V : Subring K) [IsLocalRing V] where
  carrier : Subring L
  contains : ∀ x : K, x ∈ V → algebraMap K L x ∈ carrier
  prime : Ideal carrier
  isPrime : prime.IsPrime
  contracts : ∀ (x : K) (hx : x ∈ V),
    (⟨algebraMap K L x, contains x hx⟩ : carrier) ∈ prime ↔
      (⟨x, hx⟩ : V) ∈ IsLocalRing.maximalIdeal V

/-- Domination of one pair by another. -/
def Chapter10DominationPair.Dominates
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (P Q : Chapter10DominationPair (K := K) (L := L) V) : Prop :=
  ∃ h : P.carrier ≤ Q.carrier, ∀ x : P.carrier,
    (⟨(x : L), h x.property⟩ : Q.carrier) ∈ Q.prime ↔ x ∈ P.prime

/-- A set of domination pairs is a chain. -/
def Chapter10DominationChain
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (C : Set (Chapter10DominationPair (K := K) (L := L) V)) : Prop :=
  ∀ P ∈ C, ∀ Q ∈ C,
      Chapter10DominationPair.Dominates P Q ∨
      Chapter10DominationPair.Dominates Q P

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
