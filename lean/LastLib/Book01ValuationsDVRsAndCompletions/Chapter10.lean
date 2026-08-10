import Mathlib

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

/-- Zorn upper bound for a domination chain. -/
theorem chapter10_domination_chain_upper_bound
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (C : Set (Chapter10DominationPair (K := K) (L := L) V))
    (hC : Chapter10DominationChain C) :
    ∃ Q : Chapter10DominationPair (K := K) (L := L) V, ∀ P ∈ C,
      Chapter10DominationPair.Dominates P Q := by
  classical
  let f : V →+* L := (algebraMap K L).comp V.subtype
  obtain ⟨W, hW, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  let fW := f.codRestrict W.toSubring hW
  let : IsLocalRing W.toSubring := W.toLocalSubring.isLocalRing
  let : IsLocalHom fW := hlocal
  let P₀ : Chapter10DominationPair (K := K) (L := L) V :=
    { carrier := W.toSubring
      contains := fun x hx => by
        change f ⟨x, hx⟩ ∈ W.toSubring
        exact hW ⟨x, hx⟩
      prime := IsLocalRing.maximalIdeal W.toSubring
      isPrime := Ideal.IsMaximal.isPrime
        (IsLocalRing.maximalIdeal.isMaximal W.toSubring)
      contracts := fun x hx => by
        change fW ⟨x, hx⟩ ∈ IsLocalRing.maximalIdeal W.toSubring ↔
          (⟨x, hx⟩ : V) ∈ IsLocalRing.maximalIdeal V
        rw [← IsLocalRing.maximalIdeal_comap fW]
        rfl }
  by_cases hCne : C.Nonempty
  · let : Nonempty C := hCne.to_subtype
    let B : Subring L := ⨆ P : C, P.1.carrier
    have hBdir : Directed (· ≤ ·) (fun P : C => P.1.carrier) := by
      intro P Q
      rcases hC P.1 P.2 Q.1 Q.2 with hPQ | hQP
      · exact ⟨Q, hPQ.1, le_rfl⟩
      · exact ⟨P, le_rfl, hQP.1⟩
    have hmemB {x : L} : x ∈ B ↔ ∃ P : C, x ∈ P.1.carrier := by
      exact Subring.mem_iSup_of_directed hBdir
    let Pbase : C := ⟨Classical.choose hCne, Classical.choose_spec hCne⟩
    have hcontainsB : ∀ x : K, x ∈ V → algebraMap K L x ∈ B := by
      intro x hx
      exact le_iSup (fun P : C => P.1.carrier) Pbase
        (Pbase.1.contains x hx)
    have hdom_refl (P : C) :
        Chapter10DominationPair.Dominates P.1 P.1 :=
      ⟨le_rfl, fun x => Iff.rfl⟩
    have hdom_trans {P Q R : C}
        (hPQ : Chapter10DominationPair.Dominates P.1 Q.1)
        (hQR : Chapter10DominationPair.Dominates Q.1 R.1) :
        Chapter10DominationPair.Dominates P.1 R.1 := by
      rcases hPQ with ⟨hPQ, hPQ'⟩
      rcases hQR with ⟨hQR, hQR'⟩
      refine ⟨fun x hx => hQR (hPQ hx), ?_⟩
      intro x
      rw [hQR' ⟨x, hPQ x.property⟩]
      exact hPQ' x
    have hupperdom (P Q : C) : ∃ R : C,
        Chapter10DominationPair.Dominates P.1 R.1 ∧
          Chapter10DominationPair.Dominates Q.1 R.1 := by
      rcases hC P.1 P.2 Q.1 Q.2 with hPQ | hQP
      · exact ⟨Q, hPQ, hdom_refl Q⟩
      · exact ⟨P, hdom_refl P, hQP⟩
    have hpush {P Q : C}
        (hPQ : Chapter10DominationPair.Dominates P.1 Q.1)
        {x : L} (hx : x ∈ P.1.carrier)
        (hxP : (⟨x, hx⟩ : P.1.carrier) ∈ P.1.prime) :
        ∃ hxQ : x ∈ Q.1.carrier,
          (⟨x, hxQ⟩ : Q.1.carrier) ∈ Q.1.prime := by
      rcases hPQ with ⟨hPQ, hPQ'⟩
      exact ⟨hPQ hx, (hPQ' ⟨x, hx⟩).mpr hxP⟩
    let J : Ideal B :=
      { carrier := {x | ∃ P : C, ∃ hx : (x : L) ∈ P.1.carrier,
          (⟨(x : L), hx⟩ : P.1.carrier) ∈ P.1.prime}
        zero_mem' := by
          refine ⟨Pbase, Pbase.1.carrier.zero_mem, ?_⟩
          exact Pbase.1.prime.zero_mem
        add_mem' := by
          intro x y hx hy
          rcases hx with ⟨P, hxP, hxP'⟩
          rcases hy with ⟨Q, hyQ, hyQ'⟩
          obtain ⟨R, hPR, hQR⟩ := hupperdom P Q
          obtain ⟨hxR, hxR'⟩ := hpush hPR hxP hxP'
          obtain ⟨hyR, hyR'⟩ := hpush hQR hyQ hyQ'
          refine ⟨R, R.1.carrier.add_mem hxR hyR, ?_⟩
          convert R.1.prime.add_mem hxR' hyR' using 1
          apply Subtype.ext
          rfl
        smul_mem' := by
          intro a x hx
          rcases hx with ⟨P, hxP, hxP'⟩
          obtain ⟨Q, haQ⟩ := hmemB.mp a.property
          obtain ⟨R, hPR, hQR⟩ := hupperdom P Q
          obtain ⟨hxR, hxR'⟩ := hpush hPR hxP hxP'
          rcases hQR with ⟨hQR, _⟩
          have haR : (a : L) ∈ R.1.carrier := hQR haQ
          refine ⟨R, R.1.carrier.mul_mem haR hxR, ?_⟩
          convert R.1.prime.mul_mem_left (⟨(a : L), haR⟩ : R.1.carrier) hxR' using 1
          apply Subtype.ext
          rfl
      }
    have hJprime : J.IsPrime := by
      refine ⟨?_, ?_⟩
      · intro htop
        have hone : (1 : B) ∈ J := by
          rw [htop]
          trivial
        rcases hone with ⟨P, hP, hP'⟩
        have hone' : (1 : P.1.carrier) ∈ P.1.prime := by
          convert hP' using 1
          apply Subtype.ext
          rfl
        exact P.1.isPrime.ne_top ((Ideal.eq_top_iff_one P.1.prime).mpr hone')
      · intro x y hxy
        rcases hxy with ⟨P0, hxyP0, hxyP0'⟩
        obtain ⟨P1, hxP1⟩ := hmemB.mp x.property
        obtain ⟨P2, hyP2⟩ := hmemB.mp y.property
        obtain ⟨T, h0T, h1T⟩ := hupperdom P0 P1
        obtain ⟨S, hTS, h2S⟩ := hupperdom T P2
        have h0S := hdom_trans h0T hTS
        have h1S := hdom_trans h1T hTS
        obtain ⟨hzS, hzS'⟩ := hpush h0S hxyP0 hxyP0'
        rcases h1S with ⟨h1S, _⟩
        rcases h2S with ⟨h2S, _⟩
        have hxS : (x : L) ∈ S.1.carrier := h1S hxP1
        have hyS : (y : L) ∈ S.1.carrier := h2S hyP2
        have hprodS :
            ((⟨(x : L), hxS⟩ : S.1.carrier) *
              (⟨(y : L), hyS⟩ : S.1.carrier)) ∈ S.1.prime := by
          convert hzS' using 1
          apply Subtype.ext
          rfl
        rcases S.1.isPrime.mem_or_mem hprodS with hxS' | hyS'
        · exact Or.inl ⟨S, hxS, hxS'⟩
        · exact Or.inr ⟨S, hyS, hyS'⟩
    let Q : Chapter10DominationPair (K := K) (L := L) V :=
      { carrier := B
        contains := hcontainsB
        prime := J
        isPrime := hJprime
        contracts := by
          intro x hx
          constructor
          · rintro ⟨P, hxP, hxP'⟩
            have hxP'' : (⟨algebraMap K L x, P.1.contains x hx⟩ : P.1.carrier) ∈
                P.1.prime := by
              simpa using hxP'
            exact (P.1.contracts x hx).mp hxP''
          · intro hxmax
            refine ⟨Pbase, Pbase.1.contains x hx, ?_⟩
            have := (Pbase.1.contracts x hx).mpr hxmax
            simpa using this }
    refine ⟨Q, ?_⟩
    intro P hP
    have hPB : P.carrier ≤ B := le_iSup (fun R : C => R.1.carrier) ⟨P, hP⟩
    refine ⟨hPB, ?_⟩
    intro x
    constructor
    · rintro ⟨R, hxR, hxR'⟩
      rcases hC P hP R.1 R.2 with hPR | hRP
      · exact (hPR.2 x).mp (by simpa using hxR')
      · have hxP : (⟨(x : L), hRP.1 hxR⟩ : P.carrier) ∈ P.prime :=
          (hRP.2 ⟨(x : L), hxR⟩).mpr (by simpa using hxR')
        simpa using hxP
    · intro hxP
      exact ⟨⟨P, hP⟩, x.property, hxP⟩
  · refine ⟨P₀, ?_⟩
    intro P hP
    exact (hCne ⟨P, hP⟩).elim

/-- Existence of a maximal domination pair. -/
theorem chapter10_maximal_domination_pair
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V] :
    ∃ P : Chapter10DominationPair (K := K) (L := L) V, ∀ Q,
      Chapter10DominationPair.Dominates P Q →
        Chapter10DominationPair.Dominates Q P := by
  let f : V →+* L := (algebraMap K L).comp V.subtype
  obtain ⟨W, hW, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  let fW := f.codRestrict W.toSubring hW
  let : IsLocalRing W.toSubring := W.toLocalSubring.isLocalRing
  let : IsLocalHom fW := hlocal
  let P₀ : Chapter10DominationPair (K := K) (L := L) V :=
    { carrier := W.toSubring
      contains := fun x hx => by
        change f ⟨x, hx⟩ ∈ W.toSubring
        exact hW ⟨x, hx⟩
      prime := IsLocalRing.maximalIdeal W.toSubring
      isPrime := Ideal.IsMaximal.isPrime
        (IsLocalRing.maximalIdeal.isMaximal W.toSubring)
      contracts := fun x hx => by
        change fW ⟨x, hx⟩ ∈ IsLocalRing.maximalIdeal W.toSubring ↔
          (⟨x, hx⟩ : V) ∈ IsLocalRing.maximalIdeal V
        rw [← IsLocalRing.maximalIdeal_comap fW]
        rfl }
  let : LE (Chapter10DominationPair (K := K) (L := L) V) :=
    ⟨Chapter10DominationPair.Dominates⟩
  let : Preorder (Chapter10DominationPair (K := K) (L := L) V) :=
    { le := Chapter10DominationPair.Dominates
      le_refl := by
        intro P
        exact ⟨le_rfl, fun x => Iff.rfl⟩
      le_trans := by
        intro P Q R hPQ hQR
        rcases hPQ with ⟨hPQ, hPQ'⟩
        rcases hQR with ⟨hQR, hQR'⟩
        refine ⟨fun x hx => hQR (hPQ hx), ?_⟩
        intro x
        rw [hQR' ⟨x, hPQ x.property⟩]
        exact hPQ' x }
  obtain ⟨P, hP, hmax⟩ := zorn_le_nonempty_Ici₀ P₀ (fun c hc hchain y hy => by
    have hchain' : Chapter10DominationChain (c : Set _) := by
      intro P hPc Q hQc
      by_cases hPQ : P = Q
      · subst Q
        exact Or.inl ⟨le_rfl, fun x => Iff.rfl⟩
      · exact hchain hPc hQc hPQ
    obtain ⟨Q, hQ⟩ := chapter10_domination_chain_upper_bound c hchain'
    exact ⟨Q, hQ⟩) P₀ le_rfl
  exact ⟨P, hmax⟩

/-- A maximal pair is local. -/
theorem chapter10_maximal_domination_pair_is_local
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (P : Chapter10DominationPair (K := K) (L := L) V)
    (hmax : ∀ Q, Chapter10DominationPair.Dominates P Q →
      Chapter10DominationPair.Dominates Q P) :
    IsLocalRing P.carrier := by
  let : P.prime.IsPrime := P.isPrime
  let A := LocalSubring.ofPrime P.carrier P.prime
  have hPA : P.carrier ≤ A.toSubring := LocalSubring.le_ofPrime _ _
  let Q : Chapter10DominationPair (K := K) (L := L) V :=
    { carrier := A.toSubring
      contains := fun x hx => hPA (P.contains x hx)
      prime := IsLocalRing.maximalIdeal A.toSubring
      isPrime := Ideal.IsMaximal.isPrime
        (IsLocalRing.maximalIdeal.isMaximal A.toSubring)
      contracts := fun x hx => by
        have hloc : algebraMap P.carrier A.toSubring
            ⟨algebraMap K L x, P.contains x hx⟩ ∈
              IsLocalRing.maximalIdeal A.toSubring ↔
            (⟨algebraMap K L x, P.contains x hx⟩ : P.carrier) ∈ P.prime := by
          exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _
        exact hloc.trans (P.contracts x hx) }
  have hPQ : Chapter10DominationPair.Dominates P Q := by
    refine ⟨hPA, ?_⟩
    intro x
    change algebraMap P.carrier A.toSubring x ∈
        IsLocalRing.maximalIdeal A.toSubring ↔ x ∈ P.prime
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _
  have hQP := hmax Q hPQ
  have hcarrier : P.carrier = A.toSubring := le_antisymm hPA hQP.1
  rw [hcarrier]
  exact A.isLocalRing

/-- The prime in a maximal pair is maximal. -/
theorem chapter10_maximal_domination_pair_prime_maximal
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (P : Chapter10DominationPair (K := K) (L := L) V)
    (hmax : ∀ Q, Chapter10DominationPair.Dominates P Q →
      Chapter10DominationPair.Dominates Q P) :
    P.prime.IsMaximal := by
  let : IsLocalRing P.carrier :=
    chapter10_maximal_domination_pair_is_local P hmax
  let : P.prime.IsPrime := P.isPrime
  let A := LocalSubring.ofPrime P.carrier P.prime
  have hPA : P.carrier ≤ A.toSubring := LocalSubring.le_ofPrime _ _
  let Q : Chapter10DominationPair (K := K) (L := L) V :=
    { carrier := A.toSubring
      contains := fun x hx => hPA (P.contains x hx)
      prime := IsLocalRing.maximalIdeal A.toSubring
      isPrime := Ideal.IsMaximal.isPrime
        (IsLocalRing.maximalIdeal.isMaximal A.toSubring)
      contracts := fun x hx => by
        have hloc : algebraMap P.carrier A.toSubring
            ⟨algebraMap K L x, P.contains x hx⟩ ∈
              IsLocalRing.maximalIdeal A.toSubring ↔
            (⟨algebraMap K L x, P.contains x hx⟩ : P.carrier) ∈ P.prime := by
          exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _
        exact hloc.trans (P.contracts x hx) }
  have hPQ : Chapter10DominationPair.Dominates P Q := by
    refine ⟨hPA, ?_⟩
    intro x
    change algebraMap P.carrier A.toSubring x ∈
        IsLocalRing.maximalIdeal A.toSubring ↔ x ∈ P.prime
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _
  have hQP := hmax Q hPQ
  have hcarrier : P.carrier = A.toSubring := le_antisymm hPA hQP.1
  let : (IsLocalRing.maximalIdeal A.toSubring).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal A.toSubring
  have hsurj : Function.Surjective (algebraMap P.carrier A.toSubring) := by
    intro y
    have hy : (y : L) ∈ P.carrier := by
      rw [hcarrier]
      exact y.property
    exact ⟨⟨y, hy⟩, rfl⟩
  have hmax' : (IsLocalRing.maximalIdeal A.toSubring).comap
      (algebraMap P.carrier A.toSubring) |>.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective
      (f := algebraMap P.carrier A.toSubring) hsurj
  have hcomap : (IsLocalRing.maximalIdeal A.toSubring).comap
      (algebraMap P.carrier A.toSubring) = P.prime := by
    simpa only [Ideal.under_def] using
      (IsLocalization.AtPrime.under_maximalIdeal (S := A.toSubring)
        (I := P.prime))
  rw [hcomap] at hmax'
  exact hmax'

/-- The intrinsic valuation-ring test obtained from maximality. -/
theorem chapter10_maximal_domination_pair_is_valuation_ring
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {V : Subring K} [IsLocalRing V]
    (P : Chapter10DominationPair (K := K) (L := L) V)
    (hmax : ∀ Q, Chapter10DominationPair.Dominates P Q →
      Chapter10DominationPair.Dominates Q P) :
    Chapter10ValuationRingCriterion P.carrier := by
  let : IsLocalRing P.carrier :=
    chapter10_maximal_domination_pair_is_local P hmax
  have hPmax : P.prime.IsMaximal :=
    chapter10_maximal_domination_pair_prime_maximal P hmax
  have hprime : P.prime = IsLocalRing.maximalIdeal P.carrier :=
    IsLocalRing.eq_maximalIdeal hPmax
  let A : LocalSubring L := { toSubring := P.carrier }
  obtain ⟨W, hW⟩ := A.exists_le_valuationSubring
  let f : P.carrier →+* W.toSubring := Subring.inclusion hW.1
  let : IsLocalHom f := hW.2
  let : IsLocalRing W.toSubring := W.toLocalSubring.isLocalRing
  let Q : Chapter10DominationPair (K := K) (L := L) V :=
    { carrier := W.toSubring
      contains := fun x hx => hW.1 (P.contains x hx)
      prime := IsLocalRing.maximalIdeal W.toSubring
      isPrime := Ideal.IsMaximal.isPrime
        (IsLocalRing.maximalIdeal.isMaximal W.toSubring)
      contracts := fun x hx => by
        change (⟨algebraMap K L x, P.contains x hx⟩ : P.carrier) ∈
            (IsLocalRing.maximalIdeal W.toSubring).comap f ↔
          (⟨x, hx⟩ : V) ∈ IsLocalRing.maximalIdeal V
        rw [IsLocalRing.maximalIdeal_comap f, ← hprime]
        exact P.contracts x hx }
  have hPQ : Chapter10DominationPair.Dominates P Q := by
    refine ⟨hW.1, ?_⟩
    intro x
    change x ∈ (IsLocalRing.maximalIdeal W.toSubring).comap f ↔ x ∈ P.prime
    rw [IsLocalRing.maximalIdeal_comap f, ← hprime]
  have hQP := hmax Q hPQ
  have hcarrier : P.carrier = W.toSubring := le_antisymm hW.1 hQP.1
  intro x hx
  rcases W.mem_or_inv_mem x with hxW | hxW
  · exact Or.inl (hcarrier.symm ▸ hxW)
  · exact Or.inr (hcarrier.symm ▸ hxW)

/-- Every valuation extends to an arbitrary field extension. -/
theorem chapter10_valuation_extension_exists
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) :
    ∃ W : ValuationSubring L,
      Chapter10ContractsTo v.valuationSubring.toSubring W.toSubring := by
  let f : v.valuationSubring →+* L :=
    (algebraMap K L).comp v.valuationSubring.subtype
  obtain ⟨W, hW, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  let fW := f.codRestrict W.toSubring hW
  refine ⟨W, ?_⟩
  intro x
  constructor
  · intro hx
    by_cases hxV : x ∈ v.valuationSubring
    · exact hxV
    · have hx0 : x ≠ 0 := by
        intro hx0
        exact hxV (hx0 ▸ v.valuationSubring.zero_mem)
      have hxinv : x⁻¹ ∈ v.valuationSubring :=
        (v.valuationSubring.mem_or_inv_mem x).resolve_left hxV
      have hunit_img : IsUnit (fW ⟨x⁻¹, hxinv⟩) := by
        apply isUnit_iff_exists_inv.mpr
        refine ⟨⟨algebraMap K L x, hx⟩, ?_⟩
        apply Subtype.ext
        simp [fW, f, hx0]
      have hunit_src : IsUnit (⟨x⁻¹, hxinv⟩ : v.valuationSubring) :=
        (isUnit_map_iff fW _).mp hunit_img
      obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hunit_src
      have hax : (a : K) = x :=
        (eq_of_inv_mul_eq_one (congrArg Subtype.val ha)).symm
      exact hax ▸ a.property
  · intro hx
    exact hW ⟨x, hx⟩

/-- The algebraic case of the extension theorem. -/
theorem chapter10_algebraic_valuation_extension_exists
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) :
    ∃ W : ValuationSubring L,
      Chapter10ContractsTo v.valuationSubring.toSubring W.toSubring := by
  let f : v.valuationSubring →+* L :=
    (algebraMap K L).comp v.valuationSubring.subtype
  obtain ⟨W, hW, hlocal⟩ := IsLocalRing.exists_factor_valuationRing f
  let fW := f.codRestrict W.toSubring hW
  refine ⟨W, ?_⟩
  intro x
  constructor
  · intro hx
    by_cases hxV : x ∈ v.valuationSubring
    · exact hxV
    · have hx0 : x ≠ 0 := by
        intro hx0
        exact hxV (hx0 ▸ v.valuationSubring.zero_mem)
      have hxinv : x⁻¹ ∈ v.valuationSubring :=
        (v.valuationSubring.mem_or_inv_mem x).resolve_left hxV
      have hunit_img : IsUnit (fW ⟨x⁻¹, hxinv⟩) := by
        apply isUnit_iff_exists_inv.mpr
        refine ⟨⟨algebraMap K L x, hx⟩, ?_⟩
        apply Subtype.ext
        simp [fW, f, hx0]
      have hunit_src : IsUnit (⟨x⁻¹, hxinv⟩ : v.valuationSubring) :=
        (isUnit_map_iff fW _).mp hunit_img
      obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hunit_src
      have hax : (a : K) = x :=
        (eq_of_inv_mul_eq_one (congrArg Subtype.val ha)).symm
      exact hax ▸ a.property
  · intro hx
    exact hW ⟨x, hx⟩

/-! ## 10.2--10.3. Integral elements and boundedness -/

/-- An element integral over a valuation ring lies in every extending ring. -/
theorem chapter10_integral_elements_are_bounded
    {K L Γ₀ Δ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Δ₀]
    (v : Valuation K Γ₀) (w : Valuation L Δ₀)
    [h : Valuation.HasExtension v w]
    {x : L} (hx : IsIntegral v.valuationSubring x) :
    x ∈ w.valuationSubring := by
  change x ∈ w.valuationSubring.toSubring
  apply LocalSubring.mem_of_isMax_of_isIntegral
    (R := w.valuationSubring.toLocalSubring) w.valuationSubring.isMax_toLocalSubring
  exact (show IsIntegral w.valuationSubring x from hx.tower_top)

/-- One inclusion in the valuative description of the integral closure. -/
theorem chapter10_integral_closure_subset_bounded
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (E : Set (Chapter10ValuationOnField L))
    (hE : ∀ W, W ∈ E ↔ v.IsEquiv (W.valuation.comap (algebraMap K L))) :
    Chapter10IntegralElements v.valuationSubring L ⊆
      Chapter10BoundedAtValuations E := by
  intro x hx W hW
  change IsIntegral v.valuationSubring x at hx
  have hExt := (hE W).mp hW
  let : Valuation.HasExtension v W.valuation := ⟨hExt⟩
  exact chapter10_integral_elements_are_bounded v W.valuation hx

/-- The field-theoretic valuative criterion for integrality.

The wrapper is instantiated with a value group in the same universe as `L`.
Every valuation on a field is equivalent to one with this universe-level
choice (for example, its generated value group), which avoids quantifying a
single accidentally smaller universe while retaining the field-theoretic
intersection criterion.
-/
theorem chapter10_integral_closure_valuative_criterion
    {K : Type u10K} {L : Type u10L} {Γ₀ : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) :
    Chapter10IntegralElements v.valuationSubring L =
      {x : L | ∀ (W : Chapter10ValuationOnField.{u10L, u10L} L),
        v.IsEquiv (W.valuation.comap (algebraMap K L)) →
          x ∈ W.valuation.valuationSubring} := by
  set_option maxHeartbeats 1000000 in
    ext x
    change IsIntegral v.valuationSubring x ↔
      ∀ (W : Chapter10ValuationOnField.{u10L, u10L} L),
        v.IsEquiv (W.valuation.comap (algebraMap K L)) →
          x ∈ W.valuation.valuationSubring
    constructor
    · intro hx W hW
      let : Valuation.HasExtension v W.valuation := ⟨hW⟩
      exact chapter10_integral_elements_are_bounded v W.valuation hx
    · intro hx
      by_contra hxint
      have hx0 : x ≠ 0 := by
        intro hx0
        exact hxint (hx0 ▸ isIntegral_zero)
      let : Invertible x := invertibleOfNonzero hx0
      let f : v.valuationSubring →+* L :=
        (algebraMap K L).comp v.valuationSubring.subtype
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        apply FaithfulSMul.algebraMap_injective K L
        exact hab
      let B₀ : Subring L := f.range
      let e : v.valuationSubring ≃+* B₀ :=
        RingEquiv.ofBijective f.rangeRestrict
          ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
      have he : (algebraMap B₀ L).comp e.toRingHom =
          algebraMap v.valuationSubring L := by
        ext a
        rfl
      have hI₀ : (IsLocalRing.maximalIdeal v.valuationSubring).map e.toRingHom ≠
          (⊤ : Ideal B₀) := by
        intro htop
        have hmax : (IsLocalRing.maximalIdeal v.valuationSubring).IsMaximal :=
          IsLocalRing.maximalIdeal.isMaximal v.valuationSubring
        exact hmax.ne_top ((Ideal.map_eq_top_of_bijective e.toRingHom e.bijective).mp htop)
      let I : Ideal B₀ := (IsLocalRing.maximalIdeal v.valuationSubring).map e.toRingHom
      let S : Subalgebra B₀ L := Algebra.adjoin B₀ ({x⁻¹} : Set L)
      let xinv : S := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
      have hI : I.map (algebraMap B₀ S) + Ideal.span {xinv} ≠ ⊤ := by
        intro htop
        have htop' : I.map (algebraMap B₀ S) ⊔ Ideal.span {xinv} = ⊤ := by
          rw [← Ideal.add_eq_sup]
          exact htop
        have hp_exists :=
          (set_option maxHeartbeats 1000000 in
            Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
              (x⁻¹) I hI₀ htop')
        obtain ⟨p, hp, hpx⟩ := hp_exists
        have hunit : IsUnit p.leadingCoeff := by
          apply of_not_not
          intro hlead
          have hlead' : ¬ IsUnit (e.symm p.leadingCoeff) := by
            intro hlead'
            exact hlead (by simpa using hlead'.map e.toRingHom)
          have hleadM : e.symm p.leadingCoeff ∈
              IsLocalRing.maximalIdeal v.valuationSubring := by
            rw [IsLocalRing.mem_maximalIdeal]
            exact hlead'
          have hleadI : p.leadingCoeff ∈ I := by
            change p.leadingCoeff ∈
              (IsLocalRing.maximalIdeal v.valuationSubring).map e.toRingHom
            rw [← e.apply_symm_apply p.leadingCoeff]
            exact (Ideal.apply_mem_of_equiv_iff).2 hleadM
          have hone : (1 : B₀) ∈ I := by
            simpa using sub_mem hleadI hp
          exact hI₀ (I.eq_top_iff_one.mpr hone)
        have hpoly : IsIntegral B₀ x := by
          refine ⟨.C hunit.unit⁻¹.1 * p, ?_, ?_⟩
          · simp [Polynomial.Monic]
          · have hroot :
                eval₂ (algebraMap B₀ L) x p = 0 := by
              simpa [aeval_def] using hpx
            rw [eval₂_mul, eval₂_C, hroot, mul_zero]
        exact hxint ((RingEquiv.isIntegral_iff e he x).mpr hpoly)
      obtain ⟨W, hW⟩ :=
        (set_option maxHeartbeats 1000000 in
          Ideal.image_subset_nonunits_valuationSubring (A := S.toSubring)
            (I.map (algebraMap B₀ S) + Ideal.span {xinv}) hI)
      have hxW : x ∉ W := by
        intro hxin
        exact ((W.inv_mem_nonunits_iff.mp <|
          hW.2 ⟨xinv, le_add_self (α := Ideal S) (Ideal.subset_span rfl), rfl⟩).resolve_left hx0) hxin
      let W' : Chapter10ValuationOnField.{u10L, u10L} L :=
        { valueGroup := W.ValueGroup
          valuation := W.valuation }
      have hW' : v.IsEquiv (W'.valuation.comap (algebraMap K L)) := by
        apply Valuation.isEquiv_of_val_le_one
        intro y
        rw [← Valuation.mem_valuationSubring_iff,
          ← Valuation.mem_valuationSubring_iff]
        change y ∈ v.valuationSubring ↔
          algebraMap K L y ∈ W'.valuation.valuationSubring
        rw [ValuationSubring.valuationSubring_valuation]
        constructor
        · intro hy
          apply hW.1
          have he_y := congrArg (fun g : v.valuationSubring →+* L =>
            g ⟨y, hy⟩) he
          have he_y' : algebraMap B₀ L (e ⟨y, hy⟩) = algebraMap K L y := by
            calc
              algebraMap B₀ L (e ⟨y, hy⟩) =
                  algebraMap v.valuationSubring L ⟨y, hy⟩ := by simpa using he_y
              _ = algebraMap K L y := by
                rw [IsScalarTower.algebraMap_apply v.valuationSubring K L]
                rfl
          have hS_y : algebraMap B₀ L (e ⟨y, hy⟩) ∈ S :=
            S.algebraMap_mem (e ⟨y, hy⟩)
          rw [he_y'] at hS_y
          exact hS_y
        · intro hy
          by_contra hyV
          have hyinv : y⁻¹ ∈ v.valuationSubring :=
            (v.valuationSubring.mem_or_inv_mem y).resolve_left hyV
          have hyinvM : (e ⟨y⁻¹, hyinv⟩ : B₀) ∈ I := by
            exact (Ideal.apply_mem_of_equiv_iff).2 (by
              rw [IsLocalRing.mem_maximalIdeal]
              intro hunit
              obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hunit
              have hay : (a : K) = y :=
                (eq_of_inv_mul_eq_one (congrArg Subtype.val ha)).symm
              exact hyV (hay ▸ a.property))
          have he_yinv := congrArg (fun g : v.valuationSubring →+* L =>
            g ⟨y⁻¹, hyinv⟩) he
          have he_yinv' : algebraMap B₀ L (e ⟨y⁻¹, hyinv⟩) =
              algebraMap K L y⁻¹ := by
            calc
              algebraMap B₀ L (e ⟨y⁻¹, hyinv⟩) =
                  algebraMap v.valuationSubring L ⟨y⁻¹, hyinv⟩ := by
                simpa using he_yinv
              _ = algebraMap K L y⁻¹ := by
                rw [IsScalarTower.algebraMap_apply v.valuationSubring K L]
                rfl
          have hmemS :
              (algebraMap B₀ S) (e ⟨y⁻¹, hyinv⟩) ∈
                I.map (algebraMap B₀ S) + Ideal.span {xinv} := by
            apply (le_self_add (α := Ideal S))
            exact Ideal.mem_map_of_mem (algebraMap B₀ S) hyinvM
          have hnon' : algebraMap K L y⁻¹ ∈ W.nonunits := by
            apply hW.2
            refine ⟨algebraMap B₀ S (e ⟨y⁻¹, hyinv⟩), hmemS, ?_⟩
            change algebraMap B₀ L (e ⟨y⁻¹, hyinv⟩) = algebraMap K L y⁻¹
            exact he_yinv'
          have hy0L : algebraMap K L y ≠ 0 := by
            simpa using (RingHom.injective (algebraMap K L)).ne (show y ≠ 0 by
              intro hy0
              exact hyV (hy0 ▸ v.valuationSubring.zero_mem))
          have hnon'' : (algebraMap K L y)⁻¹ ∈ W.nonunits := by
            rw [← map_inv₀]
            exact hnon'
          exact ((W.inv_mem_nonunits_iff.mp hnon'').resolve_left hy0L) hy
      apply hxW
      have hxW' := hx W' hW'
      rw [ValuationSubring.valuationSubring_valuation] at hxW'
      exact hxW'

/-- Equivalent set notation for the intersection of all extending valuation rings. -/
theorem chapter10_integral_closure_is_intersection
    {K : Type u10K} {L : Type u10L} {Γ₀ : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) :
    (Chapter10IntegralClosure v.valuationSubring L).toSubring =
      ⨅ (W : Chapter10ValuationOnField.{u10L, u10L} L)
        (_ : v.IsEquiv (W.valuation.comap (algebraMap K L))),
        W.valuation.valuationSubring.toSubring := by
  ext x
  change IsIntegral v.valuationSubring x ↔
    x ∈ ⨅ (W : Chapter10ValuationOnField.{u10L, u10L} L)
      (_ : v.IsEquiv (W.valuation.comap (algebraMap K L))),
      W.valuation.valuationSubring.toSubring
  rw [Subring.mem_iInf]
  simpa [Chapter10IntegralElements] using
    (Set.ext_iff.mp (chapter10_integral_closure_valuative_criterion v) x)

/-- If the extension is unique, the integral closure itself is a valuation ring. -/
theorem chapter10_unique_extension_makes_integral_closure_valuation_ring
    {K : Type u10K} {L : Type u10L} {Γ₀ : Type u10Γ}
    [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [Algebra.IsAlgebraic K L]
    (v : Valuation K Γ₀)
    (hunique : ∀ (W₁ W₂ : Chapter10ValuationOnField.{u10L, u10L} L),
      v.IsEquiv (W₁.valuation.comap (algebraMap K L)) →
      v.IsEquiv (W₂.valuation.comap (algebraMap K L)) →
      W₁.valuation.IsEquiv W₂.valuation) :
    Chapter10ValuationRingCriterion
      (Chapter10IntegralClosure v.valuationSubring L).toSubring := by
  obtain ⟨W₀, hW₀⟩ :=
    chapter10_algebraic_valuation_extension_exists (K := K) (L := L) (Γ₀ := Γ₀) v
  let W₀' : Chapter10ValuationOnField.{u10L, u10L} L :=
    { valueGroup := W₀.ValueGroup
      valuation := W₀.valuation }
  have hW₀' : v.IsEquiv (W₀'.valuation.comap (algebraMap K L)) := by
    apply Valuation.isEquiv_of_val_le_one
    intro x
    change x ∈ v.valuationSubring ↔ W₀.valuation (algebraMap K L x) ≤ 1
    constructor
    · intro hx
      exact (ValuationSubring.valuation_le_one_iff W₀ _).mpr ((hW₀ x).mpr hx)
    · intro hx
      exact (hW₀ x).mp ((ValuationSubring.valuation_le_one_iff W₀ _).mp hx)
  intro x hx
  rcases W₀.mem_or_inv_mem x with hxW₀ | hxW₀
  · left
    change x ∈ Chapter10IntegralElements v.valuationSubring L
    rw [chapter10_integral_closure_valuative_criterion v]
    intro W hW
    have hEq : W₀'.valuation.valuationSubring = W.valuation.valuationSubring :=
      (Valuation.isEquiv_iff_valuationSubring W₀'.valuation W.valuation).mp
        (hunique W₀' W hW₀' hW)
    have hxW₀' : x ∈ W₀'.valuation.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]
      exact (ValuationSubring.valuation_le_one_iff W₀ x).mpr hxW₀
    rw [hEq] at hxW₀'
    exact hxW₀'
  · right
    change x⁻¹ ∈ Chapter10IntegralElements v.valuationSubring L
    rw [chapter10_integral_closure_valuative_criterion v]
    intro W hW
    have hEq : W₀'.valuation.valuationSubring = W.valuation.valuationSubring :=
      (Valuation.isEquiv_iff_valuationSubring W₀'.valuation W.valuation).mp
        (hunique W₀' W hW₀' hW)
    have hxW₀' : x⁻¹ ∈ W₀'.valuation.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]
      exact (ValuationSubring.valuation_le_one_iff W₀ x⁻¹).mpr hxW₀
    rw [hEq] at hxW₀'
    exact hxW₀'

/-- All coefficients of the characteristic polynomial, trace, and norm are integral. -/
def Chapter10CharacteristicPolynomialIntegral
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L]
    (x : L) (R : Subring K) : Prop :=
  (∀ i, (LinearMap.charpoly (Algebra.lmul K L x)).coeff i ∈ R) ∧
    Algebra.trace K L x ∈ R ∧ Algebra.norm K x ∈ R

/-- Integral elements pass the finite discretely valued norm test. -/
theorem chapter10_integral_element_characteristic_data
    {K L A : Type*} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra A L] [Algebra A K]
    [IsScalarTower A K L]
    [FiniteDimensional K L]
    (R : Subring K)
    {x : L} (hx : IsIntegral A x)
    (hAtoR : ∀ z : K, IsIntegral A z → z ∈ R) :
    Chapter10CharacteristicPolynomialIntegral x R := by
  sorry

/-- A cancellation example witnessing that the norm alone is not a converse. -/
structure Chapter10NormCancellationExample
    (A K L : Type*) [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [FiniteDimensional K L] where
  x : L
  norm_mem : ∃ a : A, Algebra.norm K x = algebraMap A K a
  not_integral : ¬ IsIntegral A x

theorem chapter10_norm_alone_is_not_a_converse
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [FiniteDimensional K L]
    (exampleData : Chapter10NormCancellationExample A K L) :
    ¬ (∀ x : L, (∃ a : A, Algebra.norm K x = algebraMap A K a) →
      IsIntegral A x) := by
  intro h
  exact exampleData.not_integral (h exampleData.x exampleData.norm_mem)

/-! ## 10.4. Ramification index and residue degree -/

/-- The multiplicative subgroup generated by the nonzero values of a valuation. -/
def Chapter10ValueGroup {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) : Subgroup Γ₀ˣ :=
  MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom

/-- The residue field associated with a valuation. -/
abbrev Chapter10ResidueField {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) :=
  IsLocalRing.ResidueField v.valuationSubring

/-- The finite index of the value groups, once the inclusion is supplied. -/
noncomputable def Chapter10RamificationIndex
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    (hΓ : Chapter10ValueGroup v ≤ Chapter10ValueGroup w)
    [Finite (Chapter10ValueGroup w ⧸
      (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w))] : ℕ :=
  let _ := hΓ
  Nat.card (Chapter10ValueGroup w ⧸
    (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w))

/-- The residue degree of an extension. -/
noncomputable def Chapter10ResidueDegree
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [FiniteDimensional K L]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [Valuation.HasExtension v w] : ℕ :=
  Module.finrank (Chapter10ResidueField v) (Chapter10ResidueField w)

/-- The residue homomorphism induced by an extending valuation. -/
def Chapter10ResidueFieldMap
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [Valuation.HasExtension v w] :
    Chapter10ResidueField v →+* Chapter10ResidueField w :=
  IsLocalRing.ResidueField.map (algebraMap v.valuationSubring w.valuationSubring)

/-- The residue map induced by an extending valuation is injective. -/
theorem chapter10_residue_field_map_injective
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [Valuation.HasExtension v w] :
    Function.Injective (Chapter10ResidueFieldMap v w) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective b
  have hres :
      IsLocalRing.residue w.valuationSubring
          (algebraMap v.valuationSubring w.valuationSubring x) =
        IsLocalRing.residue w.valuationSubring
          (algebraMap v.valuationSubring w.valuationSubring y) := by
    simpa [Chapter10ResidueFieldMap] using hab
  have hzero :
      IsLocalRing.residue w.valuationSubring
          (algebraMap v.valuationSubring w.valuationSubring x -
            algebraMap v.valuationSubring w.valuationSubring y) = 0 := by
    rw [map_sub, hres, sub_self]
  have hmem :
      algebraMap v.valuationSubring w.valuationSubring (x - y) ∈
        IsLocalRing.maximalIdeal w.valuationSubring := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    simpa using hzero
  have hmem' : x - y ∈ IsLocalRing.maximalIdeal v.valuationSubring :=
    (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff v w).mp hmem
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem'

/-- The residue degree for an extension whose value group may differ. -/
noncomputable def Chapter10HeterogeneousResidueDegree
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [FiniteDimensional K L]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (h : v.IsEquiv (w.comap (algebraMap K L))) : ℕ := by
  letI : Valuation.HasExtension v w := ⟨h⟩
  exact Module.finrank (Chapter10ResidueField v) (Chapter10ResidueField w)

/-- The generator in a valuation's value group represented by a nonzero field
element.  This lets heterogeneous value-group maps state that they are
induced by restriction of the valuation, rather than merely being abstract
finite-index embeddings. -/
def Chapter10ValueGroupGenerator
    {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (x : K) (hx : v x ≠ 0) :
    Chapter10ValueGroup v :=
  ⟨Units.mk0 (v x) (by simpa using hx),
    MonoidWithZeroHom.mem_valueGroup v.toMonoidWithZeroHom ⟨x, rfl⟩⟩

/--
The actual value-group and residue-field data of one finite branch.  The map
and its finite quotient are retained explicitly, rather than identifying
different ordered value groups with a fixed codomain.
-/
structure Chapter10HeterogeneousExtensionData
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    [FiniteDimensional K L]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (h : v.IsEquiv (w.comap (algebraMap K L))) where
  valueGroupMap : Chapter10ValueGroup v →* Chapter10ValueGroup w
  /-- The map sends every value attained on `K` to the corresponding value
  attained by its image in `L`; hence it is the canonical map induced by the
  extension, not an unrelated finite-index homomorphism. -/
  valueGroupMap_spec :
    ∀ (x : K) (hx : v x ≠ 0),
      ((valueGroupMap (Chapter10ValueGroupGenerator v x hx) :
        Chapter10ValueGroup w) : ΓLˣ) =
        Units.mk0 (w (algebraMap K L x)) (h.eq_zero.ne.mp hx)
  valueGroupMap_injective : Function.Injective valueGroupMap
  finite_quotient : Finite (Chapter10ValueGroup w ⧸ valueGroupMap.range)
  ramificationIndex : ℕ

  ramificationIndex_eq :
    ramificationIndex = Nat.card (Chapter10ValueGroup w ⧸ valueGroupMap.range)
  residueDegree : ℕ
  residueDegree_eq :
    residueDegree = Chapter10HeterogeneousResidueDegree v w h

/-- The value-group and residue-field data exist for every finite branch. -/
theorem chapter10_heterogeneous_extension_data_exists
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL] [FiniteDimensional K L]
    (v : Valuation K ΓK) (w : Valuation L ΓL)
    (h : v.IsEquiv (w.comap (algebraMap K L))) :
    Nonempty (Chapter10HeterogeneousExtensionData v w h) := by
  classical
  let vc := w.comap (algebraMap K L)
  have hinc : Chapter10ValueGroup vc ≤ Chapter10ValueGroup w := by
    change MonoidWithZeroHom.valueGroup vc.toMonoidWithZeroHom ≤
      MonoidWithZeroHom.valueGroup w.toMonoidWithZeroHom
    rw [MonoidWithZeroHom.valueGroup_def]
    refine (Subgroup.closure_le
      (MonoidWithZeroHom.valueGroup w.toMonoidWithZeroHom)).mpr ?_
    rintro y ⟨x, hx⟩
    apply MonoidWithZeroHom.mem_valueGroup w.toMonoidWithZeroHom
    refine ⟨algebraMap K L x, ?_⟩
    change w (algebraMap K L x) = (y : ΓL)
    exact hx
  let e₀ := h.orderMonoidIso
  let φ₀ : Chapter10ValueGroup v →* Chapter10ValueGroup vc :=
    (WithZero.unitsWithZeroEquiv.toMonoidHom).comp
      ((Units.map e₀.toMonoidHom).comp
        WithZero.unitsWithZeroEquiv.symm.toMonoidHom)
  have hφ₀ : Function.Injective φ₀ := by
    intro a b hab
    change
      WithZero.unitsWithZeroEquiv
          (Units.map e₀.toMonoidHom
            (WithZero.unitsWithZeroEquiv.symm a)) =
        WithZero.unitsWithZeroEquiv
          (Units.map e₀.toMonoidHom
            (WithZero.unitsWithZeroEquiv.symm b)) at hab
    have hab_units :
        Units.map e₀.toMonoidHom
            (WithZero.unitsWithZeroEquiv.symm a) =
          Units.map e₀.toMonoidHom
            (WithZero.unitsWithZeroEquiv.symm b) :=
      WithZero.unitsWithZeroEquiv.injective hab
    apply WithZero.unitsWithZeroEquiv.symm.injective
    apply Units.ext
    apply e₀.injective
    exact congrArg Units.val hab_units
  let φ : Chapter10ValueGroup v →* Chapter10ValueGroup w :=
    (Subgroup.inclusion hinc).comp φ₀
  have hφ : Function.Injective φ := by
    intro a b hab
    apply hφ₀
    exact (Subgroup.inclusion_injective hinc) hab
  have hφspec (x : K) (hx : v x ≠ 0) :
      ((φ (Chapter10ValueGroupGenerator v x hx) :
        Chapter10ValueGroup w) : ΓLˣ) =
        Units.mk0 (w (algebraMap K L x)) (h.eq_zero.ne.mp hx) := by
    apply Units.ext
    have hgen :
        (WithZero.unitsWithZeroEquiv.symm
            (Chapter10ValueGroupGenerator v x hx :
              MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom)).val =
          MonoidWithZeroHom.ValueGroup₀.restrict₀
            (MonoidWithZeroHom.ofClass v) x := by
      rw [MonoidWithZeroHom.ValueGroup₀.restrict₀_of_ne_zero
        (by simpa using hx)]
      rfl
    have hs := Valuation.IsEquiv.orderMonoidIso_spec₀ h x
    have hs' :
        e₀
            (WithZero.unitsWithZeroEquiv.symm
              (Chapter10ValueGroupGenerator v x hx :
                MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom)).val =
          MonoidWithZeroHom.ValueGroup₀.restrict₀
            (MonoidWithZeroHom.ofClass vc) x := by
      rw [hgen]
      exact hs
    change
      MonoidWithZeroHom.ValueGroup₀.embedding
          (f := MonoidWithZeroHom.ofClass vc)
          (e₀
            (WithZero.unitsWithZeroEquiv.symm
              (Chapter10ValueGroupGenerator v x hx :
                MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom)).val) =
        w (algebraMap K L x)
    rw [hs']
    simp [vc]
  refine ⟨{
    valueGroupMap := φ
    valueGroupMap_spec := hφspec
    valueGroupMap_injective := hφ
    finite_quotient := by
      let Q := Chapter10ValueGroup w ⧸ φ.range
      let rep : Q → Chapter10ValueGroup w :=
        fun q => Classical.choose (QuotientGroup.mk_surjective q)
      have hrep (q : Q) : QuotientGroup.mk (rep q) = q :=
        Classical.choose_spec (QuotientGroup.mk_surjective q)
      have hvalmem (u : Chapter10ValueGroup w) : ∃ x : L, ∃ hx : w x ≠ 0,
          Units.mk0 (w x) hx = (u : ΓLˣ) := by
        have hu : (u : ΓLˣ).val ∈
            (Units.val '' (Chapter10ValueGroup w : Set ΓLˣ)) :=
          ⟨u, u.property, rfl⟩
        change (u : ΓLˣ).val ∈
          Units.val '' (MonoidWithZeroHom.valueGroup w.toMonoidWithZeroHom : Set ΓLˣ) at hu
        rw [MonoidWithZeroHom.valueGroup_eq_range w.toMonoidWithZeroHom] at hu
        rcases hu with ⟨hu, hne⟩
        rcases hu with ⟨x, hx⟩
        have hne_u : (u : ΓLˣ).val ≠ 0 := by
          exact hne
        have hne' : w x ≠ 0 := by
          have hx' : w x = (u : ΓLˣ).val := by simpa using hx
          rw [hx']
          exact hne_u
        refine ⟨x, hne', ?_⟩
        apply Units.ext
        simpa using hx
      let x : Q → L := fun q => Classical.choose (hvalmem (rep q))
      have hx (q : Q) : w (x q) ≠ 0 :=
        Classical.choose (Classical.choose_spec (hvalmem (rep q)))
      let : Valuation.HasExtension v w := ⟨h⟩
      have hLI : LinearIndependent K x := by
        rw [linearIndependent_iff_finset_linearIndependent]
        intro s
        let e : (↥s) ≃ Fin s.card := Finset.equivFin s
        let x' : Fin s.card → L := fun i => x (e.symm i)
        have hx' (i : Fin s.card) : x' i ≠ 0 := by
          simpa [x'] using hx (e.symm i)
        have hblock : ∀ (a : Fin 1 → K),
            (∑ j, algebraMap K L (a j) * (1 : L)) = 0 →
              ∀ j, a j = 0 := by
          intro a ha j
          have ha0 : algebraMap K L (a 0) = 0 := by
            simpa using ha
          have : a 0 = 0 :=
            (RingHom.injective (algebraMap K L)) (by simpa using ha0)
          simpa [Subsingleton.elim j (0 : Fin 1)] using this
        have hvalues : ∀ (a : Fin s.card × Fin 1 → K)
            (i i' : Fin s.card), i ≠ i' →
            (∑ j, algebraMap K L (a (i, j)) * (1 : L)) ≠ 0 →
            (∑ j, algebraMap K L (a (i', j)) * (1 : L)) ≠ 0 →
            w (x' i * ∑ j, algebraMap K L (a (i, j)) * (1 : L)) ≠
              w (x' i' * ∑ j, algebraMap K L (a (i', j)) * (1 : L)) := by
          intro a i i' hii hai hai'
          simp only [Fin.sum_univ_one, mul_one] at hai hai' ⊢
          intro heq
          have hai0 : a (i, 0) ≠ 0 := by
            intro hz
            apply hai
            simp [hz]
          have hai'0 : a (i', 0) ≠ 0 := by
            intro hz
            apply hai'
            simp [hz]
          have hvai : v (a (i, 0)) ≠ 0 :=
            (Valuation.ne_zero_iff v).mpr hai0
          have hvai' : v (a (i', 0)) ≠ 0 :=
            (Valuation.ne_zero_iff v).mpr hai'0
          let ui : Chapter10ValueGroup v :=
            Chapter10ValueGroupGenerator v (a (i, 0)) hvai
          let ui' : Chapter10ValueGroup v :=
            Chapter10ValueGroupGenerator v (a (i', 0)) hvai'
          have hφui : (φ ui : ΓLˣ) =
              Units.mk0 (w (algebraMap K L (a (i, 0))))
                (h.eq_zero.ne.mp hvai) := by
            simpa [ui] using hφspec (a (i, 0)) hvai
          have hφui' : (φ ui' : ΓLˣ) =
              Units.mk0 (w (algebraMap K L (a (i', 0))))
                (h.eq_zero.ne.mp hvai') := by
            simpa [ui'] using hφspec (a (i', 0)) hvai'
          have hφui_val : (φ ui : ΓLˣ).val =
              w (algebraMap K L (a (i, 0))) := by
            rw [hφui]
            rfl
          have hφui'_val : (φ ui' : ΓLˣ).val =
              w (algebraMap K L (a (i', 0))) := by
            rw [hφui']
            rfl
          have hrepval : (rep (e.symm i) : ΓLˣ) * (φ ui : ΓLˣ) =
              (rep (e.symm i') : ΓLˣ) * (φ ui' : ΓLˣ) := by
            have hxi := Classical.choose_spec (hvalmem (rep (e.symm i)))
            have hxi' := Classical.choose_spec (hvalmem (rep (e.symm i')))
            have hxi_val : Units.mk0 (w (x (e.symm i))) (hx (e.symm i)) =
                (rep (e.symm i) : ΓLˣ) := hxi.2
            have hxi'_val : Units.mk0 (w (x (e.symm i'))) (hx (e.symm i')) =
                (rep (e.symm i') : ΓLˣ) := hxi'.2
            have hxi_val' : w (x (e.symm i)) =
                (rep (e.symm i) : ΓLˣ).val := by
              simpa using congrArg Units.val hxi_val
            have hxi'_val' : w (x (e.symm i')) =
                (rep (e.symm i') : ΓLˣ).val := by
              simpa using congrArg Units.val hxi'_val
            apply Units.ext
            simpa [x', w.map_mul, hφui_val, hφui'_val, hxi_val', hxi'_val'] using heq
          let g : Chapter10ValueGroup w :=
            ⟨(rep (e.symm i) : ΓLˣ)⁻¹ *
                (rep (e.symm i') : ΓLˣ), by
              exact (Chapter10ValueGroup w).mul_mem
                ((Chapter10ValueGroup w).inv_mem (rep (e.symm i)).property)
                (rep (e.symm i')).property⟩
          have huieq :
              ((rep (e.symm i) : ΓLˣ)⁻¹ *
                (rep (e.symm i') : ΓLˣ) : ΓLˣ) =
                (φ ui : ΓLˣ) * (φ ui' : ΓLˣ)⁻¹ := by
            calc
              ((rep (e.symm i) : ΓLˣ)⁻¹ *
                  (rep (e.symm i') : ΓLˣ) : ΓLˣ) =
                  (rep (e.symm i) : ΓLˣ)⁻¹ *
                    ((rep (e.symm i) : ΓLˣ) * (φ ui : ΓLˣ)) *
                      (φ ui' : ΓLˣ)⁻¹ := by rw [hrepval]; simp [mul_assoc]
            _ = (φ ui : ΓLˣ) * (φ ui' : ΓLˣ)⁻¹ := by simp
          have hmem' : g ∈ φ.range := by
            rw [MonoidHom.mem_range]
            refine ⟨ui * ui'⁻¹, ?_⟩
            apply Subtype.ext
            change (φ (ui * ui'⁻¹) : ΓLˣ) =
              (rep (e.symm i) : ΓLˣ)⁻¹ * (rep (e.symm i') : ΓLˣ)
            simpa [map_mul] using huieq.symm
          have hg : g = (rep (e.symm i))⁻¹ * rep (e.symm i') := by
            apply Subtype.ext
            rfl
          have hq0 :
              (QuotientGroup.mk (s := φ.range)
                  (rep (e.symm i)) : Q) =
                QuotientGroup.mk (s := φ.range)
                  (rep (e.symm i')) := by
            apply QuotientGroup.eq.mpr
            rw [← hg]
            exact hmem'
          have hq : (e.symm i : Q) = (e.symm i' : Q) := by
            calc
              (e.symm i : Q) = QuotientGroup.mk (rep (e.symm i)) :=
                (hrep (e.symm i)).symm
              _ = QuotientGroup.mk (rep (e.symm i')) := hq0
              _ = (e.symm i' : Q) := hrep (e.symm i')
          have hq' : e.symm i = e.symm i' := Subtype.ext hq
          exact hii (e.symm.injective hq')
        have hvalpair : ∀ (a : Fin s.card → K) (i i' : Fin s.card), i ≠ i' →
            a i ≠ 0 → a i' ≠ 0 →
            w (x' i * algebraMap K L (a i)) ≠
              w (x' i' * algebraMap K L (a i')) := by
          intro a i i' hii hai hai'
          let b : Fin s.card × Fin 1 → K := fun ij => a ij.1
          simpa [b] using hvalues b i i' hii
            (by simpa [b] using hai) (by simpa [b] using hai')
        have hLI'' : LinearIndependent K x' := by
          rw [Fintype.linearIndependent_iff]
          intro a ha
          let T : Finset (Fin s.card) :=
            Finset.univ.filter (fun i => a i ≠ 0)
          have hTempty : T = ∅ := by
            by_contra hT
            have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
            let U : Finset ΓL :=
              T.image (fun i => w (x' i * algebraMap K L (a i)))
            have hUne : U.Nonempty := hTne.image _
            obtain ⟨i₀, hi₀T, hi₀eq⟩ :=
              Finset.mem_image.mp (Finset.max'_mem U hUne)
            have hai₀ : a i₀ ≠ 0 := (Finset.mem_filter.mp hi₀T).2
            have hamap₀ : algebraMap K L (a i₀) ≠ 0 := by
              intro hamap
              apply hai₀
              exact (RingHom.injective (algebraMap K L)) (by simpa using hamap)
            have hterm₀ : w (x' i₀ * algebraMap K L (a i₀)) ≠ 0 := by
              exact (Valuation.ne_zero_iff w).mpr
                (mul_ne_zero (hx' i₀) hamap₀)
            have hmax (i : Fin s.card) (hiT : i ∈ T) :
                w (x' i * algebraMap K L (a i)) ≤
                  w (x' i₀ * algebraMap K L (a i₀)) := by
              calc
                w (x' i * algebraMap K L (a i)) ≤ U.max' hUne :=
                  Finset.le_max' U _ (Finset.mem_image.mpr ⟨i, hiT, rfl⟩)
                _ = w (x' i₀ * algebraMap K L (a i₀)) := hi₀eq.symm
            have hstrict (i : Fin s.card) (hiT : i ∈ T) (hne : i ≠ i₀) :
                w (x' i * algebraMap K L (a i)) <
                  w (x' i₀ * algebraMap K L (a i₀)) := by
              apply lt_of_le_of_ne (hmax i hiT)
              exact hvalpair a i i₀ hne
                (Finset.mem_filter.mp hiT).2 hai₀
            have hsumT :
                (∑ i ∈ T, x' i * algebraMap K L (a i)) = 0 := by
              calc
                (∑ i ∈ T, x' i * algebraMap K L (a i)) =
                    ∑ i : Fin s.card, x' i * algebraMap K L (a i) := by
                  apply Finset.sum_subset (Finset.subset_univ T)
                  intro i hiuniv hiNotT
                  have hai : a i = 0 := by
                    by_contra hai
                    exact hiNotT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩)
                  simp [hai]
                _ = 0 := by
                  calc
                    (∑ i : Fin s.card, x' i * algebraMap K L (a i)) =
                        ∑ i : Fin s.card, algebraMap K L (a i) * x' i := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [mul_comm]
                    _ = ∑ i : Fin s.card, a i • x' i := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [Algebra.smul_def]
                    _ = 0 := ha
            have hvalsum :
                w (∑ i ∈ T, x' i * algebraMap K L (a i)) =
                  w (x' i₀ * algebraMap K L (a i₀)) := by
              apply w.map_sum_eq_of_lt hi₀T
              intro i hiT
              rcases Finset.mem_sdiff.mp hiT with ⟨hiT, hiNot⟩
              exact hstrict i hiT (by simpa using hiNot)
            rw [hsumT, w.map_zero] at hvalsum
            exact hterm₀ hvalsum.symm
          have hz : ∀ i : Fin s.card, a i = 0 := by
            intro i
            by_contra hai
            have hiT : i ∈ T :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
            rw [hTempty] at hiT
            simp at hiT
          intro i
          exact hz i
        have hLI_s := (linearIndependent_equiv e).mpr hLI''
        change LinearIndependent K (fun q : (↥s) => x' (e q)) at hLI_s
        have heqfun : (fun q : (↥s) => x' (e q)) =
            (fun q : (↥s) => x q) := by
          funext q
          simp [x']
        have hLI_s' : LinearIndependent K (fun q : (↥s) => x q) := by
          rw [← heqfun]
          exact hLI_s
        change LinearIndependent K (fun q : (↥s) => x q)
        exact hLI_s'
      exact hLI.finite
    ramificationIndex := Nat.card (Chapter10ValueGroup w ⧸ φ.range)
    ramificationIndex_eq := rfl
    residueDegree := Chapter10HeterogeneousResidueDegree v w h
    residueDegree_eq := rfl
  }⟩
/-- Value-group inclusion for a valuation extension. -/
theorem chapter10_value_group_inclusion
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    (hval : ∀ x : K, v x = w (algebraMap K L x)) :
    Chapter10ValueGroup v ≤ Chapter10ValueGroup w := by
  change MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom ≤
    MonoidWithZeroHom.valueGroup w.toMonoidWithZeroHom
  rw [MonoidWithZeroHom.valueGroup_def]
  refine (Subgroup.closure_le
    (MonoidWithZeroHom.valueGroup w.toMonoidWithZeroHom)).mpr ?_
  rintro y ⟨x, hx⟩
  apply MonoidWithZeroHom.mem_valueGroup w.toMonoidWithZeroHom
  refine ⟨algebraMap K L x, ?_⟩
  change w (algebraMap K L x) = (y : Γ₀)
  rw [← hval x]
  exact hx

/-- Finiteness of the value-group quotient in a finite extension. -/
theorem chapter10_value_group_quotient_finite
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [FiniteDimensional K L]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    (hval : ∀ x : K, v x = w (algebraMap K L x))
    (hΓ : Chapter10ValueGroup v ≤ Chapter10ValueGroup w) :
    Finite (Chapter10ValueGroup w ⧸
      (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w)) := by
  classical
  have _ := hΓ
  let Q := Chapter10ValueGroup w ⧸
    (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w)
  let rep : Q → Chapter10ValueGroup w :=
    fun q => Classical.choose (QuotientGroup.mk_surjective q)
  have hrep (q : Q) : QuotientGroup.mk (rep q) = q :=
    Classical.choose_spec (QuotientGroup.mk_surjective q)
  have hvalmem (u : Chapter10ValueGroup w) : ∃ x : L, ∃ hx : w x ≠ 0,
      Units.mk0 (w x) hx = (u : Γ₀ˣ) := by
    have hu : (u : Γ₀ˣ).val ∈
        (Units.val '' (Chapter10ValueGroup w : Set Γ₀ˣ)) :=
      ⟨u, u.property, rfl⟩
    change (u : Γ₀ˣ).val ∈
      Units.val '' (MonoidWithZeroHom.valueGroup w.toMonoidWithZeroHom : Set Γ₀ˣ) at hu
    rw [MonoidWithZeroHom.valueGroup_eq_range w.toMonoidWithZeroHom] at hu
    rcases hu with ⟨hu, hne⟩
    rcases hu with ⟨x, hx⟩
    have hne_u : (u : Γ₀ˣ).val ≠ 0 := by
      exact hne
    have hne' : w x ≠ 0 := by
      have hx' : w x = (u : Γ₀ˣ).val := by simpa using hx
      rw [hx']
      exact hne_u
    refine ⟨x, hne', ?_⟩
    apply Units.ext
    simpa using hx
  let x : Q → L := fun q => Classical.choose (hvalmem (rep q))
  have hx (q : Q) : w (x q) ≠ 0 :=
    Classical.choose (Classical.choose_spec (hvalmem (rep q)))
  let : Valuation.HasExtension v w := ⟨by
    intro a b
    change v a ≤ v b ↔ w (algebraMap K L a) ≤ w (algebraMap K L b)
    rw [hval a, hval b]⟩
  have hLI : LinearIndependent K x := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    let e : (↥s) ≃ Fin s.card := Finset.equivFin s
    let x' : Fin s.card → L := fun i => x (e.symm i)
    have hx' (i : Fin s.card) : x' i ≠ 0 := by
      simpa [x'] using hx (e.symm i)
    have hblock : ∀ (a : Fin 1 → K),
        (∑ j, algebraMap K L (a j) * (1 : L)) = 0 →
          ∀ j, a j = 0 := by
      intro a ha j
      have ha0 : algebraMap K L (a 0) = 0 := by
        simpa using ha
      have : a 0 = 0 := (RingHom.injective (algebraMap K L)) (by simpa using ha0)
      simpa [Subsingleton.elim j (0 : Fin 1)] using this
    have hvalues : ∀ (a : Fin s.card × Fin 1 → K)
        (i i' : Fin s.card), i ≠ i' →
        (∑ j, algebraMap K L (a (i, j)) * (1 : L)) ≠ 0 →
        (∑ j, algebraMap K L (a (i', j)) * (1 : L)) ≠ 0 →
        w (x' i * ∑ j, algebraMap K L (a (i, j)) * (1 : L)) ≠
          w (x' i' * ∑ j, algebraMap K L (a (i', j)) * (1 : L)) := by
      intro a i i' hii hai hai'
      simp only [Fin.sum_univ_one, mul_one] at hai hai' ⊢
      intro heq
      have hai0 : a (i, 0) ≠ 0 := by
        intro hz
        apply hai
        simp [hz]
      have hai'0 : a (i', 0) ≠ 0 := by
        intro hz
        apply hai'
        simp [hz]
      have hvai : v (a (i, 0)) ≠ 0 :=
        (Valuation.ne_zero_iff v).mpr hai0
      have hvai' : v (a (i', 0)) ≠ 0 :=
        (Valuation.ne_zero_iff v).mpr hai'0
      let ui : Chapter10ValueGroup v :=
        Chapter10ValueGroupGenerator v (a (i, 0)) hvai
      let ui' : Chapter10ValueGroup v :=
        Chapter10ValueGroupGenerator v (a (i', 0)) hvai'
      have hui : (ui : Γ₀ˣ) = Units.mk0 (v (a (i, 0))) hvai := by
        rfl
      have hui' : (ui' : Γ₀ˣ) = Units.mk0 (v (a (i', 0))) hvai' := by
        rfl
      have hrepval : (rep (e.symm i) : Γ₀ˣ) * (ui : Γ₀ˣ) =
          (rep (e.symm i') : Γ₀ˣ) * (ui' : Γ₀ˣ) := by
        have hxi := Classical.choose_spec (hvalmem (rep (e.symm i)))
        have hxi' := Classical.choose_spec (hvalmem (rep (e.symm i')))
        have hxi_val : Units.mk0 (w (x (e.symm i))) (hx (e.symm i)) =
            (rep (e.symm i) : Γ₀ˣ) := hxi.2
        have hxi'_val : Units.mk0 (w (x (e.symm i'))) (hx (e.symm i')) =
            (rep (e.symm i') : Γ₀ˣ) := hxi'.2
        have hxi_val' : w (x (e.symm i)) =
            (rep (e.symm i) : Γ₀ˣ).val := by
          simpa using congrArg Units.val hxi_val
        have hxi'_val' : w (x (e.symm i')) =
            (rep (e.symm i') : Γ₀ˣ).val := by
          simpa using congrArg Units.val hxi'_val
        apply Units.ext
        simpa [x', hval, hui, hui', w.map_mul, mul_assoc, hxi_val', hxi'_val'] using heq
      have hmem :
          ((rep (e.symm i) : Γ₀ˣ)⁻¹ *
              (rep (e.symm i') : Γ₀ˣ) : Γ₀ˣ) ∈ Chapter10ValueGroup v := by
        have huieq :
            ((rep (e.symm i) : Γ₀ˣ)⁻¹ *
                (rep (e.symm i') : Γ₀ˣ) : Γ₀ˣ) =
              (ui : Γ₀ˣ) * (ui' : Γ₀ˣ)⁻¹ := by
          calc
            ((rep (e.symm i) : Γ₀ˣ)⁻¹ *
                (rep (e.symm i') : Γ₀ˣ) : Γ₀ˣ) =
                (rep (e.symm i) : Γ₀ˣ)⁻¹ *
                  ((rep (e.symm i) : Γ₀ˣ) * (ui : Γ₀ˣ)) *
                    (ui' : Γ₀ˣ)⁻¹ := by rw [hrepval]; simp [mul_assoc]
            _ = (ui : Γ₀ˣ) * (ui' : Γ₀ˣ)⁻¹ := by simp
        rw [huieq]
        exact (Chapter10ValueGroup v).mul_mem ui.property
          ((Chapter10ValueGroup v).inv_mem ui'.property)
      let g : Chapter10ValueGroup w :=
        ⟨(rep (e.symm i) : Γ₀ˣ)⁻¹ *
            (rep (e.symm i') : Γ₀ˣ), by
          exact (Chapter10ValueGroup w).mul_mem
            ((Chapter10ValueGroup w).inv_mem (rep (e.symm i)).property)
            (rep (e.symm i')).property⟩
      have hmem' : g ∈
          (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w) := by
        apply Subgroup.mem_subgroupOf.mpr
        exact hmem
      have hg : g = (rep (e.symm i))⁻¹ * rep (e.symm i') := by
        apply Subtype.ext
        rfl
      have hq0 :
          (QuotientGroup.mk (s :=
              (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w))
            (rep (e.symm i)) : Q) =
            QuotientGroup.mk (s :=
              (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w))
              (rep (e.symm i')) := by
        apply QuotientGroup.eq.mpr
        rw [← hg]
        exact hmem'
      have hq : (e.symm i : Q) = (e.symm i' : Q) := by
        calc
          (e.symm i : Q) = QuotientGroup.mk (rep (e.symm i)) :=
            (hrep (e.symm i)).symm
          _ = QuotientGroup.mk (rep (e.symm i')) := hq0
          _ = (e.symm i' : Q) := hrep (e.symm i')
      have hq' : e.symm i = e.symm i' := Subtype.ext hq
      exact hii (e.symm.injective hq')
    have hvalpair : ∀ (a : Fin s.card → K) (i i' : Fin s.card), i ≠ i' →
        a i ≠ 0 → a i' ≠ 0 →
        w (x' i * algebraMap K L (a i)) ≠
          w (x' i' * algebraMap K L (a i')) := by
      intro a i i' hii hai hai'
      let b : Fin s.card × Fin 1 → K := fun ij => a ij.1
      simpa [b] using hvalues b i i' hii
        (by simpa [b] using hai) (by simpa [b] using hai')
    have hLI'' : LinearIndependent K x' := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      let T : Finset (Fin s.card) :=
        Finset.univ.filter (fun i => a i ≠ 0)
      have hTempty : T = ∅ := by
        by_contra hT
        have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
        let U : Finset Γ₀ :=
          T.image (fun i => w (x' i * algebraMap K L (a i)))
        have hUne : U.Nonempty := hTne.image _
        obtain ⟨i₀, hi₀T, hi₀eq⟩ :=
          Finset.mem_image.mp (Finset.max'_mem U hUne)
        have hai₀ : a i₀ ≠ 0 := (Finset.mem_filter.mp hi₀T).2
        have hamap₀ : algebraMap K L (a i₀) ≠ 0 := by
          intro hamap
          apply hai₀
          exact (RingHom.injective (algebraMap K L)) (by simpa using hamap)
        have hterm₀ : w (x' i₀ * algebraMap K L (a i₀)) ≠ 0 := by
          exact (Valuation.ne_zero_iff w).mpr
            (mul_ne_zero (hx' i₀) hamap₀)
        have hmax (i : Fin s.card) (hiT : i ∈ T) :
            w (x' i * algebraMap K L (a i)) ≤
              w (x' i₀ * algebraMap K L (a i₀)) := by
          calc
            w (x' i * algebraMap K L (a i)) ≤ U.max' hUne :=
              Finset.le_max' U _ (Finset.mem_image.mpr ⟨i, hiT, rfl⟩)
            _ = w (x' i₀ * algebraMap K L (a i₀)) := hi₀eq.symm
        have hstrict (i : Fin s.card) (hiT : i ∈ T) (hne : i ≠ i₀) :
            w (x' i * algebraMap K L (a i)) <
              w (x' i₀ * algebraMap K L (a i₀)) := by
          apply lt_of_le_of_ne (hmax i hiT)
          exact hvalpair a i i₀ hne
            (Finset.mem_filter.mp hiT).2 hai₀
        have hsumT :
            (∑ i ∈ T, x' i * algebraMap K L (a i)) = 0 := by
          calc
            (∑ i ∈ T, x' i * algebraMap K L (a i)) =
                ∑ i : Fin s.card, x' i * algebraMap K L (a i) := by
              apply Finset.sum_subset (Finset.subset_univ T)
              intro i hiuniv hiNotT
              have hai : a i = 0 := by
                by_contra hai
                exact hiNotT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩)
              simp [hai]
            _ = 0 := by
              calc
                (∑ i : Fin s.card, x' i * algebraMap K L (a i)) =
                    ∑ i : Fin s.card, algebraMap K L (a i) * x' i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [mul_comm]
                _ = ∑ i : Fin s.card, a i • x' i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [Algebra.smul_def]
                _ = 0 := ha
        have hvalsum :
            w (∑ i ∈ T, x' i * algebraMap K L (a i)) =
              w (x' i₀ * algebraMap K L (a i₀)) := by
          apply w.map_sum_eq_of_lt hi₀T
          intro i hiT
          rcases Finset.mem_sdiff.mp hiT with ⟨hiT, hiNot⟩
          exact hstrict i hiT (by simpa using hiNot)
        rw [hsumT, w.map_zero] at hvalsum
        exact hterm₀ hvalsum.symm
      have hz : ∀ i : Fin s.card, a i = 0 := by
        intro i
        by_contra hai
        have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
        rw [hTempty] at hiT
        simp at hiT
      intro i
      exact hz i
    have hLI_s := (linearIndependent_equiv e).mpr hLI''
    change LinearIndependent K (fun q : (↥s) => x' (e q)) at hLI_s
    have heqfun : (fun q : (↥s) => x' (e q)) =
        (fun q : (↥s) => x q) := by
      funext q
      simp [x']
    have hLI_s' : LinearIndependent K (fun q : (↥s) => x q) := by
      rw [← heqfun]
      exact hLI_s
    change LinearIndependent K (fun q : (↥s) => x q)
    exact hLI_s'
  exact hLI.finite

/-- Finiteness of the induced residue-field extension. -/
theorem chapter10_residue_degree_finite
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [FiniteDimensional K L]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [h : Valuation.HasExtension v w] :
    FiniteDimensional (Chapter10ResidueField v) (Chapter10ResidueField w) := by
  classical
  let k := Chapter10ResidueField v
  let E := Chapter10ResidueField w
  let I := Module.Basis.ofVectorSpaceIndex k E
  let b : Module.Basis I k E := Module.Basis.ofVectorSpace k E
  let y₀ : I → w.valuationSubring := fun i =>
    Classical.choose (IsLocalRing.residue_surjective (b i))
  have hy₀ (i : I) :
      IsLocalRing.residue w.valuationSubring (y₀ i) = b i :=
    Classical.choose_spec (IsLocalRing.residue_surjective (b i))
  let y : I → L := fun i => y₀ i
  have hyval (i : I) : w (y i) = 1 := by
    have hbi : b i ≠ 0 := b.ne_zero i
    have hnot : y₀ i ∉ IsLocalRing.maximalIdeal w.valuationSubring := by
      intro hmem
      apply hbi
      rw [← hy₀ i]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    have hle : w (y i) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff w (y i)).mpr (y₀ i).property
    have hnlt : ¬w (y i) < 1 := by
      intro hlt
      apply hnot
      exact (Valuation.mem_maximalIdeal_iff (v := w)).mpr hlt
    exact le_antisymm hle (le_of_not_gt hnlt)
  have hLI : LinearIndependent K y := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    let e : (↥s) ≃ Fin s.card := Finset.equivFin s
    let y' : Fin s.card → L := fun i => y (e.symm i)
    have hy' (i : Fin s.card) : w (y' i) = 1 := by
      simpa [y'] using hyval (e.symm i)
    have hLI' : LinearIndependent K y' := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      let T : Finset (Fin s.card) :=
        Finset.univ.filter (fun i => a i ≠ 0)
      have hTempty : T = ∅ := by
        by_contra hT
        have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
        let U : Finset Γ₀ :=
          T.image (fun i => w (algebraMap K L (a i)))
        have hUne : U.Nonempty := hTne.image _
        obtain ⟨i₀, hi₀T, hi₀eq⟩ :=
          Finset.mem_image.mp (Finset.max'_mem U hUne)
        have hai₀ : a i₀ ≠ 0 := (Finset.mem_filter.mp hi₀T).2
        have hamap₀ : algebraMap K L (a i₀) ≠ 0 := by
          simpa using (RingHom.injective (algebraMap K L)).ne hai₀
        have hw₀ : w (algebraMap K L (a i₀)) ≠ 0 :=
          (Valuation.ne_zero_iff w).mpr hamap₀
        have hmax (i : Fin s.card) (hiT : i ∈ T) :
            w (algebraMap K L (a i)) ≤
              w (algebraMap K L (a i₀)) := by
          calc
            w (algebraMap K L (a i)) ≤ U.max' hUne :=
              Finset.le_max' U _ (Finset.mem_image.mpr ⟨i, hiT, rfl⟩)
            _ = w (algebraMap K L (a i₀)) := hi₀eq.symm
        let c : Fin s.card → v.valuationSubring := fun i =>
          ⟨a i / a i₀, by
            by_cases hai : a i = 0
            · simp [hai]
            · have hiT : i ∈ T :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
              apply (Valuation.mem_valuationSubring_iff v _).mpr
              apply (Valuation.HasExtension.val_map_le_one_iff v w _).mp
              rw [map_div₀, w.map_div]
              exact (div_le_one₀ (w.pos_iff.mpr hamap₀)).mpr (hmax i hiT)
            ⟩
        have hnorm :
            (∑ i : Fin s.card,
              algebraMap K L (a i / a i₀) * y' i) = 0 := by
          have ha' :
              (∑ i : Fin s.card, algebraMap K L (a i) * y' i) = 0 := by
            simpa only [Algebra.smul_def] using ha
          calc
            (∑ i : Fin s.card,
                algebraMap K L (a i / a i₀) * y' i) =
                ∑ i : Fin s.card,
                  (algebraMap K L (a i₀))⁻¹ *
                    (algebraMap K L (a i) * y' i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [map_div₀]
              field_simp [hw₀]
            _ = (algebraMap K L (a i₀))⁻¹ *
                ∑ i : Fin s.card, algebraMap K L (a i) * y' i := by
              rw [Finset.mul_sum]
            _ = 0 := by rw [ha', mul_zero]
        have hnormB :
            (∑ i : Fin s.card,
                (algebraMap v.valuationSubring w.valuationSubring (c i)) *
                  (y₀ (e.symm i))) = 0 := by
          apply Subtype.ext
          simpa [c, y', y] using hnorm
        have hresnorm :=
          congrArg (IsLocalRing.residue w.valuationSubring) hnormB
        have hresrel :
            (∑ i : Fin s.card,
              algebraMap (Chapter10ResidueField v) (Chapter10ResidueField w)
                (IsLocalRing.residue v.valuationSubring (c i)) *
                b (e.symm i)) = 0 := by
          simpa only [map_sum, map_mul,
            Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap,
            hy₀, map_zero] using hresnorm
        have hb' : LinearIndependent k (fun i : Fin s.card => b (e.symm i)) :=
          b.linearIndependent.comp
            (fun i : Fin s.card => (e.symm i : I))
            (fun i j hij => by
              exact e.symm.injective (Subtype.ext hij))
        have hc0 : ∀ i : Fin s.card,
            IsLocalRing.residue v.valuationSubring (c i) = 0 := by
          apply (Fintype.linearIndependent_iff.mp hb')
          simpa only [Algebra.smul_def] using hresrel
        have hc₀ : c i₀ = 1 := by
          apply Subtype.ext
          dsimp [c]
          exact div_self hai₀
        have honezero : (1 : Chapter10ResidueField v) = 0 := by
          calc
            (1 : Chapter10ResidueField v) =
                IsLocalRing.residue v.valuationSubring (c i₀) := by
              rw [hc₀]
              simp
            _ = 0 := hc0 i₀
        exact one_ne_zero honezero
      have hz : ∀ i : Fin s.card, a i = 0 := by
        intro i
        by_contra hai
        have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
        rw [hTempty] at hiT
        simp at hiT
      intro i
      exact hz i
    have heq :
        (fun i : Fin s.card => y' i) ∘ e =
          (fun q : (↥s) => y q) := by
      funext q
      simp [y']
    exact (linearIndependent_equiv' e heq).mpr hLI'
  let : Finite I := Cardinal.mk_lt_aleph0_iff.mp
    hLI.lt_aleph0_of_finiteDimensional
  exact b.finiteDimensional_of_finite

/-- The value-group and residue directions give independent vectors. -/
theorem chapter10_value_residue_product_independence
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [Valuation.HasExtension v w]
    {r s : ℕ} (x : Fin r → L) (y : Fin s → L)
    (hx : ∀ i, x i ≠ 0)
    (hblock : ∀ (a : Fin s → K),
      (∑ j, algebraMap K L (a j) * y j) = 0 → ∀ j, a j = 0)
    (hvalues : ∀ (a : Fin r × Fin s → K) (i i' : Fin r), i ≠ i' →
      (∑ j, algebraMap K L (a (i, j)) * y j) ≠ 0 →
      (∑ j, algebraMap K L (a (i', j)) * y j) ≠ 0 →
      w (x i * ∑ j, algebraMap K L (a (i, j)) * y j) ≠
        w (x i' * ∑ j, algebraMap K L (a (i', j)) * y j)) :
    LinearIndependent K (fun ij : Fin r × Fin s => x ij.1 * y ij.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  let z : Fin r → L := fun i => ∑ j, algebraMap K L (a (i, j)) * y j
  have hregroup :
      (∑ ij : Fin r × Fin s, a ij • (x ij.1 * y ij.2)) =
        ∑ i : Fin r, x i * z i := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [z, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Algebra.smul_def]
    ring
  have hzero : (∑ i : Fin r, x i * z i) = 0 := by
    rw [← hregroup]
    exact ha
  let T : Finset (Fin r) := Finset.univ.filter (fun i => z i ≠ 0)
  have hTempty : T = ∅ := by
    by_contra hT
    have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
    let U : Finset Γ₀ := T.image (fun i => w (x i * z i))
    have hUne : U.Nonempty := hTne.image _
    obtain ⟨i₀, hi₀T, hi₀eq⟩ :=
      Finset.mem_image.mp (Finset.max'_mem U hUne)
    have hzi₀ : z i₀ ≠ 0 := (Finset.mem_filter.mp hi₀T).2
    have hterm₀ : w (x i₀ * z i₀) ≠ 0 := by
      exact (Valuation.ne_zero_iff w).mpr (mul_ne_zero (hx i₀) hzi₀)
    have hmax (i : Fin r) (hiT : i ∈ T) :
        w (x i * z i) ≤ w (x i₀ * z i₀) := by
      calc
        w (x i * z i) ≤ U.max' hUne :=
          Finset.le_max' U _ (Finset.mem_image.mpr ⟨i, hiT, rfl⟩)
        _ = w (x i₀ * z i₀) := hi₀eq.symm
    have hstrict (i : Fin r) (hiT : i ∈ T) (hne : i ≠ i₀) :
        w (x i * z i) < w (x i₀ * z i₀) := by
      apply lt_of_le_of_ne (hmax i hiT)
      exact hvalues a i i₀ hne (Finset.mem_filter.mp hiT).2 hzi₀
    have hsumT : (∑ i ∈ T, x i * z i) = 0 := by
      calc
        (∑ i ∈ T, x i * z i) = ∑ i : Fin r, x i * z i := by
          apply Finset.sum_subset (Finset.subset_univ T)
          intro i hiuniv hiNotT
          have hzi : z i = 0 := by
            by_contra hzi
            exact hiNotT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzi⟩)
          simp [hzi]
        _ = 0 := hzero
    have hvalsum : w (∑ i ∈ T, x i * z i) = w (x i₀ * z i₀) := by
      apply w.map_sum_eq_of_lt hi₀T
      intro i hiT
      rcases Finset.mem_sdiff.mp hiT with ⟨hiT, hiNot⟩
      exact hstrict i hiT (by simpa using hiNot)
    rw [hsumT, w.map_zero] at hvalsum
    exact hterm₀ hvalsum.symm
  have hz : ∀ i : Fin r, z i = 0 := by
    intro i
    by_contra hzi
    have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzi⟩
    rw [hTempty] at hiT
    simp at hiT
  intro ij
  exact (hblock (fun j => a (ij.1, j)) (hz ij.1)) ij.2

/-- The single-extension fundamental inequality ef ≤ [L:K]. -/
theorem chapter10_single_extension_fundamental_inequality
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [FiniteDimensional K L]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [h : Valuation.HasExtension v w]
    (hval : ∀ x : K, v x = w (algebraMap K L x))
    (hΓ : Chapter10ValueGroup v ≤ Chapter10ValueGroup w)
    [hfinite : Finite (Chapter10ValueGroup w ⧸
      (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w))] :
    Chapter10RamificationIndex v w hΓ * Chapter10ResidueDegree v w ≤
      Module.finrank K L := by
  set_option maxHeartbeats 1000000 in
    classical
    let : FiniteDimensional (Chapter10ResidueField v)
        (Chapter10ResidueField w) := chapter10_residue_degree_finite v w
    let Q := Chapter10ValueGroup w ⧸
      (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w)
    let : Fintype Q := Fintype.ofFinite Q
    let d : ℕ := Module.finrank (Chapter10ResidueField v)
      (Chapter10ResidueField w)
    let b : Module.Basis (Fin d) (Chapter10ResidueField v)
        (Chapter10ResidueField w) := Module.finBasis _ _
    let rep : Q → Chapter10ValueGroup w := fun q =>
      Classical.choose (QuotientGroup.mk_surjective q)
    have hrep (q : Q) : QuotientGroup.mk (rep q) = q :=
      Classical.choose_spec (QuotientGroup.mk_surjective q)
    have hvalmem (u : Chapter10ValueGroup w) : ∃ z : L, ∃ hz : w z ≠ 0,
        Units.mk0 (w z) hz = (u : Γ₀ˣ) := by
      have hu : (u : Γ₀ˣ).val ∈
          (Units.val '' (Chapter10ValueGroup w : Set Γ₀ˣ)) :=
        ⟨u, u.property, rfl⟩
      change (u : Γ₀ˣ).val ∈
        Units.val ''
          (MonoidWithZeroHom.valueGroup w.toMonoidWithZeroHom : Set Γ₀ˣ) at hu
      rw [MonoidWithZeroHom.valueGroup_eq_range w.toMonoidWithZeroHom] at hu
      rcases hu with ⟨hu, hne⟩
      rcases hu with ⟨z, hz⟩
      have hne_u : (u : Γ₀ˣ).val ≠ 0 := by exact hne
      have hz' : w z ≠ 0 := by
        have hz_eq : w z = (u : Γ₀ˣ).val := by simpa using hz
        rw [hz_eq]
        exact hne_u
      refine ⟨z, hz', ?_⟩
      apply Units.ext
      simpa using hz
    let x : Q → L := fun q => Classical.choose (hvalmem (rep q))
    have hx (q : Q) : w (x q) ≠ 0 :=
      Classical.choose (Classical.choose_spec (hvalmem (rep q)))
    let y₀ : Fin d → w.valuationSubring := fun i =>
      Classical.choose (IsLocalRing.residue_surjective (b i))
    have hy₀ (i : Fin d) :
        IsLocalRing.residue w.valuationSubring (y₀ i) = b i :=
      Classical.choose_spec (IsLocalRing.residue_surjective (b i))
    let y : Fin d → L := fun i => y₀ i
    have hyval (i : Fin d) : w (y i) = 1 := by
      have hbi : b i ≠ 0 := b.ne_zero i
      have hnot : y₀ i ∉ IsLocalRing.maximalIdeal w.valuationSubring := by
        intro hmem
        apply hbi
        rw [← hy₀ i]
        exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
      have hle : w (y i) ≤ 1 :=
        (Valuation.mem_valuationSubring_iff w (y i)).mpr (y₀ i).property
      have hnlt : ¬w (y i) < 1 := by
        intro hlt
        apply hnot
        exact (Valuation.mem_maximalIdeal_iff (v := w)).mpr hlt
      exact le_antisymm hle (le_of_not_gt hnlt)
    have hLIy : LinearIndependent K y := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      let T : Finset (Fin d) :=
        Finset.univ.filter (fun i => a i ≠ 0)
      have hTempty : T = ∅ := by
        by_contra hT
        have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
        let U : Finset Γ₀ :=
          T.image (fun i => w (algebraMap K L (a i)))
        have hUne : U.Nonempty := hTne.image _
        obtain ⟨i₀, hi₀T, hi₀eq⟩ :=
          Finset.mem_image.mp (Finset.max'_mem U hUne)
        have hai₀ : a i₀ ≠ 0 := (Finset.mem_filter.mp hi₀T).2
        have hamap₀ : algebraMap K L (a i₀) ≠ 0 := by
          simpa using (RingHom.injective (algebraMap K L)).ne hai₀
        have hw₀ : w (algebraMap K L (a i₀)) ≠ 0 :=
          (Valuation.ne_zero_iff w).mpr hamap₀
        have hmax (i : Fin d) (hiT : i ∈ T) :
            w (algebraMap K L (a i)) ≤
              w (algebraMap K L (a i₀)) := by
          calc
            w (algebraMap K L (a i)) ≤ U.max' hUne :=
              Finset.le_max' U _ (Finset.mem_image.mpr ⟨i, hiT, rfl⟩)
            _ = w (algebraMap K L (a i₀)) := hi₀eq.symm
        let c : Fin d → v.valuationSubring := fun i =>
          ⟨a i / a i₀, by
            by_cases hai : a i = 0
            · simp [hai]
            · have hiT : i ∈ T :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
              apply (Valuation.mem_valuationSubring_iff v _).mpr
              apply (Valuation.HasExtension.val_map_le_one_iff v w _).mp
              rw [map_div₀, w.map_div]
              exact (div_le_one₀ (w.pos_iff.mpr hamap₀)).mpr (hmax i hiT)
            ⟩
        have hnorm :
            (∑ i : Fin d, algebraMap K L (a i / a i₀) * y i) = 0 := by
          have ha' : (∑ i : Fin d, algebraMap K L (a i) * y i) = 0 := by
            simpa only [Algebra.smul_def] using ha
          calc
            (∑ i : Fin d, algebraMap K L (a i / a i₀) * y i) =
                ∑ i : Fin d,
                  (algebraMap K L (a i₀))⁻¹ *
                    (algebraMap K L (a i) * y i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [map_div₀]
              field_simp [hw₀]
            _ = (algebraMap K L (a i₀))⁻¹ *
                ∑ i : Fin d, algebraMap K L (a i) * y i := by
              rw [Finset.mul_sum]
            _ = 0 := by rw [ha', mul_zero]
        have hnormB :
            (∑ i : Fin d,
                (algebraMap v.valuationSubring w.valuationSubring (c i)) *
                  (y₀ i)) = 0 := by
          apply Subtype.ext
          simpa [c, y] using hnorm
        have hresnorm :=
          congrArg (IsLocalRing.residue w.valuationSubring) hnormB
        have hresrel :
            (∑ i : Fin d,
              algebraMap (Chapter10ResidueField v) (Chapter10ResidueField w)
                (IsLocalRing.residue v.valuationSubring (c i)) * b i) = 0 := by
          simpa only [map_sum, map_mul,
            Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap v w,
            hy₀, map_zero] using hresnorm
        have hc0 : ∀ i : Fin d,
            IsLocalRing.residue v.valuationSubring (c i) = 0 := by
          apply (Fintype.linearIndependent_iff.mp b.linearIndependent)
          simpa only [Algebra.smul_def] using hresrel
        have hc₀ : c i₀ = 1 := by
          apply Subtype.ext
          dsimp [c]
          exact div_self hai₀
        have honezero : (1 : Chapter10ResidueField v) = 0 := by
          calc
            (1 : Chapter10ResidueField v) =
                IsLocalRing.residue v.valuationSubring (c i₀) := by
              rw [hc₀]
              simp
            _ = 0 := hc0 i₀
        exact one_ne_zero honezero
      have hz : ∀ i : Fin d, a i = 0 := by
        intro i
        by_contra hai
        have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
        rw [hTempty] at hiT
        simp at hiT
      intro i
      exact hz i
    have hblock : ∀ (a : Fin d → K),
        (∑ j, algebraMap K L (a j) * y j) = 0 → ∀ j, a j = 0 := by
      intro a ha
      apply (Fintype.linearIndependent_iff.mp hLIy) a
      simpa only [Algebra.smul_def] using ha
    have hsum_value (a : Fin d → K)
        (ha : (∑ j, algebraMap K L (a j) * y j) ≠ 0) :
        ∃ j, a j ≠ 0 ∧
          w (∑ j, algebraMap K L (a j) * y j) =
            w (algebraMap K L (a j)) := by
      let T : Finset (Fin d) :=
        Finset.univ.filter (fun i => a i ≠ 0)
      have hTne : T.Nonempty := by
        by_contra hT
        apply ha
        have hz : ∀ i : Fin d, a i = 0 := by
          intro i
          by_contra hai
          exact hT ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩⟩
        simp [hz]
      let U : Finset Γ₀ :=
        T.image (fun i => w (algebraMap K L (a i)))
      have hUne : U.Nonempty := hTne.image _
      obtain ⟨i₀, hi₀T, hi₀eq⟩ :=
        Finset.mem_image.mp (Finset.max'_mem U hUne)
      have hai₀ : a i₀ ≠ 0 := (Finset.mem_filter.mp hi₀T).2
      have hamap₀ : algebraMap K L (a i₀) ≠ 0 := by
        simpa using (RingHom.injective (algebraMap K L)).ne hai₀
      have hw₀ : w (algebraMap K L (a i₀)) ≠ 0 :=
        (Valuation.ne_zero_iff w).mpr hamap₀
      have hmax (i : Fin d) (hiT : i ∈ T) :
          w (algebraMap K L (a i)) ≤
            w (algebraMap K L (a i₀)) := by
        calc
          w (algebraMap K L (a i)) ≤ U.max' hUne :=
            Finset.le_max' U _ (Finset.mem_image.mpr ⟨i, hiT, rfl⟩)
          _ = w (algebraMap K L (a i₀)) := hi₀eq.symm
      let c : Fin d → v.valuationSubring := fun i =>
        ⟨a i / a i₀, by
          by_cases hai : a i = 0
          · simp [hai]
          · have hiT : i ∈ T :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
            apply (Valuation.mem_valuationSubring_iff v _).mpr
            apply (Valuation.HasExtension.val_map_le_one_iff v w _).mp
            rw [map_div₀, w.map_div]
            exact (div_le_one₀ (w.pos_iff.mpr hamap₀)).mpr (hmax i hiT)
          ⟩
      let normB : w.valuationSubring :=
        ∑ i : Fin d,
          (algebraMap v.valuationSubring w.valuationSubring (c i)) * y₀ i
      have hnormB_coe : (normB : L) =
          ∑ i : Fin d, algebraMap K L (a i / a i₀) * y i := by
        simp [normB, c, y]
      have hresnorm_ne :
          IsLocalRing.residue w.valuationSubring normB ≠ 0 := by
        intro hres
        have hresrel :
            (∑ i : Fin d,
              algebraMap (Chapter10ResidueField v) (Chapter10ResidueField w)
                (IsLocalRing.residue v.valuationSubring (c i)) * b i) = 0 := by
          have hres' := hres
          simpa [normB, map_sum, map_mul,
            Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap v w,
            hy₀] using hres'
        have hc0 : ∀ i : Fin d,
            IsLocalRing.residue v.valuationSubring (c i) = 0 := by
          apply (Fintype.linearIndependent_iff.mp b.linearIndependent)
          simpa only [Algebra.smul_def] using hresrel
        have hc₀ : c i₀ = 1 := by
          apply Subtype.ext
          dsimp [c]
          exact div_self hai₀
        have honezero : (1 : Chapter10ResidueField v) = 0 := by
          calc
            (1 : Chapter10ResidueField v) =
                IsLocalRing.residue v.valuationSubring (c i₀) := by
              rw [hc₀]
              simp
            _ = 0 := hc0 i₀
        exact one_ne_zero honezero
      have hnormval : w (normB : L) = 1 := by
        have hle : w (normB : L) ≤ 1 :=
          (Valuation.mem_valuationSubring_iff w (normB : L)).mpr normB.property
        have hnlt : ¬w (normB : L) < 1 := by
          intro hlt
          apply hresnorm_ne
          exact (IsLocalRing.residue_eq_zero_iff _).mpr
            ((Valuation.mem_maximalIdeal_iff (v := w)).mpr hlt)
        exact le_antisymm hle (le_of_not_gt hnlt)
      have hnorm_eq :
          (∑ i : Fin d, algebraMap K L (a i / a i₀) * y i) =
            (algebraMap K L (a i₀))⁻¹ *
              ∑ i : Fin d, algebraMap K L (a i) * y i := by
        calc
          (∑ i : Fin d, algebraMap K L (a i / a i₀) * y i) =
              ∑ i : Fin d,
                (algebraMap K L (a i₀))⁻¹ *
                  (algebraMap K L (a i) * y i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_div₀]
            field_simp [hw₀]
          _ = (algebraMap K L (a i₀))⁻¹ *
              ∑ i : Fin d, algebraMap K L (a i) * y i := by
            rw [Finset.mul_sum]
      have hsum_eq :
          (∑ i : Fin d, algebraMap K L (a i) * y i) =
            algebraMap K L (a i₀) * (normB : L) := by
        calc
          (∑ i : Fin d, algebraMap K L (a i) * y i) =
              algebraMap K L (a i₀) *
                ((algebraMap K L (a i₀))⁻¹ *
                  ∑ i : Fin d, algebraMap K L (a i) * y i) := by
            field_simp [hw₀]
          _ = algebraMap K L (a i₀) *
              (∑ i : Fin d, algebraMap K L (a i / a i₀) * y i) := by
            rw [hnorm_eq]
          _ = algebraMap K L (a i₀) * (normB : L) := by
            rw [hnormB_coe]
      refine ⟨i₀, hai₀, ?_⟩
      rw [hsum_eq, w.map_mul, hnormval, mul_one]
    have hvalues : ∀ (a : Q × Fin d → K) (q q' : Q), q ≠ q' →
        (∑ j, algebraMap K L (a (q, j)) * y j) ≠ 0 →
        (∑ j, algebraMap K L (a (q', j)) * y j) ≠ 0 →
        w (x q * ∑ j, algebraMap K L (a (q, j)) * y j) ≠
          w (x q' * ∑ j, algebraMap K L (a (q', j)) * y j) := by
      intro a q q' hqq' hq hq'
      obtain ⟨j, haj, hj⟩ := hsum_value (fun j => a (q, j)) hq
      obtain ⟨j', haj', hj'⟩ := hsum_value (fun j => a (q', j)) hq'
      intro heq
      have hvj : v (a (q, j)) ≠ 0 :=
        (Valuation.ne_zero_iff v).mpr haj
      have hvj' : v (a (q', j')) ≠ 0 :=
        (Valuation.ne_zero_iff v).mpr haj'
      let uj : Chapter10ValueGroup v :=
        Chapter10ValueGroupGenerator v (a (q, j)) hvj
      let uj' : Chapter10ValueGroup v :=
        Chapter10ValueGroupGenerator v (a (q', j')) hvj'
      have huj : (uj : Γ₀ˣ) =
          Units.mk0 (v (a (q, j))) hvj := by rfl
      have huj' : (uj' : Γ₀ˣ) =
          Units.mk0 (v (a (q', j'))) hvj' := by rfl
      have hrepval :
          (rep q : Γ₀ˣ) * (uj : Γ₀ˣ) =
            (rep q' : Γ₀ˣ) * (uj' : Γ₀ˣ) := by
        have hxi := Classical.choose_spec (hvalmem (rep q))
        have hxi' := Classical.choose_spec (hvalmem (rep q'))
        have hxi_val : Units.mk0 (w (x q)) (hx q) = (rep q : Γ₀ˣ) := hxi.2
        have hxi'_val : Units.mk0 (w (x q')) (hx q') =
            (rep q' : Γ₀ˣ) := hxi'.2
        have hxi_val' : w (x q) = (rep q : Γ₀ˣ).val := by
          simpa using congrArg Units.val hxi_val
        have hxi'_val' : w (x q') = (rep q' : Γ₀ˣ).val := by
          simpa using congrArg Units.val hxi'_val
        apply Units.ext
        simpa [w.map_mul, hval, huj, huj', hj, hj', hxi_val', hxi'_val']
          using heq
      have hmem :
          ((uj : Γ₀ˣ) * (uj' : Γ₀ˣ)⁻¹) ∈ Chapter10ValueGroup v := by
        exact (Chapter10ValueGroup v).mul_mem uj.property
          ((Chapter10ValueGroup v).inv_mem uj'.property)
      let g : Chapter10ValueGroup w :=
        ⟨(rep q : Γ₀ˣ)⁻¹ * (rep q' : Γ₀ˣ), by
          exact (Chapter10ValueGroup w).mul_mem
            ((Chapter10ValueGroup w).inv_mem (rep q).property)
            (rep q').property⟩
      have huieq :
          ((rep q : Γ₀ˣ)⁻¹ * (rep q' : Γ₀ˣ) : Γ₀ˣ) =
            (uj : Γ₀ˣ) * (uj' : Γ₀ˣ)⁻¹ := by
        calc
          ((rep q : Γ₀ˣ)⁻¹ * (rep q' : Γ₀ˣ) : Γ₀ˣ) =
              (rep q : Γ₀ˣ)⁻¹ *
                ((rep q : Γ₀ˣ) * (uj : Γ₀ˣ)) *
                  (uj' : Γ₀ˣ)⁻¹ := by rw [hrepval]; simp [mul_assoc]
          _ = (uj : Γ₀ˣ) * (uj' : Γ₀ˣ)⁻¹ := by simp
      have hmem' : g ∈
          (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w) := by
        apply Subgroup.mem_subgroupOf.mpr
        change ((rep q : Γ₀ˣ)⁻¹ * (rep q' : Γ₀ˣ)) ∈ Chapter10ValueGroup v
        rw [huieq]
        exact hmem
      have hg : g = (rep q)⁻¹ * rep q' := by
        apply Subtype.ext
        rfl
      have hq0 :
          (QuotientGroup.mk (s :=
              (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w))
            (rep q) : Q) =
            QuotientGroup.mk (s :=
              (Chapter10ValueGroup v).subgroupOf (Chapter10ValueGroup w))
              (rep q') := by
        apply QuotientGroup.eq.mpr
        rw [← hg]
        exact hmem'
      have hq'' : q = q' := by
        calc
          q = QuotientGroup.mk (rep q) := (hrep q).symm
          _ = QuotientGroup.mk (rep q') := hq0
          _ = q' := hrep q'
      exact hqq' hq''
    let eQ : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
    let x' : Fin (Fintype.card Q) → L := fun i => x (eQ.symm i)
    have hx' (i : Fin (Fintype.card Q)) : x' i ≠ 0 := by
      simpa [x'] using (Valuation.ne_zero_iff w).mp (hx (eQ.symm i))
    have hvalues' : ∀ (a : Fin (Fintype.card Q) × Fin d → K)
        (i i' : Fin (Fintype.card Q)), i ≠ i' →
        (∑ j, algebraMap K L (a (i, j)) * y j) ≠ 0 →
        (∑ j, algebraMap K L (a (i', j)) * y j) ≠ 0 →
        w (x' i * ∑ j, algebraMap K L (a (i, j)) * y j) ≠
          w (x' i' * ∑ j, algebraMap K L (a (i', j)) * y j) := by
      intro a i i' hii hi hi'
      let a' : Q × Fin d → K := fun qj => a (eQ qj.1, qj.2)
      have hq : eQ.symm i ≠ eQ.symm i' := by
        intro heq
        apply hii
        exact eQ.symm.injective heq
      simpa [x', a'] using
        hvalues a' (eQ.symm i) (eQ.symm i') hq
          (by simpa [a'] using hi) (by simpa [a'] using hi')
    have hLI := chapter10_value_residue_product_independence v w x' y hx' hblock hvalues'
    have hcard := hLI.fintype_card_le_finrank
    simpa [Chapter10RamificationIndex, Chapter10ResidueDegree, Q, d,
      Nat.card_eq_fintype_card] using hcard

/-- Normalized discrete additive valuations. -/
def Chapter10DiscreteAddValuation {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Prop :=
  ∃ π : K, π ≠ 0 ∧ v π = 1 ∧
    ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = (n : WithTop ℤ)

/-- Units for an additive valuation. -/
def Chapter10AddValuationUnit {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (u : K) : Prop :=
  u ≠ 0 ∧ v u = 0

/-- Restriction of a normalized discrete valuation scales by the ramification index. -/
theorem chapter10_normalized_restriction_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (hv : Chapter10DiscreteAddValuation v)
    (hw : Chapter10DiscreteAddValuation w)
    (hext : v.IsEquiv (w.comap (algebraMap K L))) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : K, x ≠ 0 →
      w (algebraMap K L x) = e • v x := by
  rcases hv with ⟨π, hπ0, hπ, hv⟩
  rcases hw with ⟨Pi, hPi0, hPi, hw⟩
  obtain ⟨m, hm⟩ := hw (algebraMap K L π)
    (by simpa using (RingHom.injective (algebraMap K L)).ne hπ0)
  have hmpos : (0 : WithTop ℤ) < (m : WithTop ℤ) := by
    rw [← hm]
    have hlt_hidden :
        (AddValuation.toValuation v) π <
          (AddValuation.toValuation v) 1 := by
      simp only [AddValuation.toValuation_apply]
      change (OrderDual.toDual (v π)) < (OrderDual.toDual (v 1))
      rw [hπ, v.map_one]
      exact OrderDual.toDual_lt_toDual.mpr zero_lt_one
    have hlt_hidden' :=
      (hext.lt_iff_lt (x := π) (y := (1 : K))).mp hlt_hidden
    have hlt_add : w (algebraMap K L (1 : K)) <
        w (algebraMap K L π) := by
      change (OrderDual.toDual (w (algebraMap K L π))) <
        (OrderDual.toDual (w (algebraMap K L (1 : K)))) at hlt_hidden'
      exact OrderDual.toDual_lt_toDual.mp hlt_hidden'
    simpa using hlt_add
  have hm_int : 0 < m := by
    exact_mod_cast hmpos
  have hm0 : 0 ≤ m := by
    exact hm_int.le
  let e : ℕ := m.toNat
  have hme : (m : ℤ) = e := by
    simp [e, Int.toNat_of_nonneg hm0]
  have hepos : 0 < e := by
    have he_int : (0 : ℤ) < (e : ℤ) := by
      simpa [hme] using hm_int
    exact_mod_cast he_int
  refine ⟨e, hepos, ?_⟩
  intro x hx0
  obtain ⟨n, hn⟩ := hv x hx0
  have hone : ∀ z : ℕ, z • (1 : WithTop ℤ) = (z : WithTop ℤ) := by
    intro z
    induction z with
    | zero => simp
    | succ z ih =>
        rw [succ_nsmul, Nat.cast_succ, ih]
  have hnat : ∀ a b : ℕ,
      a • (b : WithTop ℤ) = b • (a : WithTop ℤ) := by
    intro a b
    induction b with
    | zero => simp
    | succ b ih =>
        rw [Nat.cast_succ, smul_add, succ_nsmul, ih, hone]
  have hnegcast : ∀ z : ℕ,
      (Int.negSucc z : WithTop ℤ) = -((z + 1 : ℕ) : WithTop ℤ) := by
    intro z
    simp [Int.negSucc_eq]
  have hpow_v : ∀ z : ℤ, v (π ^ z) = (z : WithTop ℤ) := by
    intro z
    cases z with
    | ofNat z =>
        change v (π ^ (z : ℤ)) = (z : WithTop ℤ)
        rw [zpow_natCast, v.map_pow, hπ, hone]
    | negSucc z =>
        rw [zpow_negSucc, v.map_inv, v.map_pow, hπ]
        rw [hnegcast z, hone]
  have hpow_w : ∀ z : ℤ,
      w (algebraMap K L (π ^ z)) = z • w (algebraMap K L π) := by
    intro z
    cases z with
    | ofNat z =>
        change w (algebraMap K L (π ^ (z : ℤ))) =
          (z : ℤ) • w (algebraMap K L π)
        rw [zpow_natCast, map_pow, w.map_pow, natCast_zsmul]
    | negSucc z =>
        rw [zpow_negSucc, map_inv₀, map_pow, w.map_inv, w.map_pow,
          negSucc_zsmul]
  have hv_eq : v x = v (π ^ n) := hn.trans (hpow_v n).symm
  have hw_eq : w (algebraMap K L x) =
      w (algebraMap K L (π ^ n)) :=
    (hext.eq_iff).mp hv_eq
  rw [hw_eq, hpow_w, hm, hme, hn]
  have hcast : ∀ z : ℕ,
      ((z : ℤ) : WithTop ℤ) = (z : WithTop ℤ) := by
    intro z
    norm_cast
  have hneg_nsmul : ∀ (a : ℕ) (b : WithTop ℤ),
      a • -b = -(a • b) := by
    intro a b
    induction a with
    | zero => simp
    | succ a ih =>
        simp only [succ_nsmul, ih]
        rw [neg_add_rev, add_comm]
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, hcast e, natCast_zsmul]
      exact hnat n e
  | negSucc n =>
      rw [hcast e, negSucc_zsmul, hnegcast n, hneg_nsmul]
      congr 1
      exact hnat (n + 1) e

/-- Uniformizers are related by π = u Piᵉ. -/
theorem chapter10_uniformizer_relation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (π : K) (Pi : L) (e : ℕ)
    (he : 0 < e) (hπ : v π = 1) (hPi : w Pi = 1)
    (hv : Chapter10DiscreteAddValuation v)
    (hw : Chapter10DiscreteAddValuation w)
    (hscale : ∀ x : K, x ≠ 0 →
      w (algebraMap K L x) = e • v x) :
    ∃ u : L, Chapter10AddValuationUnit w u ∧
      algebraMap K L π = u * Pi ^ e := by
  have _ := he
  have _ := hv
  have _ := hw
  have hπ0 : π ≠ 0 := by
    intro h
    subst π
    simp at hπ
  have hPi0 : Pi ≠ 0 := by
    intro h
    subst Pi
    simp at hPi
  have hpow0 : Pi ^ e ≠ 0 := pow_ne_zero _ hPi0
  let u : L := algebraMap K L π / Pi ^ e
  refine ⟨u, ?_, (div_mul_cancel₀ _ hpow0).symm⟩
  constructor
  · have hmap0 : algebraMap K L π ≠ 0 := by
      simpa using (RingHom.injective (algebraMap K L)).ne hπ0
    exact div_ne_zero hmap0 hpow0
  · dsimp [u]
    rw [div_eq_mul_inv, w.map_mul, w.map_inv, w.map_pow, hscale π hπ0, hπ, hPi]
    simp

/-- The residue-field injection is finite in the finite-extension setting. -/
theorem chapter10_ramification_residue_finite
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] [FiniteDimensional K L]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    [Valuation.HasExtension v w] :
    FiniteDimensional (Chapter10ResidueField v) (Chapter10ResidueField w) := by
  exact chapter10_residue_degree_finite v w

/-! ## 10.5. Several extensions and the fundamental inequality -/

/-- The numerical data attached to one branch. -/
structure Chapter10BranchInvariant where
  degree : ℕ
  e : ℕ
  f : ℕ

/-- The contribution ef of one branch. -/
def Chapter10BranchContribution (p : Chapter10BranchInvariant) : ℕ :=
  p.e * p.f

/-- A valuation branch together with its numerical profile. -/
structure Chapter10ValuationBranch {K L ΓK : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK) where
  valueGroup : Type*
  [orderedValueGroup : LinearOrderedCommGroupWithZero valueGroup]
  w : Valuation L valueGroup
  isExtension : v.IsEquiv (w.comap (algebraMap K L))
  extensionData : Chapter10HeterogeneousExtensionData v w isExtension
  profile : Chapter10BranchInvariant
  profile_e : profile.e = extensionData.ramificationIndex
  profile_f : profile.f = extensionData.residueDegree

/-- A finite list of branches containing every inequivalent extension. -/
def Chapter10CompleteBranchFamily
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK)
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v)) : Prop :=
  ∀ (ΓL : Type*) [LinearOrderedCommGroupWithZero ΓL]
      (w : Valuation L ΓL),
    v.IsEquiv (w.comap (algebraMap K L)) ↔
      ∃ b, b ∈ S ∧
        (letI : LinearOrderedCommGroupWithZero b.valueGroup := b.orderedValueGroup
         b.w.IsEquiv w)

/-- A branch profile is its ramification index and residue degree. -/
def Chapter10BranchProfileCorrect
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK)
    (b : Chapter10ValuationBranch (K := K) (L := L) v) : Prop :=
  letI : LinearOrderedCommGroupWithZero b.valueGroup := b.orderedValueGroup
  b.profile.degree = Module.finrank K L ∧
    b.profile.e = b.extensionData.ramificationIndex ∧
    b.profile.f = b.extensionData.residueDegree

/-- Residue degree as a function of the explicit extension equivalence. -/
noncomputable def Chapter10ResidueDegreeOfExtension
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [FiniteDimensional K L]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    (h : v.IsEquiv (w.comap (algebraMap K L))) : ℕ := by
  let : Valuation.HasExtension v w := ⟨h⟩
  exact Chapter10ResidueDegree v w

/-- There are only finitely many inequivalent extensions of a finite extension. -/
theorem chapter10_finitely_many_valuation_extensions
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK) :
    ∃ S : Finset (Chapter10ValuationBranch (K := K) (L := L) v),
      Chapter10CompleteBranchFamily v S := by
  sorry

/-- The sum of ef over all branches is bounded by the extension degree. -/
theorem chapter10_fundamental_inequality
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] [FiniteDimensional K L]
    (v : Valuation K ΓK) :
    ∃ S : Finset (Chapter10ValuationBranch (K := K) (L := L) v),
      Chapter10CompleteBranchFamily v S ∧
        Finset.sum S (fun b => Chapter10BranchContribution b.profile) ≤
          Module.finrank K L := by
  sorry

/-- An immediate valuation extension has unchanged value group and induced residue field. -/
def Chapter10ImmediateValuationExtension
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) (w : Valuation L Γ₀)
    (h : v.IsEquiv (w.comap (algebraMap K L))) : Prop := by
  letI : Valuation.HasExtension v w := ⟨h⟩
  exact Chapter10ValueGroup v = Chapter10ValueGroup w ∧
    Function.Bijective (Chapter10ResidueFieldMap v w)

/-- Tensoring a finite extension with a field extension preserves its dimension. -/
theorem chapter10_henselized_tensor_dimension
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh] [Algebra Kh (L ⊗[K] Kh)]
    [FiniteDimensional K L] :
    Module.finrank Kh (Kh ⊗[K] L) = Module.finrank K L := by
  exact Module.finrank_baseChange (R := Kh) (S := K) (M' := L)

/-- The base-change tensor product used to separate the branches. -/
abbrev Chapter10HenselizedTensor (K L Kh : Type*) [CommRing K] [CommRing L]
    [CommRing Kh] [Algebra K L] [Algebra K Kh] : Type _ := L ⊗[K] Kh

/-- Maximal ideals of an algebra are the local-factor indices. -/
def Chapter10TensorMaximalIdeals {C : Type*} [CommRing C] : Set (Ideal C) :=
  {P | P.IsMaximal}

/-- The finite base-change tensor product has finitely many maximal local factors. -/
theorem chapter10_henselized_tensor_has_finitely_many_factors
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh] [FiniteDimensional K L]
    [Algebra Kh (L ⊗[K] Kh)] [Module.Finite Kh (L ⊗[K] Kh)]
    : Set.Finite (Chapter10TensorMaximalIdeals (C := L ⊗[K] Kh)) := by
  let : IsArtinianRing (L ⊗[K] Kh) :=
    IsArtinianRing.of_finite Kh (L ⊗[K] Kh)
  exact IsArtinianRing.setOfPred_isMaximal_finite (L ⊗[K] Kh)

/-- Residue-field dimensions of the local base-change tensor factors are bounded by the total
dimension; nilpotent Artinian multiplicities account for the possible gap. -/
theorem chapter10_henselized_tensor_factor_dimensions
    {K L Kh : Type*} [Field K] [Field L] [Field Kh]
    [Algebra K L] [Algebra K Kh]
    [FiniteDimensional K L]
    (factors : Finset (Ideal (L ⊗[K] Kh)))
    (hmax : ∀ P ∈ factors, P.IsMaximal)
    (hexhaustive : ∀ P, P.IsMaximal ↔ P ∈ factors) :
    (letI : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
     Finset.sum factors
         (fun P => Module.finrank Kh ((L ⊗[K] Kh) ⧸ P)) ≤
       Module.finrank K L) := by
  let : Algebra Kh (Kh ⊗[K] L) := Algebra.TensorProduct.leftAlgebra
  let : Algebra Kh (L ⊗[K] Kh) := Algebra.TensorProduct.rightAlgebra
  let : Module.Finite Kh (Kh ⊗[K] L) :=
    Module.Finite.base_change (R := K) (A := Kh) (M := L)
  let : Module.Finite Kh (L ⊗[K] Kh) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight K Kh L).toLinearEquiv
  let : IsArtinianRing (L ⊗[K] Kh) :=
    IsArtinianRing.of_finite Kh (L ⊗[K] Kh)
  let : Finite (PrimeSpectrum (L ⊗[K] Kh)) := inferInstance
  let : Fintype (PrimeSpectrum (L ⊗[K] Kh)) := Fintype.ofFinite _
  have hdim := IsArtinianRing.finrank_eq_sum_primeSpectrum
    (L ⊗[K] Kh) Kh
  have hquot (p : PrimeSpectrum (L ⊗[K] Kh)) :
      Module.finrank Kh ((L ⊗[K] Kh) ⧸ p.asIdeal) ≤
        Module.finrank Kh (Localization.AtPrime p.asIdeal) := by
    let : p.asIdeal.IsMaximal := by
      rw [← IsArtinianRing.isPrime_iff_isMaximal]
      exact p.isPrime
    let f : (L ⊗[K] Kh) →ₐ[Kh] ((L ⊗[K] Kh) ⧸ p.asIdeal) :=
      Ideal.Quotient.mkₐ Kh p.asIdeal
    have hf : ∀ y : p.asIdeal.primeCompl, IsUnit (f y) := by
      intro y
      let : Field ((L ⊗[K] Kh) ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
      change IsUnit (Ideal.Quotient.mk p.asIdeal y)
      rw [isUnit_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_primeCompl_iff.mp y.property
    let g : Localization.AtPrime p.asIdeal →ₐ[Kh]
        ((L ⊗[K] Kh) ⧸ p.asIdeal) :=
      IsLocalization.liftAlgHom hf
    have hg : Function.Surjective g := by
      intro z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective Kh p.asIdeal z
      refine ⟨algebraMap (L ⊗[K] Kh) (Localization.AtPrime p.asIdeal) x, ?_⟩
      rw [IsLocalization.liftAlgHom_apply]
      simp [f]
    let : Module.Finite Kh (Localization.AtPrime p.asIdeal) :=
      Module.Finite.of_surjective
        (IsScalarTower.toAlgHom Kh (L ⊗[K] Kh)
          (Localization.AtPrime p.asIdeal)).toLinearMap
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl
          (Localization.AtPrime p.asIdeal))
    exact LinearMap.finrank_le_finrank_of_surjective (f := g.toLinearMap) hg
  let e : {P // P ∈ factors} ≃ PrimeSpectrum (L ⊗[K] Kh) :=
    { toFun := fun P =>
        ⟨P.1, (IsArtinianRing.isPrime_iff_isMaximal P.1).mpr
          (hmax P.1 P.2)⟩
      invFun := fun p =>
        ⟨p.asIdeal, (hexhaustive p.asIdeal).mp
          ((IsArtinianRing.isPrime_iff_isMaximal p.asIdeal).mp p.isPrime)⟩
      left_inv := by
        intro P
        rfl
      right_inv := by
        intro p
        change (⟨p.asIdeal, _⟩ : PrimeSpectrum (L ⊗[K] Kh)) = p
        rfl }
  have hsum0 : Finset.sum factors (fun P =>
      Module.finrank Kh ((L ⊗[K] Kh) ⧸ P)) =
      ∑ P : {P // P ∈ factors},
        Module.finrank Kh ((L ⊗[K] Kh) ⧸ P.1) := by
    rw [Finset.sum_subtype factors (p := fun P => P ∈ factors)
      (fun P => Iff.rfl)]
  have hsum1 : (∑ P : {P // P ∈ factors},
      Module.finrank Kh ((L ⊗[K] Kh) ⧸ P.1)) =
      ∑ p : PrimeSpectrum (L ⊗[K] Kh),
        Module.finrank Kh ((L ⊗[K] Kh) ⧸ p.asIdeal) := by
    apply Fintype.sum_equiv e
    intro P
    rfl
  rw [hsum0, hsum1]
  calc
    (∑ p : PrimeSpectrum (L ⊗[K] Kh),
        Module.finrank Kh ((L ⊗[K] Kh) ⧸ p.asIdeal)) ≤
        ∑ p : PrimeSpectrum (L ⊗[K] Kh),
          Module.finrank Kh (Localization.AtPrime p.asIdeal) :=
      Finset.sum_le_sum (fun p _ => hquot p)
    _ = Module.finrank Kh (L ⊗[K] Kh) := hdim.symm
    _ = Module.finrank K L := by
      rw [← Module.finrank_baseChange (R := Kh) (S := K) (M' := L)]
      exact (Algebra.TensorProduct.commRight K Kh L).toLinearEquiv.finrank_eq.symm

/-- The defect records the possible loss in a local tensor factor. -/
def Chapter10Defect (degree e f : ℕ) : ℚ :=
  (degree : ℚ) / ((e * f : ℕ) : ℚ)

/-- Defect one is exactly equality in the fundamental inequality. -/
theorem chapter10_defect_eq_one_iff
    (degree e f : ℕ) (hpos : 0 < e * f) (hdiv : e * f ∣ degree) :
    Chapter10Defect degree e f = 1 ↔ degree = e * f := by
  constructor
  · intro h
    unfold Chapter10Defect at h
    have hne : (e * f : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hpos)
    field_simp [hne] at h
    exact_mod_cast h
  · intro h
    subst degree
    unfold Chapter10Defect
    field_simp [show (e * f : ℚ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hpos)]

/-- A numerical profile is defectless when its degree is ef. -/
def Chapter10DefectlessProfile (p : Chapter10BranchInvariant) : Prop :=
  p.degree = p.e * p.f

/-- The finite normalization hypothesis in the DVR equality theorem. -/
def Chapter10FiniteNormalization (A B : Type*) [Semiring A]
    [AddCommMonoid B] [Module A B] : Prop :=
  Module.Finite A B

/-- Finite normalization of a DVR gives equality in the sum formula. -/
theorem chapter10_finite_dvr_normalization_fundamental_equality
    {A K L ΓK : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [LinearOrderedCommGroupWithZero ΓK]
    (v : Valuation K ΓK) (hA : v.Integers A)
    (hfinite : Module.Finite A (integralClosure A L))
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v))
    (hcomplete : Chapter10CompleteBranchFamily v S)
    (hprofile : ∀ b ∈ S, Chapter10BranchProfileCorrect v b) :
    Finset.sum S (fun b => Chapter10BranchContribution b.profile) = Module.finrank K L := by
  sorry

/-- The normalization of a ring in an algebra, named for the Dedekind case. -/
noncomputable def Chapter10Normalization (A L : Type*) [CommRing A] [CommRing L]
    [Algebra A L] : Subalgebra A L :=
  integralClosure A L

/-- Finite separable extensions of Dedekind domains have finite normalization. -/
theorem chapter10_dedekind_separable_normalization_finite
    {A K L : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsFractionRing A K] [IsScalarTower A K L]
    [FiniteDimensional K L]
    (hseparable : Algebra.IsSeparable K L) :
    Module.Finite A (Chapter10Normalization A L) := by
  exact IsIntegralClosure.finite A K L (integralClosure A L)

/-- In the discrete setting, finite normalization gives the same equality. -/
theorem chapter10_complete_discrete_valuation_defectless
    {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀)
    [IsDiscreteValuationRing v.valuationSubring]
    (hfinite : Module.Finite v.valuationSubring
      (integralClosure v.valuationSubring L))
    (S : Finset (Chapter10ValuationBranch (K := K) (L := L) v))
    (hcomplete : Chapter10CompleteBranchFamily v S)
    (hprofile : ∀ b ∈ S, Chapter10BranchProfileCorrect v b) :
    Finset.sum S (fun b => Chapter10BranchContribution b.profile) = Module.finrank K L := by
  let : IsFractionRing v.valuationSubring K :=
    (Valuation.valuationSubring.integers v).isFractionRing
  exact chapter10_finite_dvr_normalization_fundamental_equality
    (A := v.valuationSubring) (K := K) (L := L) v
    (Valuation.valuationSubring.integers v) hfinite S hcomplete hprofile

/-- Henselian valuation rings have one branch over an algebraic extension. -/
theorem chapter10_henselian_valuation_has_unique_branch
    {K L Γ₀ Γ₁ Γ₂ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂] [Algebra.IsAlgebraic K L]
    (v : Valuation K Γ₀) [HenselianLocalRing v.valuationSubring]
    (w₁ : Valuation L Γ₁) (w₂ : Valuation L Γ₂)
    (h₁ : v.IsEquiv (w₁.comap (algebraMap K L)))
    (h₂ : v.IsEquiv (w₂.comap (algebraMap K L))) :
    w₁.IsEquiv w₂ := by
  sorry

/-- Complete nonarchimedean fields are henselian. -/
theorem chapter10_complete_nonarchimedean_is_henselian
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] :
    HenselianLocalRing K := by
  infer_instance

/-! ## 10.6. Finite extensions of complete fields -/

/-- Coordinate max norm attached to a finite basis. -/
def Chapter10CoordinateNorm {K L ι : Type*} [NormedField K]
    [AddCommGroup L] [Module K L] [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι K L) : L → ℝ :=
  fun x => Finset.univ.sup' Finset.univ_nonempty (fun i => ‖b.repr x i‖)

/-- Two real-valued norms are equivalent up to positive constants. -/
def Chapter10EquivalentRealNorms {L : Type*} (N M : L → ℝ) : Prop :=
  ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
    (∀ x, N x ≤ c * M x) ∧ (∀ x, M x ≤ d * N x)

/-- Coordinate Cauchy condition, stated without choosing a topology on L. -/
def Chapter10CauchyInNorm {L : Type*} [AddGroup L]
    (N : L → ℝ) (s : ℕ → L) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ m n : ℕ,
    N₀ ≤ m → N₀ ≤ n → N (s m - s n) < ε

/-- Convergence in a specified real-valued norm. -/
def Chapter10TendsToInNorm {L : Type*} [AddGroup L]
    (N : L → ℝ) (s : ℕ → L) (x : L) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ,
    N₀ ≤ n → N (s n - x) < ε

/-- The coordinate max norm is complete when the base field is complete. -/
theorem chapter10_coordinate_norm_complete
    {K L ι : Type*} [NormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι K L) (s : ℕ → L)
    (hs : Chapter10CauchyInNorm (Chapter10CoordinateNorm b) s) :
    ∃ x : L, Chapter10TendsToInNorm (Chapter10CoordinateNorm b) s x := by
  let coeff : ι → ℕ → K := fun i n => b.repr (s n) i
  have hcoeff : ∀ i, CauchySeq (coeff i) := by
    intro i
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hcoord : ‖b.repr (s m - s n) i‖ < ε := by
      have hsup := hN m n hm hn
      exact lt_of_le_of_lt (Module.Basis.norm_repr_le_norm b i) hsup
    rw [map_sub] at hcoord
    change ‖(b.repr (s m)) i - (b.repr (s n)) i‖ < ε at hcoord
    change dist (coeff i m) (coeff i n) < ε
    simpa only [dist_eq_norm, coeff] using hcoord
  choose lim hlim using fun i => cauchySeq_tendsto_of_complete (hcoeff i)
  let x : L := (b.equivFun).symm lim
  refine ⟨x, ?_⟩
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, ∀ i ∈ (Finset.univ : Finset ι),
      ‖b.repr (s n - x) i‖ < ε := by
    rw [Finset.eventually_all]
    intro i hi
    have hi' := (Metric.tendsto_atTop.1 (hlim i)) ε hε
    rcases hi' with ⟨N, hN⟩
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    have hxi : b.repr x i = lim i := by
      change (b.equivFun x) i = lim i
      dsimp [x]
      exact congrFun (b.equivFun.apply_symm_apply lim) i
    rw [map_sub]
    change ‖(b.repr (s n)) i - (b.repr x) i‖ < ε
    rw [hxi]
    simpa only [coeff, dist_eq_norm] using hN n hn
  rcases (Filter.eventually_atTop.1 hevent) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  change Finset.univ.sup' Finset.univ_nonempty (fun i => ‖b.repr (s n - x) i‖) < ε
  rw [Finset.sup'_lt_iff Finset.univ_nonempty]
  intro i hi
  exact hN n hn i hi

/-- Every K-linear endomorphism is bounded for a coordinate norm. -/
theorem chapter10_coordinate_norm_eq_pi_norm
    {K L ι : Type*} [NormedField K] [AddCommGroup L] [Module K L]
    [Fintype ι] [Nonempty ι] (b : Module.Basis ι K L) (x : L) :
    Chapter10CoordinateNorm b x = ‖b.equivFun x‖ := by
  simp only [Chapter10CoordinateNorm, Pi.norm_def, Module.Basis.equivFun_apply]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    have h := Finset.le_sup' (fun j : ι => ‖b.repr x j‖₊) hi
    rw [Finset.sup'_eq_sup Finset.univ_nonempty] at h
    simpa only [coe_nnnorm] using (NNReal.coe_le_coe.mpr h)
  · obtain ⟨i, hi, hi_sup⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : ι => ‖b.repr x i‖₊)
    rw [← Finset.sup'_eq_sup Finset.univ_nonempty, hi_sup]
    simpa only [coe_nnnorm] using
      (Finset.le_sup' (fun j : ι => ‖b.repr x j‖) hi)

theorem chapter10_coordinate_norm_linear_map_bound
    {K L ι : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L]
    [Fintype ι] [Nonempty ι] [FiniteDimensional K L]
    (b : Module.Basis ι K L) (T : L →ₗ[K] L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : L,
      Chapter10CoordinateNorm b (T x) ≤
        C * Chapter10CoordinateNorm b x := by
  let Fₗ : (ι → K) →ₗ[K] (ι → K) :=
    b.equivFun.toLinearMap.comp (T.comp b.equivFun.symm.toLinearMap)
  let F : (ι → K) →L[K] (ι → K) :=
    { toLinearMap := Fₗ
      cont := by exact LinearMap.continuous_of_finiteDimensional Fₗ }
  obtain ⟨C, hC, hF⟩ := F.isBoundedLinearMap.bound
  refine ⟨C, le_of_lt hC, ?_⟩
  have hcoord (y : L) : Chapter10CoordinateNorm b y = ‖b.equivFun y‖ :=
    chapter10_coordinate_norm_eq_pi_norm b y
  have hF_apply (x : L) : F (b.equivFun x) = b.equivFun (T x) := by
    change Fₗ (b.equivFun x) = b.equivFun (T x)
    simp [Fₗ]
  intro x
  have h := hF (b.equivFun x)
  calc
    Chapter10CoordinateNorm b (T x) = ‖b.equivFun (T x)‖ := hcoord _
    _ = ‖F (b.equivFun x)‖ := by rw [hF_apply]
    _ ≤ C * ‖b.equivFun x‖ := h
    _ = C * Chapter10CoordinateNorm b x := by rw [hcoord]

/-- Coordinate norms from two bases are equivalent. -/
theorem chapter10_coordinate_norms_equivalent
    {K L ι κ : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L]
    [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    [FiniteDimensional K L]
    (b : Module.Basis ι K L) (c : Module.Basis κ K L) :
    Chapter10EquivalentRealNorms (Chapter10CoordinateNorm b)
      (Chapter10CoordinateNorm c) := by
  let Fbcₗ : (ι → K) →ₗ[K] (κ → K) :=
    c.equivFun.toLinearMap.comp b.equivFun.symm.toLinearMap
  let Fcbₗ : (κ → K) →ₗ[K] (ι → K) :=
    b.equivFun.toLinearMap.comp c.equivFun.symm.toLinearMap
  let Fbc : (ι → K) →L[K] (κ → K) :=
    { toLinearMap := Fbcₗ
      cont := by exact LinearMap.continuous_of_finiteDimensional Fbcₗ }
  let Fcb : (κ → K) →L[K] (ι → K) :=
    { toLinearMap := Fcbₗ
      cont := by exact LinearMap.continuous_of_finiteDimensional Fcbₗ }
  obtain ⟨Cbc, hCbc, hbc⟩ := Fbc.isBoundedLinearMap.bound
  obtain ⟨Ccb, hCcb, hcb⟩ := Fcb.isBoundedLinearMap.bound
  have hcoordb (x : L) : Chapter10CoordinateNorm b x = ‖b.equivFun x‖ :=
    chapter10_coordinate_norm_eq_pi_norm b x
  have hcoordc (x : L) : Chapter10CoordinateNorm c x = ‖c.equivFun x‖ :=
    chapter10_coordinate_norm_eq_pi_norm c x
  have hbc_apply (x : L) : Fbc (b.equivFun x) = c.equivFun x := by
    change Fbcₗ (b.equivFun x) = c.equivFun x
    simp [Fbcₗ]
  have hcb_apply (x : L) : Fcb (c.equivFun x) = b.equivFun x := by
    change Fcbₗ (c.equivFun x) = b.equivFun x
    simp [Fcbₗ]
  refine ⟨Ccb, Cbc, hCcb, hCbc, ?_, ?_⟩
  · intro x
    calc
      Chapter10CoordinateNorm b x = ‖b.equivFun x‖ := hcoordb _
      _ = ‖Fcb (c.equivFun x)‖ := by rw [hcb_apply]
      _ ≤ Ccb * ‖c.equivFun x‖ := hcb (c.equivFun x)
      _ = Ccb * Chapter10CoordinateNorm c x := by rw [hcoordc]
  · intro x
    calc
      Chapter10CoordinateNorm c x = ‖c.equivFun x‖ := hcoordc _
      _ = ‖Fbc (b.equivFun x)‖ := by rw [hbc_apply]
      _ ≤ Cbc * ‖b.equivFun x‖ := hbc (b.equivFun x)
      _ = Cbc * Chapter10CoordinateNorm b x := by rw [hcoordb]

/-- Multiplication is bounded by a constant times the product of coordinate norms. -/
theorem chapter10_coordinate_norm_multiplication_bound
    {K L ι : Type*} [NormedField K] [IsUltrametricDist K]
    [Field L] [Algebra K L]
    [Fintype ι] [Nonempty ι] [FiniteDimensional K L]
    (b : Module.Basis ι K L) (i : ι) (hBi : b i = (1 : L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : L,
      Chapter10CoordinateNorm b (x * y) ≤
        C * Chapter10CoordinateNorm b x * Chapter10CoordinateNorm b y := by
  obtain ⟨C, hC, hmul⟩ :=
    Module.Basis.norm_mul_le_const_mul_norm (B := b) hBi
      IsUltrametricDist.isNonarchimedean_norm
  refine ⟨C, le_of_lt hC, ?_⟩
  intro x y
  simpa [Chapter10CoordinateNorm, Module.Basis.norm] using hmul x y

/-- Nonarchimedean triangle inequality for a real-valued norm. -/
def Chapter10NonarchimedeanNorm {L : Type*} [Add L] (N : L → ℝ) : Prop :=
  ∀ x y : L, N (x + y) ≤ max (N x) (N y)

/-- Extension of the base-field norm. -/
def Chapter10ExtendsBaseNorm {K L : Type*} [NormedField K]
    [Field L] [Algebra K L] (N : L → ℝ) : Prop :=
  ∀ x : K, N (algebraMap K L x) = ‖x‖

/-- Power multiplicativity, including the norm formula's uniqueness condition. -/
def Chapter10PowerMultiplicative {L : Type*} [Pow L ℕ] (N : L → ℝ) : Prop :=
  ∀ (x : L) (n : ℕ), N (x ^ n) = N x ^ n

/-- The property characterizing the unique nonarchimedean extension norm. -/
def Chapter10UniqueExtensionNormProperty
    {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    (N : AlgebraNorm K L) : Prop :=
  Chapter10NonarchimedeanNorm (N : L → ℝ) ∧
    Chapter10PowerMultiplicative (N : L → ℝ) ∧
    Chapter10ExtendsBaseNorm (K := K) (L := L) (N : L → ℝ)


/-- The actual absolute-value axioms for an algebraic extension. -/
def Chapter10AlgebraicExtensionNormProperty
    {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    (N : L → ℝ) : Prop :=
  N 0 = 0 ∧ N 1 = 1 ∧
    (∀ x, 0 ≤ N x) ∧ (∀ x, N x = 0 ↔ x = 0) ∧
    (∀ x y, N (x * y) = N x * N y) ∧
    (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧
    Chapter10ExtendsBaseNorm (K := K) (L := L) N
/-- Any nonarchimedean norm on a finite extension is equivalent to a coordinate norm. -/
theorem chapter10_nonarchimedean_norm_equivalent_to_coordinate_norm
    {K L ι : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    [FiniteDimensional K L]
    (b : Module.Basis ι K L) (N : AlgebraNorm K L)
    (_hN : Chapter10NonarchimedeanNorm (N : L → ℝ)) :
    Chapter10EquivalentRealNorms (N : L → ℝ) (Chapter10CoordinateNorm b) := by
  let : NormedRing L := N.toRingNorm.toNormedRing
  let : NormedSpace K L :=
    { norm_smul_le := fun k x => le_of_eq (map_smul_eq_mul N k x) }
  let Fₗ : L →ₗ[K] (ι → K) := b.equivFun.toLinearMap
  let Gₗ : (ι → K) →ₗ[K] L := b.equivFun.symm.toLinearMap
  let F : L →L[K] (ι → K) :=
    { toLinearMap := Fₗ
      cont := by exact LinearMap.continuous_of_finiteDimensional Fₗ }
  let G : (ι → K) →L[K] L :=
    { toLinearMap := Gₗ
      cont := by exact LinearMap.continuous_of_finiteDimensional Gₗ }
  obtain ⟨c, hc, hG⟩ := G.isBoundedLinearMap.bound
  obtain ⟨d, hd, hF⟩ := F.isBoundedLinearMap.bound
  have hcoord (y : L) : Chapter10CoordinateNorm b y = ‖b.equivFun y‖ :=
    chapter10_coordinate_norm_eq_pi_norm b y
  have hF_apply (x : L) : F x = b.equivFun x := by
    change Fₗ x = b.equivFun x
    simp [Fₗ]
  have hG_apply (x : L) : G (F x) = x := by
    change Gₗ (Fₗ x) = x
    simp [Fₗ, Gₗ]
  refine ⟨c, d, hc, hd, ?_, ?_⟩
  · intro x
    have h := hG (F x)
    calc
      N x = ‖x‖ := rfl
      _ = ‖G (F x)‖ := by rw [hG_apply]
      _ ≤ c * ‖F x‖ := h
      _ = c * Chapter10CoordinateNorm b x := by rw [hF_apply, hcoord]
  · intro x
    have h := hF x
    calc
      Chapter10CoordinateNorm b x = ‖F x‖ := by rw [hF_apply, hcoord]
      _ ≤ d * ‖x‖ := h
      _ = d * N x := by rfl

/-- The reverse inequality in the finite-dimensional nonarchimedean norm lemma. -/
theorem chapter10_nonarchimedean_norm_reverse_coordinate_bound
    {K L ι : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [Fintype ι] [Nonempty ι]
    [FiniteDimensional K L]
    (b : Module.Basis ι K L) (N : AlgebraNorm K L)
    (hN : Chapter10NonarchimedeanNorm (N : L → ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : L,
      c * Chapter10CoordinateNorm b x ≤ N x := by
  obtain ⟨c, d, hc, hd, _hupper, hlower⟩ :=
    chapter10_nonarchimedean_norm_equivalent_to_coordinate_norm b N hN
  refine ⟨d⁻¹, inv_pos.mpr hd, ?_⟩
  intro x
  calc
    d⁻¹ * Chapter10CoordinateNorm b x ≤ d⁻¹ * (d * N x) :=
      mul_le_mul_of_nonneg_left (hlower x) (le_of_lt (inv_pos.mpr hd))
    _ = N x := by field_simp

/-- The one-dimensional induction step uses a positive distance from a closed subspace. -/
theorem chapter10_closed_subspace_distance_step
    {K L : Type*} [NormedField K] [CompleteSpace K]
    [NormedField L] [Algebra K L] (W : Submodule K L) (e : L)
    (hclosed : IsClosed (W : Set L)) (he : e ∉ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : W, δ ≤ ‖e - w‖ := by
  have hWnonempty : (W : Set L).Nonempty := ⟨0, W.zero_mem⟩
  let δ : ℝ := Metric.infDist e (W : Set L)
  refine ⟨δ, ?_, ?_⟩
  · exact (hclosed.notMem_iff_infDist_pos hWnonempty).mp he
  · intro w
    simpa [δ, dist_eq_norm] using Metric.infDist_le_dist_of_mem w.property

/-- Every finite algebraic extension of a complete normed field is complete. -/
theorem chapter10_finite_extension_is_complete
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
    CompleteSpace L := by
  exact FiniteDimensional.complete K L

/--
Uniqueness over an arbitrary algebraic extension.  The values are compared
as real absolute values, so this statement does not silently fix a value
group for the algebraic extension.
-/
theorem chapter10_unique_complete_extension_norm
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] :
    ∃ N : L → ℝ,
      Chapter10AlgebraicExtensionNormProperty (K := K) (L := L) N ∧
        ∀ N' : L → ℝ,
          Chapter10AlgebraicExtensionNormProperty (K := K) (L := L) N' →
            ∀ x, N' x = N x := by
  let S : AlgebraNorm K L := spectralAlgNorm K L
  have hS : Chapter10AlgebraicExtensionNormProperty (K := K) (L := L) S := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [S, spectralAlgNorm_def] using (spectralNorm_zero (K := K) (L := L))
    · simpa [S] using (spectralAlgNorm_one (K := K) (L := L))
    · intro x
      simpa [S, spectralAlgNorm_def] using (spectralNorm_nonneg (K := K) (L := L) x)
    · intro x
      exact map_eq_zero_iff_eq_zero S
    · intro x y
      simpa [S] using (spectralAlgNorm_mul (K := K) (L := L) x y)
    · intro x y
      simpa [S, spectralAlgNorm_def] using
        (isNonarchimedean_spectralNorm (K := K) (L := L) x y)
    · intro k
      simpa [S] using (spectralAlgNorm_extends (K := K) (L := L) k)
  refine ⟨S, hS, ?_⟩
  intro N' hN' x
  rcases hN' with ⟨h0, h1, hpos, hzero, hmul, hadd, hext⟩
  let f : AbsoluteValue L ℝ :=
    { toFun := N'
      map_mul' := hmul
      nonneg' := hpos
      eq_zero' := hzero
      add_le' := by
        intro a b
        refine (hadd a b).trans ?_
        rw [max_le_iff]
        exact ⟨le_add_of_nonneg_right (hpos b), le_add_of_nonneg_left (hpos a)⟩ }
  have hf := spectralNorm_unique_field_norm_ext (K := K) (L := L) (f := f) hext x
  simpa [f, S, spectralAlgNorm_def] using hf

/-- K-automorphisms preserve the unique extension norm. -/
theorem chapter10_automorphism_preserves_unique_norm
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (N : AlgebraNorm K L)
    (hN : Chapter10UniqueExtensionNormProperty N)
    (σ : L ≃ₐ[K] L) :
    ∀ x : L, N (σ x) = N x := by
  have hp : IsPowMul N := fun x n _hn => hN.2.1 x n
  have hspec : N = spectralAlgNorm K L := spectralNorm_unique hp
  intro x
  rw [hspec]
  simpa [spectralAlgNorm_def] using
    (spectralNorm_eq_of_equiv (K := K) (L := L) σ x).symm

/-- Norm/product formula for a finite extension. -/
def Chapter10NormProductFormula
    {K L : Type*} [NormedField K] [Field L] [Algebra K L]
    (N : L → ℝ) : Prop :=
  ∀ x : L,
    N x = Real.rpow ‖Algebra.norm K x‖
      ((Module.finrank K L : ℝ)⁻¹)

theorem chapter10_complete_extension_norm_product_formula
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (N : AlgebraNorm K L)
    (hN : Chapter10UniqueExtensionNormProperty N) :
    Chapter10NormProductFormula (K := K) (L := L) (N : L → ℝ) := by
  have hp : IsPowMul N := fun x n _hn => hN.2.1 x n
  have hspec : N = spectralAlgNorm K L := spectralNorm_unique hp
  intro x
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hnorm_gen :
      ‖Algebra.norm K (IntermediateField.AdjoinSimple.gen K x)‖ =
        ‖(minpoly K x).coeff 0‖ := by
    have hpb :=
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
        (IntermediateField.adjoin.powerBasis hxint)
    simpa [IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.minpoly_gen] using
      congrArg (fun z : K => ‖z‖) hpb
  have hnorm :
      ‖Algebra.norm K x‖ =
        ‖(minpoly K x).coeff 0‖ ^
          (Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L) := by
    rw [Algebra.norm_eq_norm_adjoin K x, norm_pow, hnorm_gen]
  have hdim :
      (minpoly K x).natDegree *
          Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L =
        Module.finrank K L := by
    rw [← IntermediateField.adjoin.finrank hxint]
    exact Module.finrank_mul_finrank K (IntermediateField.adjoin K ({x} : Set L)) L
  have hdim_real :
      ((minpoly K x).natDegree : ℝ) *
          (Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L : ℝ) =
        (Module.finrank K L : ℝ) := by
    exact_mod_cast hdim
  have hnpos : 0 < (minpoly K x).natDegree :=
    minpoly.natDegree_pos hxint
  have hdpos : 0 < Module.finrank K L := Module.finrank_pos
  have hexp :
      (Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L : ℝ) *
          (Module.finrank K L : ℝ)⁻¹ =
        ((minpoly K x).natDegree : ℝ)⁻¹ := by
    have hn0 : ((minpoly K x).natDegree : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr hnpos)
    have hd0 : (Module.finrank K L : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr hdpos)
    field_simp [hn0, hd0]
    nlinarith [hdim_real]
  rw [hspec, spectralAlgNorm_def,
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, hnorm,
    one_div]
  rw [← Real.rpow_natCast, ← hexp]
  exact
    (Real.rpow_mul
      (norm_nonneg ((minpoly K x).coeff 0))
      ((Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L : ℝ))
      ((Module.finrank K L : ℝ)⁻¹))

/-- Complete fields give the unique valuation extension in the exact henselian sense. -/
theorem chapter10_henselian_unique_extension
    {K L Γ₀ Γ₁ Γ₂ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂] [Algebra.IsAlgebraic K L]
    (v : Valuation K Γ₀) [HenselianLocalRing v.valuationSubring]
    (w₁ : Valuation L Γ₁) (w₂ : Valuation L Γ₂)
    (h₁ : v.IsEquiv (w₁.comap (algebraMap K L)))
    (h₂ : v.IsEquiv (w₂.comap (algebraMap K L))) :
    w₁.IsEquiv w₂ := by
  exact chapter10_henselian_valuation_has_unique_branch v w₁ w₂ h₁ h₂

/-- Every algebraic element lies in a finite intermediate extension. -/
theorem chapter10_algebraic_element_in_finite_subextension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x : L} (hx : IsAlgebraic K x) :
    ∃ E : IntermediateField K L, x ∈ E ∧ FiniteDimensional K E := by
  let E : IntermediateField K L := IntermediateField.adjoin K ({x} : Set L)
  refine ⟨E, ?_, ?_⟩
  · exact IntermediateField.subset_adjoin K ({x} : Set L) (Set.mem_singleton x)
  · exact IntermediateField.adjoin.finiteDimensional hx.isIntegral

/-- Compatible finite-extension norms glue over an infinite algebraic extension. -/
theorem chapter10_compatible_finite_values_glue
    {K L : Type*} [NormedField K] [CompleteSpace K]
    [Field L] [Algebra K L]
    (Nfin : ∀ E : IntermediateField K L, E → ℝ)
    (hfinite : ∀ x : L, ∃ E : IntermediateField K L,
      x ∈ E ∧ FiniteDimensional K E)
    (hcompat : ∀ (E F : IntermediateField K L) (hEF : E ≤ F) (x : E),
      Nfin E x = Nfin F ⟨x.1, hEF x.2⟩) :
    ∃ N : L → ℝ, ∀ (E : IntermediateField K L) (x : E),
      N (x : L) = Nfin E x := by
  let Eof : L → IntermediateField K L := fun x => Classical.choose (hfinite x)
  have hmem : ∀ x : L, x ∈ Eof x := fun x => (Classical.choose_spec (hfinite x)).1
  let N : L → ℝ := fun x => Nfin (Eof x) ⟨x, hmem x⟩
  refine ⟨N, ?_⟩
  intro E x
  let F := Eof (x : L)
  let G := E ⊔ F
  have hEG := hcompat E G le_sup_left x
  have hFG := hcompat F G le_sup_right ⟨x, hmem (x : L)⟩
  dsimp [N, F, G]
  rw [hFG]
  simpa using hEG.symm

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

/-- The numerical part of an unramified profile. -/
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
    (ht : vK t = 1) (hu : vL u = 1)
    (hscale : Chapter10ValueScaling vK vL n) :
    ∃ d : Chapter10HeterogeneousExtensionData vK vL hext,
      ∃ p : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d p ∧
          p.degree = n ∧ p.ramificationIndex = n ∧ p.residueDegree = 1 ∧
          Chapter10TotallyRamified p := by
  sorry

/-- Constant-field extensions have e = 1 and residue degree equal to the field degree. -/
theorem chapter10_constant_field_extension_profile
    {k k' : Type*} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    (n : ℕ) (hn : n = Module.finrank k k') :
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
            (P.map res).Separable := by
  sorry

/-- The p-adic uniformizer has normalized valuation one. -/
theorem chapter10_padic_uniformizer_value
    {p : ℕ} [Fact p.Prime] :
    Padic.valuation (p : ℚ_[p]) = 1 := by
  exact Padic.valuation_p

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
  exact chapter10_eisenstein_totally_ramified_profile
    (A := ℤ_[p]) (K := ℚ_[p]) (L := L) P (p : ℤ_[p]) α
    hE hroot hgen hdegree (Padic.addValuation (p := p)) vL hvK hvL hext hπ hscale

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
