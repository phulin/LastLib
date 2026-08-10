import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section01TheExtensionProblem

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

/-! # Book 1, Chapter 10, Section 10.2: Existence by Maximal Domination
-/

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

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
