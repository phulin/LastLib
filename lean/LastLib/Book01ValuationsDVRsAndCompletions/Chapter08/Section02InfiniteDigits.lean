import LastLib.Book01ValuationsDVRsAndCompletions.Chapter08.Section01CompatibleFiniteApproximations

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter08

open Polynomial IsLocalRing
open Filter
open scoped BigOperators LaurentSeries Topology PowerSeries.WithPiTopology

noncomputable section

/-!
# Chapter 8: Inverse limits and digit expansions

This file is deliberately a statement-generation pass. The declarations use Mathlib's
AdicCompletion, ideal quotients, PadicInt, Padic, PowerSeries, and LaurentSeries
where those interfaces match the book. A few predicates package the adic convergence and
digit notation used in the prose.
-/

/-! # Book 1, Chapter 8, Section 8.2: Infinite Digits
-/

/-! ### 8.2 Infinite digits -/

/-- A set of representatives for the residue classes modulo an ideal. -/
def Chapter08IsResidueRepresentativeSet
    (A : Type*) [CommRing A] (I : Ideal A) (S : Set A) : Prop :=
  ∀ a : A, ∃! s : A, s ∈ S ∧ a - s ∈ I

/-- Adic convergence written only in terms of eventual stabilization in every quotient. -/
def Chapter08AdicConverges
    {A : Type*} [CommRing A] (I : Ideal A)
    (u : ℕ → AdicCompletion I A) (x : AdicCompletion I A) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
    AdicCompletion.evalₐ I n (u m) = AdicCompletion.evalₐ I n x

/-- The adic meaning of a sequence of terms tending to zero. -/
def Chapter08AdicTendsToZero
    {A : Type*} [CommRing A] (I : Ideal A) (a : ℕ → A) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i → a i ∈ I ^ n

/-- The n-th partial sum of a digit series in the adic completion. -/
def Chapter08DigitPartialSum
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (d : ℕ → A) (n : ℕ) :
    AdicCompletion I A :=
  ∑ i ∈ Finset.range n,
    algebraMap A (AdicCompletion I A) (d i) *
      (algebraMap A (AdicCompletion I A) π) ^ i

/-- The finite-residue and convergence conditions for an infinite digit expansion. -/
def Chapter08DigitExpansion
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (S : Set A)
    (x : AdicCompletion I A) (d : ℕ → A) : Prop :=
  (∀ i : ℕ, d i ∈ S) ∧
    (∀ n : ℕ,
      AdicCompletion.evalₐ I n x =
        Ideal.Quotient.mk (I ^ n)
          (∑ i ∈ Finset.range n, d i * π ^ i)) ∧
    Chapter08AdicConverges I (Chapter08DigitPartialSum I π d) x

/-- The first n digits matching a residue class modulo pi^n. -/
def Chapter08MatchesTruncation
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (S : Set A)
    (x : AdicCompletion I A) (n : ℕ) (pref : Fin n → A) : Prop :=
  (∀ i : Fin n, pref i ∈ S) ∧
    AdicCompletion.evalₐ I n x =
      Ideal.Quotient.mk (I ^ n)
        (∑ i : Fin n, pref i * π ^ (i : ℕ))

/-! The truncated digit lemma and compatibility of the chosen prefixes. -/
theorem chapter08_truncated_digit_lemma
    {A : Type*} [CommRing A] [IsDomain A] (I : Ideal A) (π : A) (S : Set A)
    (hI : I = Ideal.span {π})
    (hS : Chapter08IsResidueRepresentativeSet A I S)
    (hπ : π ≠ 0)
    (x : AdicCompletion I A) (n : ℕ) :
    ∃! pref : Fin n → A, Chapter08MatchesTruncation I π S x n pref := by
  classical
  have hπmem : π ∈ I := by
    rw [hI]
    exact Ideal.subset_span (by simp)
  have hsum_succ : ∀ (r : ℕ) (w : Fin (r + 1) → A),
      (∑ i : Fin (r + 1), w i * π ^ (i : ℕ)) =
        w 0 + π * ∑ i : Fin r, w i.succ * π ^ (i : ℕ) := by
    intro r w
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one]
    congr 1
    calc
      (∑ i : Fin r, w i.succ * π ^ (i.succ : ℕ)) =
          ∑ i : Fin r, π * (w i.succ * π ^ (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Fin.val_succ, pow_succ]
        ring
      _ = π * ∑ i : Fin r, w i.succ * π ^ (i : ℕ) := by
        rw [Finset.mul_sum]
  have hcancel : ∀ {r : ℕ} {z : A},
      π * z ∈ I ^ (r + 1) → z ∈ I ^ r := by
    intro r z hz
    have hz' : π * z ∈ (Ideal.span {π}) ^ (r + 1) := by
      simpa [hI] using hz
    rw [Ideal.span_singleton_pow] at hz'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hz'
    rw [hI, Ideal.span_singleton_pow]
    apply Ideal.mem_span_singleton'.2
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ hπ
    calc
      π * (c * π ^ r) = c * π ^ (r + 1) := by
        rw [pow_succ]
        ring
      _ = π * z := hc
  have hrepresent : ∀ (r : ℕ) (a : A),
      ∃ w : Fin r → A,
        (∀ i, w i ∈ S) ∧
          Ideal.Quotient.mk (I ^ r)
              (∑ i : Fin r, w i * π ^ (i : ℕ)) =
            Ideal.Quotient.mk (I ^ r) a := by
    intro r
    induction r with
    | zero =>
        intro a
        refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · rw [show I ^ 0 = (⊤ : Ideal A) by simp]
          exact Subsingleton.elim _ _
    | succ r ihr =>
        intro a
        obtain ⟨s, hs, hsu⟩ := hS a
        have hsa : a - s ∈ Ideal.span {π} := by
          simpa [hI] using hs.2
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hsa
        obtain ⟨t, ht, htq⟩ := ihr c
        let w : Fin (r + 1) → A := Fin.cases s (fun i => t i)
        refine ⟨w, ?_, ?_⟩
        · intro i
          refine Fin.cases hs.1 (fun j => ht j) i
        · have htail :
              ∑ i : Fin r, t i * π ^ (i : ℕ) - c ∈ I ^ r :=
            (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 htq
          have hprod :
              π * (∑ i : Fin r, t i * π ^ (i : ℕ) - c) ∈ I ^ (r + 1) := by
            rw [Ideal.IsTwoSided.pow_succ]
            exact Ideal.mul_mem_mul hπmem htail
          apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
          have hsw := hsum_succ r w
          rw [hsw]
          convert hprod using 1
          dsimp [w]
          calc
            s + π * (∑ i : Fin r, t i * π ^ (i : ℕ)) - a =
                π * (∑ i : Fin r, t i * π ^ (i : ℕ)) - (a - s) := by ring
            _ = π * (∑ i : Fin r, t i * π ^ (i : ℕ)) - c * π := by
              rw [← hc]
            _ = π * (∑ i : Fin r, t i * π ^ (i : ℕ) - c) := by ring
  have hunique : ∀ (r : ℕ) {u v : Fin r → A},
      (∀ i, u i ∈ S) → (∀ i, v i ∈ S) →
      Ideal.Quotient.mk (I ^ r) (∑ i : Fin r, u i * π ^ (i : ℕ)) =
        Ideal.Quotient.mk (I ^ r) (∑ i : Fin r, v i * π ^ (i : ℕ)) →
      u = v := by
    intro r
    induction r with
    | zero =>
        intro u v hu hv huv
        funext i
        exact Fin.elim0 i
    | succ r ihr =>
        intro u v hu hv huv
        have htotal :
            (∑ i : Fin (r + 1), u i * π ^ (i : ℕ)) -
                ∑ i : Fin (r + 1), v i * π ^ (i : ℕ) ∈ I ^ (r + 1) :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 huv
        have htotalI :
            (∑ i : Fin (r + 1), u i * π ^ (i : ℕ)) -
                ∑ i : Fin (r + 1), v i * π ^ (i : ℕ) ∈ I := by
          have hpow : I ^ (r + 1) ≤ I := by
            simpa [pow_one] using
              (Ideal.pow_le_pow_right (I := I)
                (show 1 ≤ r + 1 by omega))
          exact hpow htotal
        let U : A := ∑ i : Fin r, u i.succ * π ^ (i : ℕ)
        let V : A := ∑ i : Fin r, v i.succ * π ^ (i : ℕ)
        have htailI : π * (U - V) ∈ I := by
          rw [mul_comm]
          exact I.mul_mem_left _ hπmem
        have hsumI : u 0 - v 0 + π * (U - V) ∈ I := by
          convert htotalI using 1
          rw [hsum_succ r u, hsum_succ r v]
          dsimp [U, V]
          ring
        have hzero : u 0 - v 0 ∈ I := by
          have := I.sub_mem hsumI htailI
          convert this using 1; ring
        have hzero' : v 0 - u 0 ∈ I := by
          simpa [sub_eq_add_neg, add_comm] using I.neg_mem hzero
        have heq0 : u 0 = v 0 := by
          exact (hS (v 0)).unique ⟨hu 0, hzero'⟩
            ⟨hv 0, by simp⟩
        have htail : π * (U - V) ∈ I ^ (r + 1) := by
          convert htotal using 1
          rw [hsum_succ r u, hsum_succ r v, heq0]
          dsimp [U, V]
          ring
        have htail' : U - V ∈ I ^ r := hcancel htail
        have htailq :
            Ideal.Quotient.mk (I ^ r) U = Ideal.Quotient.mk (I ^ r) V :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 htail'
        have htail_eq :
            (fun i : Fin r => u i.succ) = (fun i : Fin r => v i.succ) := by
          apply ihr
          · intro i
            exact hu i.succ
          · intro i
            exact hv i.succ
          · simpa [U, V] using htailq
        funext i
        refine Fin.cases heq0 (fun j => ?_) i
        exact congr_fun htail_eq j
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  obtain ⟨w, hwS, hwq⟩ := hrepresent n a
  have hwx : Chapter08MatchesTruncation I π S x n w := by
    refine ⟨hwS, ?_⟩
    calc
      AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a := ha.symm
      _ = Ideal.Quotient.mk (I ^ n)
          (∑ i : Fin n, w i * π ^ (i : ℕ)) := hwq.symm
  refine ⟨w, hwx, ?_⟩
  intro v hv
  have hq : Ideal.Quotient.mk (I ^ n)
        (∑ i : Fin n, w i * π ^ (i : ℕ)) =
      Ideal.Quotient.mk (I ^ n) (∑ i : Fin n, v i * π ^ (i : ℕ)) := by
    calc
      Ideal.Quotient.mk (I ^ n)
          (∑ i : Fin n, w i * π ^ (i : ℕ)) =
          AdicCompletion.evalₐ I n x := hwx.2.symm
      _ = Ideal.Quotient.mk (I ^ n) (∑ i : Fin n, v i * π ^ (i : ℕ)) := hv.2
  exact (hunique n hwS hv.1 hq).symm

theorem chapter08_truncated_digits_are_compatible
    {A : Type*} [CommRing A] [IsDomain A] (I : Ideal A) (π : A) (S : Set A)
    (hI : I = Ideal.span {π})
    (hS : Chapter08IsResidueRepresentativeSet A I S)
    (hπ : π ≠ 0)
    {x : AdicCompletion I A} {m n : ℕ} (hmn : m ≤ n)
    {u : Fin m → A} {v : Fin n → A}
    (hu : Chapter08MatchesTruncation I π S x m u)
    (hv : Chapter08MatchesTruncation I π S x n v) :
    ∀ i : Fin m, u i = v ⟨i, lt_of_lt_of_le i.isLt hmn⟩ := by
  classical
  have hfactor : ∀ {r s : ℕ} (hrs : r ≤ s),
      Ideal.Quotient.factorPow I hrs (AdicCompletion.evalₐ I s x) =
        AdicCompletion.evalₐ I r x := by
    intro r s hrs
    let hr : (I ^ r • (⊤ : Ideal A)) = I ^ r := by ext; simp
    let hs : (I ^ s • (⊤ : Ideal A)) = I ^ s := by ext; simp
    change Ideal.Quotient.factorPow I hrs
        ((Ideal.quotientEquivAlgOfEq A hs) (x.val s)) =
      (Ideal.quotientEquivAlgOfEq A hr) (x.val r)
    rw [← x.property hrs]
    induction x.val s using Quotient.inductionOn' with
    | _ a =>
        change Ideal.Quotient.factorPow I hrs
            (Ideal.Quotient.mk (I ^ s) a) = Ideal.Quotient.mk (I ^ r) a
        rfl
  have htail : ∀ {r s : ℕ} (hrs : r ≤ s) (w : Fin s → A),
      (∑ i : Fin s, w i * π ^ (i : ℕ)) -
          ∑ i : Fin r, w ⟨i, lt_of_lt_of_le i.isLt hrs⟩ * π ^ (i : ℕ) ∈ I ^ r := by
    intro r s hrs w
    let f : ℕ → A := fun i =>
      if hi : i < s then w ⟨i, hi⟩ * π ^ i else 0
    have hsum_s : (∑ i : Fin s, w i * π ^ (i : ℕ)) =
        ∑ i ∈ Finset.range s, f i := by
      calc
        (∑ i : Fin s, w i * π ^ (i : ℕ)) =
            ∑ i : Fin s, f (i : ℕ) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [f, i.isLt]
        _ = ∑ i ∈ Finset.range s, f i := by
          rw [Fin.sum_univ_eq_sum_range f]
    have hsum_r :
        (∑ i : Fin r, w ⟨i, lt_of_lt_of_le i.isLt hrs⟩ * π ^ (i : ℕ)) =
          ∑ i ∈ Finset.range r, f i := by
      calc
        (∑ i : Fin r, w ⟨i, lt_of_lt_of_le i.isLt hrs⟩ * π ^ (i : ℕ)) =
            ∑ i : Fin r, f (i : ℕ) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [f, lt_of_lt_of_le i.isLt hrs]
        _ = ∑ i ∈ Finset.range r, f i := by
          rw [Fin.sum_univ_eq_sum_range f]
    rw [hsum_s, hsum_r, Finset.sum_range_sub_sum_range hrs]
    apply (I ^ r).sum_mem
    intro i hi
    rw [Finset.mem_filter] at hi
    have hi_lt : i < s := Finset.mem_range.1 hi.1
    have hir : r ≤ i := hi.2
    dsimp [f]
    rw [dif_pos hi_lt]
    rw [hI, Ideal.span_singleton_pow]
    apply Ideal.mem_span_singleton'.2
    refine ⟨w ⟨i, hi_lt⟩ * π ^ (i - r), ?_⟩
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hir]
  let v' : Fin m → A := fun i => v ⟨i, lt_of_lt_of_le i.isLt hmn⟩
  have hv' : Chapter08MatchesTruncation I π S x m v' := by
    refine ⟨?_, ?_⟩
    · intro i
      exact hv.1 ⟨i, lt_of_lt_of_le i.isLt hmn⟩
    · calc
        AdicCompletion.evalₐ I m x =
            Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) :=
          (hfactor hmn).symm
        _ = Ideal.Quotient.factorPow I hmn
            (Ideal.Quotient.mk (I ^ n)
              (∑ i : Fin n, v i * π ^ (i : ℕ))) := by rw [hv.2]
        _ = Ideal.Quotient.mk (I ^ m)
            (∑ i : Fin m, v' i * π ^ (i : ℕ)) := by
          calc
            Ideal.Quotient.factorPow I hmn
                (Ideal.Quotient.mk (I ^ n)
                  (∑ i : Fin n, v i * π ^ (i : ℕ))) =
                Ideal.Quotient.mk (I ^ m)
                  (∑ i : Fin n, v i * π ^ (i : ℕ)) := by rfl
            _ = Ideal.Quotient.mk (I ^ m)
                (∑ i : Fin m, v' i * π ^ (i : ℕ)) :=
              (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (htail hmn v)
  have heq : u = v' :=
    (chapter08_truncated_digit_lemma I π S hI hS hπ x m).unique hu hv'
  intro i
  exact congr_fun heq i

-- The partial sums differ from the represented element by an element of I^n. -/
theorem chapter08_digit_partial_sum_error
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (S : Set A)
    {x : AdicCompletion I A} {d : ℕ → A}
    (hd : Chapter08DigitExpansion I π S x d) (n : ℕ) :
    AdicCompletion.evalₐ I n
        (x - Chapter08DigitPartialSum I π d n) = 0 := by
  rw [map_sub, hd.2.1 n]
  simp [Chapter08DigitPartialSum]

theorem chapter08_digit_terms_tend_to_zero
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (d : ℕ → A)
    (hI : I = Ideal.span {π}) :
    Chapter08AdicTendsToZero I (fun i => d i * π ^ i) := by
  intro n
  refine ⟨n, fun i hi => ?_⟩
  rw [hI, Ideal.span_singleton_pow]
  apply Ideal.mem_span_singleton'.2
  refine ⟨d i * π ^ (i - n), ?_⟩
  change d i * π ^ (i - n) * π ^ n = d i * π ^ i
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi]

-- Conversely, every digit series converges in the complete adic model. -/
theorem chapter08_every_digit_series_converges
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (d : ℕ → A)
    (hI : I = Ideal.span {π}) :
    ∃ x : AdicCompletion I A,
      Chapter08AdicConverges I (Chapter08DigitPartialSum I π d) x := by
  classical
  let s : ℕ → A := fun n => ∑ i ∈ Finset.range n, d i * π ^ i
  have hs : ∀ n : ℕ,
      s n ≡ s (n + 1) [SMOD (I ^ n • (⊤ : Submodule A A))] := by
    intro n
    rw [SModEq.sub_mem]
    dsimp [s]
    rw [Finset.sum_range_succ]
    have hterm : d n * π ^ n ∈ I ^ n := by
      rw [hI, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton'.2 ⟨d n, rfl⟩
    simpa [sub_eq_add_neg] using ((I ^ n).neg_mem hterm)
  let c : AdicCompletion.AdicCauchySequence I A :=
    AdicCompletion.AdicCauchySequence.mk I A s hs
  let x : AdicCompletion I A := AdicCompletion.mk I A c
  refine ⟨x, ?_⟩
  intro n
  refine ⟨n, fun m hnm => ?_⟩
  have hc :
      Ideal.Quotient.mk (I ^ n) (s m) = Ideal.Quotient.mk (I ^ n) (s n) := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    simpa [c, s, sub_eq_add_neg, add_comm, Ideal.smul_eq_mul, Ideal.mul_top] using
      (SModEq.sub_mem.1 (c.property hnm).neg)
  calc
    AdicCompletion.evalₐ I n (Chapter08DigitPartialSum I π d m) =
        Ideal.Quotient.mk (I ^ n) (s m) := by
          simp [Chapter08DigitPartialSum, s]
    _ = Ideal.Quotient.mk (I ^ n) (s n) := hc
    _ = AdicCompletion.evalₐ I n x := by
      simp [x, c, s]

/-- Digit sequences with values in the chosen representative set. -/
abbrev Chapter08DigitSequences (A : Type*) (S : Set A) : Type _ :=
  {d : ℕ → A // ∀ n : ℕ, d n ∈ S}

/-! The digit expansion is a bijection of sets, not in general a coefficientwise ring map. -/
theorem chapter08_digit_expansion_set_bijection
    {A : Type*} [CommRing A] [IsDomain A] (I : Ideal A) (π : A) (S : Set A)
    (hI : I = Ideal.span {π})
    (hS : Chapter08IsResidueRepresentativeSet A I S) (hπ : π ≠ 0) :
    ∃ e : AdicCompletion I A ≃ Chapter08DigitSequences A S,
      ∀ x, Chapter08DigitExpansion I π S x (e x).1 ∧
        ∀ d : ℕ → A,
          Chapter08DigitExpansion I π S x d → d = (e x).1 := by
  classical
  have htail : ∀ {r s : ℕ} (hrs : r ≤ s) (w : ℕ → A),
      (∑ i ∈ Finset.range s, w i * π ^ i) -
          ∑ i ∈ Finset.range r, w i * π ^ i ∈ I ^ r := by
    intro r s hrs w
    rw [Finset.sum_range_sub_sum_range hrs]
    apply (I ^ r).sum_mem
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [hI, Ideal.span_singleton_pow]
    apply Ideal.mem_span_singleton'.2
    refine ⟨w i * π ^ (i - r), ?_⟩
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi.2]
  let pref : AdicCompletion I A → ∀ n : ℕ, Fin n → A := fun x n =>
    (chapter08_truncated_digit_lemma I π S hI hS hπ x n).choose
  have hpref : ∀ (x : AdicCompletion I A) (n : ℕ),
      Chapter08MatchesTruncation I π S x n (pref x n) := by
    intro x n
    exact (chapter08_truncated_digit_lemma I π S hI hS hπ x n).choose_spec.1
  let digits : AdicCompletion I A → ℕ → A := fun x i =>
    pref x (i + 1) ⟨i, Nat.lt_succ_self i⟩
  have hdigit_mem : ∀ (x : AdicCompletion I A) (i : ℕ), digits x i ∈ S := by
    intro x i
    exact (hpref x (i + 1)).1 ⟨i, Nat.lt_succ_self i⟩
  have hpref_eq : ∀ (x : AdicCompletion I A) (n : ℕ) (i : Fin n),
      pref x n i = digits x i := by
    intro x n i
    have hcompat := chapter08_truncated_digits_are_compatible
      I π S hI hS hπ (Nat.succ_le_iff.2 i.isLt)
      (hpref x (i + 1)) (hpref x n)
    simpa [digits] using (hcompat ⟨i, Nat.lt_succ_self i⟩).symm
  have hEval : ∀ (x : AdicCompletion I A) (n : ℕ),
      AdicCompletion.evalₐ I n x =
        Ideal.Quotient.mk (I ^ n)
          (∑ i ∈ Finset.range n, digits x i * π ^ i) := by
    intro x n
    have hsum :
        (∑ i : Fin n, pref x n i * π ^ (i : ℕ)) =
          ∑ i ∈ Finset.range n, digits x i * π ^ i := by
      let q : ℕ → A := fun i =>
        if hi : i < n then pref x n ⟨i, hi⟩ * π ^ i else 0
      calc
        (∑ i : Fin n, pref x n i * π ^ (i : ℕ)) =
            ∑ i : Fin n, q (i : ℕ) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [q, i.isLt]
        _ = ∑ i ∈ Finset.range n, q i := by
              rw [Fin.sum_univ_eq_sum_range q]
        _ = ∑ i ∈ Finset.range n, digits x i * π ^ i := by
              apply Finset.sum_congr rfl
              intro i hi
              have he := hpref_eq x n ⟨i, Finset.mem_range.1 hi⟩
              simp [q, Finset.mem_range.1 hi, digits, he]
    rw [(hpref x n).2, hsum]
  have hconv_of_expansion : ∀ (x : AdicCompletion I A),
      Chapter08AdicConverges I (Chapter08DigitPartialSum I π (digits x)) x := by
    intro x n
    refine ⟨n, fun m hnm => ?_⟩
    calc
      AdicCompletion.evalₐ I n
          (Chapter08DigitPartialSum I π (digits x) m) =
          Ideal.Quotient.mk (I ^ n)
            (∑ i ∈ Finset.range m, digits x i * π ^ i) := by
              simp [Chapter08DigitPartialSum]
      _ = Ideal.Quotient.mk (I ^ n)
            (∑ i ∈ Finset.range n, digits x i * π ^ i) :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (htail hnm (digits x))
      _ = AdicCompletion.evalₐ I n x := (hEval x n).symm
  let toDigits : AdicCompletion I A → Chapter08DigitSequences A S := fun x =>
    ⟨digits x, hdigit_mem x⟩
  have hfinite_of_converges : ∀ (d : Chapter08DigitSequences A S)
      (x : AdicCompletion I A),
      Chapter08AdicConverges I (Chapter08DigitPartialSum I π d.1) x →
      ∀ n : ℕ,
        AdicCompletion.evalₐ I n x =
          Ideal.Quotient.mk (I ^ n)
            (∑ i ∈ Finset.range n, d.1 i * π ^ i) := by
    intro d x hconv n
    obtain ⟨N, hN⟩ := hconv n
    let m := max N n
    have hmN : N ≤ m := le_max_left _ _
    have hmn : n ≤ m := le_max_right _ _
    calc
      AdicCompletion.evalₐ I n x =
          AdicCompletion.evalₐ I n (Chapter08DigitPartialSum I π d.1 m) :=
        (hN m hmN).symm
      _ = Ideal.Quotient.mk (I ^ n)
          (∑ i ∈ Finset.range m, d.1 i * π ^ i) := by
            simp [Chapter08DigitPartialSum]
      _ = Ideal.Quotient.mk (I ^ n)
          (∑ i ∈ Finset.range n, d.1 i * π ^ i) :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (htail hmn d.1)
  let fromDigits : Chapter08DigitSequences A S → AdicCompletion I A := fun d =>
    Classical.choose (chapter08_every_digit_series_converges I π d.1 hI)
  have hfrom_conv : ∀ d : Chapter08DigitSequences A S,
      Chapter08AdicConverges I (Chapter08DigitPartialSum I π d.1) (fromDigits d) := by
    intro d
    exact Classical.choose_spec (chapter08_every_digit_series_converges I π d.1 hI)
  have hfrom_expansion : ∀ d : Chapter08DigitSequences A S,
      Chapter08DigitExpansion I π S (fromDigits d) d.1 := by
    intro d
    refine ⟨d.2, hfinite_of_converges d (fromDigits d) (hfrom_conv d), hfrom_conv d⟩
  have hdigit_expansion : ∀ x : AdicCompletion I A,
      Chapter08DigitExpansion I π S x (digits x) := by
    intro x
    exact ⟨hdigit_mem x, hEval x, hconv_of_expansion x⟩
  have hexp_unique : ∀ {x : AdicCompletion I A} {d e : ℕ → A},
      Chapter08DigitExpansion I π S x d →
        Chapter08DigitExpansion I π S x e → d = e := by
    intro x d e hd he
    funext i
    let n := i + 1
    let u : Fin n → A := fun j => d j
    let v : Fin n → A := fun j => e j
    have hu : Chapter08MatchesTruncation I π S x n u := by
      refine ⟨fun j => hd.1 j, ?_⟩
      calc
        AdicCompletion.evalₐ I n x =
            Ideal.Quotient.mk (I ^ n)
              (∑ j ∈ Finset.range n, d j * π ^ j) := hd.2.1 n
        _ = Ideal.Quotient.mk (I ^ n)
            (∑ j : Fin n, u j * π ^ (j : ℕ)) := by
          change Ideal.Quotient.mk (I ^ n)
              (∑ j ∈ Finset.range n, d j * π ^ j) =
            Ideal.Quotient.mk (I ^ n)
              (∑ j : Fin n, d j * π ^ (j : ℕ))
          rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => d j * π ^ j)]
    have hv : Chapter08MatchesTruncation I π S x n v := by
      refine ⟨fun j => he.1 j, ?_⟩
      calc
        AdicCompletion.evalₐ I n x =
            Ideal.Quotient.mk (I ^ n)
              (∑ j ∈ Finset.range n, e j * π ^ j) := he.2.1 n
        _ = Ideal.Quotient.mk (I ^ n)
            (∑ j : Fin n, v j * π ^ (j : ℕ)) := by
          change Ideal.Quotient.mk (I ^ n)
              (∑ j ∈ Finset.range n, e j * π ^ j) =
            Ideal.Quotient.mk (I ^ n)
              (∑ j : Fin n, e j * π ^ (j : ℕ))
          rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => e j * π ^ j)]
    have huv := (chapter08_truncated_digit_lemma I π S hI hS hπ x n).unique hu hv
    exact congr_fun huv ⟨i, Nat.lt_succ_self i⟩
  let e : AdicCompletion I A ≃ Chapter08DigitSequences A S :=
    { toFun := toDigits
      invFun := fromDigits
      left_inv := by
        intro x
        apply AdicCompletion.ext_evalₐ
        intro n
        calc
          AdicCompletion.evalₐ I n (fromDigits (toDigits x)) =
              Ideal.Quotient.mk (I ^ n)
                (∑ i ∈ Finset.range n, digits x i * π ^ i) :=
            (hfrom_expansion (toDigits x)).2.1 n
          _ = AdicCompletion.evalₐ I n x := (hEval x n).symm
      right_inv := by
        intro d
        apply Subtype.ext
        funext i
        have h := hexp_unique (x := fromDigits d) (d := d.1)
          (e := (digits (fromDigits d)))
          (hfrom_expansion d) (hdigit_expansion (fromDigits d))
        change digits (fromDigits d) i = d.1 i
        exact (congr_fun h i).symm }
  refine ⟨e, ?_⟩
  intro x
  refine ⟨hdigit_expansion x, ?_⟩
  intro d hd
  exact hexp_unique hd (hdigit_expansion x)

/-- The raw coefficientwise addition suggested by a digit sequence. -/
def Chapter08CoefficientwiseAdd {A : Type*} [Add A]
    (d e : ℕ → A) : ℕ → A := fun n => d n + e n

/-- The raw coefficientwise multiplication suggested by a digit sequence. -/
def Chapter08CoefficientwiseMul {A : Type*} [Mul A]
    (d e : ℕ → A) : ℕ → A := fun n => d n * e n

/-- A predicate saying that a digit coding respects addition coefficient by coefficient. -/
def Chapter08CoefficientwiseAdditiveCoding
    {A : Type*} [CommRing A] (I : Ideal A) (S : Set A)
    (e : AdicCompletion I A ≃ Chapter08DigitSequences A S) : Prop :=
  ∀ x y : AdicCompletion I A, ∀ n : ℕ,
    (e (x + y)).1 n = Chapter08CoefficientwiseAdd (e x).1 (e y).1 n

private theorem chapter08_mixed_characteristic_no_additive_residue_section
    {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [CharZero A]
    (I : Ideal A) (p : ℕ) [Fact p.Prime]
    (hI : I = Ideal.span {(p : A)})
    (hImax : I = IsLocalRing.maximalIdeal A) :
    ¬ ∃ f : (A ⧸ I) →+ A, Function.Injective f := by
  classical
  rintro ⟨f, hf⟩
  have hp : (p : A) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  have hzero : ∀ q : A ⧸ I, f q = 0 := by
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hq : p • (Ideal.Quotient.mk I a) = 0 := by
      rw [← map_nsmul]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [hI]
      have hpI : (p : A) ∈ Ideal.span {(p : A)} :=
        Ideal.mem_span_singleton_self (p : A)
      simpa [nsmul_eq_mul, mul_comm] using
        (Ideal.span {(p : A)}).mul_mem_left a hpI
    have hpq' : p • f (Ideal.Quotient.mk I a) = 0 := by
      calc
        p • f (Ideal.Quotient.mk I a) =
            f (p • Ideal.Quotient.mk I a) := (map_nsmul f p _).symm
        _ = 0 := by rw [hq, map_zero]
    have hpq : (p : A) * f (Ideal.Quotient.mk I a) = 0 := by
      simpa [nsmul_eq_mul] using hpq'
    exact (mul_eq_zero.mp hpq).resolve_left hp
  have hItop : I ≠ (⊤ : Ideal A) := by
    rw [hImax]
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  exact (Ideal.Quotient.zero_ne_one_iff.mpr hItop) (hf (by simp [hzero]))

/-! In mixed characteristic, the absence of a coefficient-field embedding is the carry
obstruction behind the preceding set-theoretic, rather than coefficientwise-ring, model. -/
private theorem chapter08_mixed_characteristic_additive_section_obstruction
    {A : Type*} [CommRing A] [CharZero A] (I : Ideal A) (S : Set A)
    (p : ℕ) [Fact p.Prime]
    (_hI : I = Ideal.span {(p : A)})
    (hS : Chapter08IsResidueRepresentativeSet A I S)
    (hnoembed : ¬ ∃ f : (A ⧸ I) →+ A, Function.Injective f)
    (e : AdicCompletion I A ≃ Chapter08DigitSequences A S)
    (hdigits : ∀ x, Chapter08DigitExpansion I (p : A) S x (e x).1) :
    ¬ Chapter08CoefficientwiseAdditiveCoding I S e := by
  classical
  intro hadd
  let d0 : A → A := fun a => (e (algebraMap A (AdicCompletion I A) a)).1 0
  have hadd0 : ∀ a b : A, d0 (a + b) = d0 a + d0 b := by
    intro a b
    have h := hadd (algebraMap A (AdicCompletion I A) a)
      (algebraMap A (AdicCompletion I A) b) 0
    simpa [d0, Chapter08CoefficientwiseAdd] using h
  have hzero : d0 0 = 0 := by
    have h := hadd0 0 0
    apply Eq.symm
    apply add_left_cancel (a := d0 0)
    simpa using h
  have hdigit_mem : ∀ a : A, d0 a ∈ S := by
    intro a
    simpa [d0] using (hdigits (algebraMap A (AdicCompletion I A) a)).1 0
  have hmk : ∀ a : A,
      Ideal.Quotient.mk I a = Ideal.Quotient.mk I (d0 a) := by
    intro a
    have h := (hdigits (algebraMap A (AdicCompletion I A) a)).2.1 1
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of] at h
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have h' : Ideal.Quotient.mk (I ^ 1) a =
        Ideal.Quotient.mk (I ^ 1) (d0 a) := by
      simpa [d0, AdicCompletion.algebraMap_apply] using h
    simpa using (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 h'
  have h0S : (0 : A) ∈ S := by
    simpa [hzero] using hdigit_mem 0
  have hzero_of_mem : ∀ {a : A}, a ∈ I → d0 a = 0 := by
    intro a ha
    have hda : d0 a ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← hmk a]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    exact (hS 0).unique ⟨hdigit_mem a, by simpa using I.neg_mem hda⟩
      ⟨h0S, by simp⟩
  let f0 : A →+ A :=
    { toFun := d0
      map_zero' := hzero
      map_add' := hadd0 }
  have hker : f0.ker = I.toAddSubgroup := by
    ext a
    constructor
    · intro ha
      change d0 a = 0 at ha
      have hqa : Ideal.Quotient.mk I a = 0 := by
        rw [hmk a, ha]
        exact map_zero (Ideal.Quotient.mk I)
      exact Ideal.Quotient.eq_zero_iff_mem.mp hqa
    · intro ha
      change d0 a = 0
      exact hzero_of_mem ha
  have hfactor : I.toAddSubgroup ≤ f0.ker := by
    rw [hker]
  let f : (A ⧸ I) →+ A :=
    QuotientAddGroup.lift I.toAddSubgroup f0 hfactor
  have hf_mk : ∀ a : A,
      f (Ideal.Quotient.mk I a) = d0 a := by
    intro a
    rfl
  have hf_inj : Function.Injective f := by
    intro q r hqr
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hab : d0 a = d0 b := by
      simpa [hf_mk] using hqr
    have hab0 : f0 (a - b) = 0 := by
      rw [map_sub]
      change d0 a - d0 b = 0
      rw [hab, sub_self]
    have habI : a - b ∈ I := by
      have : a - b ∈ f0.ker := hab0
      rw [hker] at this
      exact this
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 habI
  exact hnoembed ⟨f, hf_inj⟩

theorem chapter08_mixed_characteristic_digit_carries_obstruct_coefficientwise_addition
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
    (I : Ideal A) (S : Set A)
    (p : ℕ) [Fact p.Prime]
    (hI : I = Ideal.span {(p : A)})
    (hS : Chapter08IsResidueRepresentativeSet A I S)
    (hImax : I = IsLocalRing.maximalIdeal A)
    (e : AdicCompletion I A ≃ Chapter08DigitSequences A S)
    (hdigits : ∀ x, Chapter08DigitExpansion I (p : A) S x (e x).1) :
    ¬ Chapter08CoefficientwiseAdditiveCoding I S e := by
  have hnoembed :=
    chapter08_mixed_characteristic_no_additive_residue_section I p hI hImax
  exact chapter08_mixed_characteristic_additive_section_obstruction
    I S p hI hS hnoembed e hdigits

/-! Equal characteristic: a coefficient field gives literal formal-series coefficients. -/
structure Chapter08CoefficientFieldSection
    (A k : Type*) [CommRing A] [Field k] (I : Ideal A) where
  lift : k →+* A
  residue : A →+* k
  residue_lift : residue.comp lift = RingHom.id k
  kernel_residue : RingHom.ker residue = I

/-- The coefficient sequence represented by a formal power series. -/
def Chapter08CoefficientSequenceEquiv (k : Type*) [Field k] :
    (ℕ → k) ≃ PowerSeries k where
  toFun := PowerSeries.mk
  invFun := fun f n => PowerSeries.coeff n f
  left_inv := by
    intro f
    funext n
    simp
  right_inv := by
    intro f
    apply PowerSeries.ext
    intro n
    simp

/-- The Cauchy product of two coefficient sequences. -/
def Chapter08CauchyProduct {k : Type*} [Semiring k]
    (a b : ℕ → k) (n : ℕ) : k :=
  ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

theorem chapter08_power_series_multiplication_is_cauchy_product
    {k : Type*} [Field k] (a b : ℕ → k) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b) =
      Chapter08CauchyProduct a b n := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Chapter08CauchyProduct]

structure Chapter08FormalSeriesModel
    (A k : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] (I : Ideal A) (π : A)
    (sectionData : Chapter08CoefficientFieldSection A k I) where
  equiv : AdicCompletion I A ≃+* PowerSeries k
  maps_section : ∀ c : k,
    equiv (algebraMap A (AdicCompletion I A) (sectionData.lift c)) = PowerSeries.C c
  maps_uniformizer :
    equiv (algebraMap A (AdicCompletion I A) π) = PowerSeries.X

/-! A complete equal-characteristic DVR with a coefficient field has the formal-series model. -/
theorem chapter08_equal_characteristic_formal_series_model
    {A k : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] (I : Ideal A) (π : A)
    (hI : I = Ideal.span {π})
    (hcomplete : IsAdicComplete I A)
    (sectionData : Chapter08CoefficientFieldSection A k I) :
    Nonempty (Chapter08FormalSeriesModel A k I π sectionData) := by
  classical
  let : WithIdeal A := ⟨I⟩
  let : TopologicalSpace k := ⊥
  let : UniformSpace k := ⊥
  let : DiscreteTopology k := discreteTopology_bot k
  have htop := (IsAdic.isAdicComplete_iff (I := I) (by rfl)).mp hcomplete
  let : CompleteSpace A := htop.1
  let : T2Space A := htop.2
  have hres_surj : Function.Surjective sectionData.residue := by
    intro c
    refine ⟨sectionData.lift c, ?_⟩
    simpa using congrArg (fun g => g c) sectionData.residue_lift
  have hImax : I.IsMaximal := by
    rw [← sectionData.kernel_residue]
    exact RingHom.ker_isMaximal_of_surjective sectionData.residue hres_surj
  have hInonbot : I ≠ (⊥ : Ideal A) :=
    Ring.ne_bot_of_isMaximal_of_not_isField hImax
      (IsDiscreteValuationRing.not_isField A)
  have hπ : π ≠ 0 := by
    intro hπ0
    apply hInonbot
    calc
      I = Ideal.span {π} := hI
      _ = (⊥ : Ideal A) := Ideal.span_singleton_eq_bot.mpr hπ0
  have hπmem : π ∈ I := by
    rw [hI]
    exact Ideal.mem_span_singleton_self π
  have hπeval : PowerSeries.HasEval π := by
    exact WithIdeal.isTopologicallyNilpotent_of_mem hπmem
  have hlift_cont : Continuous sectionData.lift := continuous_of_discreteTopology
  let f : PowerSeries k →+* A :=
    PowerSeries.eval₂Hom hlift_cont hπeval
  have hfC (c : k) : f (PowerSeries.C c) = sectionData.lift c := by
    dsimp [f]
    rw [PowerSeries.coe_eval₂Hom]
    simp
  have hfX : f PowerSeries.X = π := by
    dsimp [f]
    rw [PowerSeries.coe_eval₂Hom]
    simp
  have hmap :
      (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))).map f = I := by
    rw [Ideal.map_span]
    simp [hfX, hI]
  have hres : Function.Surjective
      ((Ideal.Quotient.mk ((Ideal.span ({PowerSeries.X} : Set (PowerSeries k))).map f)).comp f) := by
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨PowerSeries.C (sectionData.residue a), ?_⟩
    rw [RingHom.comp_apply, hfC, hmap]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have hmem : sectionData.lift (sectionData.residue a) - a ∈
        RingHom.ker sectionData.residue := by
      apply RingHom.mem_ker.mpr
      have hleft : sectionData.residue (sectionData.lift (sectionData.residue a)) =
          sectionData.residue a := by
        simpa [RingHom.comp_apply] using
          congrArg (fun g => g (sectionData.residue a)) sectionData.residue_lift
      rw [map_sub, hleft, sub_self]
    simpa only [sectionData.kernel_residue] using hmem
  let : IsHausdorff
      ((Ideal.span ({PowerSeries.X} : Set (PowerSeries k))).map f) A := by
    rw [hmap]
    exact hcomplete.toIsHausdorff
  let : IsAdicComplete
      (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) (PowerSeries k) := inferInstance
  have hf_surj : Function.Surjective f := by
    exact surjective_of_mk_map_comp_surjective f hres
  have hf_inj : Function.Injective f := by
    intro p q hpq
    by_contra hne
    let r : PowerSeries k := p - q
    have hr : r ≠ 0 := by
      intro hr0
      apply hne
      exact sub_eq_zero.mp hr0
    have hunit : IsUnit (PowerSeries.divXPowOrder r) :=
      PowerSeries.isUnit_divided_by_X_pow_order hr
    have hunit_map : IsUnit (f (PowerSeries.divXPowOrder r)) := hunit.map f
    have hpow : f (PowerSeries.X ^ r.order.toNat) ≠ 0 := by
      rw [map_pow, hfX]
      exact pow_ne_zero _ hπ
    have hprod : f (PowerSeries.X ^ r.order.toNat * PowerSeries.divXPowOrder r) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero hpow hunit_map.ne_zero
    apply hprod
    rw [PowerSeries.X_pow_order_mul_divXPowOrder]
    dsimp [r]
    rw [map_sub, hpq, sub_self]
  let e₀ : PowerSeries k ≃+* A := RingEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let eA : A ≃+* AdicCompletion I A := (AdicCompletion.ofAlgEquiv I).toRingEquiv
  let e : AdicCompletion I A ≃+* PowerSeries k := eA.symm.trans e₀.symm
  have heA (a : A) :
      eA.symm (algebraMap A (AdicCompletion I A) a) = a := by
    change (AdicCompletion.ofAlgEquiv I).symm (AdicCompletion.of I A a) = a
    exact AdicCompletion.ofAlgEquiv_symm_of I a
  have he₀C (c : k) : e₀ (PowerSeries.C c) = sectionData.lift c := by
    change f (PowerSeries.C c) = sectionData.lift c
    exact hfC c
  have he₀X : e₀ PowerSeries.X = π := by
    change f PowerSeries.X = π
    exact hfX
  refine ⟨{
    equiv := e
    maps_section := ?_
    maps_uniformizer := ?_ }⟩
  · intro c
    apply e₀.injective
    simpa [e, heA] using (he₀C c).symm
  · apply e₀.injective
    simpa [e, heA] using he₀X.symm

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter08
