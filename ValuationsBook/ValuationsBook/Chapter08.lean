import Mathlib

namespace ValuationsBook.Chapter08

open Polynomial IsLocalRing
open Filter
open scoped BigOperators LaurentSeries Topology

noncomputable section

/-!
# Chapter 8: Inverse limits and digit expansions

This file is deliberately a statement-generation pass. The declarations use Mathlib's
AdicCompletion, ideal quotients, PadicInt, Padic, PowerSeries, and LaurentSeries
where those interfaces match the book. A few predicates package the adic convergence and
digit notation used in the prose.
-/

/-! ### 8.1 Compatible finite approximations -/

/-- The finite precision quotient occurring in Chapter 8. -/
abbrev Chapter08Truncation (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) : Type _ :=
  A ⧸ I ^ n

/-- The ring of compatible families of residues, indexed from precision 1 onwards. -/
def Chapter08CompatibleSubring (A : Type*) [CommRing A] (I : Ideal A) :
    Subring (∀ n : ℕ, A ⧸ I ^ (n + 1)) where
  carrier := {x | ∀ n : ℕ,
    Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)) (x (n + 1)) = x n}
  zero_mem' := by
    intro n
    simp
  add_mem' := by
    intro x y hx hy n
    simp [hx n, hy n]
  neg_mem' := by
    intro x hx n
    simp [hx n]
  one_mem' := by
    intro n
    simp
  mul_mem' := by
    intro x y hx hy n
    simp [hx n, hy n]

/-- A compatible family is the inverse-limit model used throughout the chapter. -/
abbrev Chapter08CompatibleFamily (A : Type*) [CommRing A] (I : Ideal A) : Type _ :=
  Chapter08CompatibleSubring A I

@[simp]
theorem Chapter08CompatibleFamily.compatible
    {A : Type*} [CommRing A] {I : Ideal A}
    (x : Chapter08CompatibleFamily A I) (n : ℕ) :
    Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)) (x.1 (n + 1)) = x.1 n := by
  sorry

def Chapter08FiniteQuotientTopology
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) :
    TopologicalSpace (A ⧸ I ^ (n + 1)) := ⊥

/-- A small interface for the phrase topological-ring isomorphism. -/
structure Chapter08TopologicalRingEquiv (R S : Type*)
    [CommRing R] [CommRing S] (tR : TopologicalSpace R) (tS : TopologicalSpace S) where
  ringEquiv : R ≃+* S
  continuous_toFun : @Continuous R S tR tS ringEquiv
  continuous_invFun : @Continuous S R tS tR ringEquiv.symm

def Chapter08InverseLimitProductTopology
    (A : Type*) [CommRing A] (I : Ideal A) :
    TopologicalSpace (∀ n : ℕ, A ⧸ I ^ (n + 1)) :=
  @Pi.topologicalSpace ℕ (fun n : ℕ => A ⧸ I ^ (n + 1))
    (fun n => Chapter08FiniteQuotientTopology A I n)

def Chapter08InverseLimitTopology
    (A : Type*) [CommRing A] (I : Ideal A) :
    TopologicalSpace (Chapter08CompatibleFamily A I) :=
  TopologicalSpace.induced (fun x : Chapter08CompatibleFamily A I => x.1)
    (Chapter08InverseLimitProductTopology A I)

def Chapter08AdicCompletionTopology
    (A : Type*) [CommRing A] (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  (Ideal.map (algebraMap A (AdicCompletion I A)) I).adicTopology

/-- The residue family attached to an element of an adic completion. -/
def Chapter08CompletionResidues
    {A : Type*} [CommRing A] (I : Ideal A) (x : AdicCompletion I A) :
    Chapter08CompatibleFamily A I := by
  refine ⟨fun n => AdicCompletion.evalₐ I (n + 1) x, ?_⟩
  intro n
  sorry

/-! Theorem 8.1: the completion is canonically the inverse limit of its finite quotients. -/
theorem chapter08_theorem_8_1_inverse_limit_description
    {A : Type*} [CommRing A] (I : Ideal A)
    :
    ∃ e : Chapter08TopologicalRingEquiv (AdicCompletion I A)
        (Chapter08CompatibleFamily A I)
        (Chapter08AdicCompletionTopology A I)
        (Chapter08InverseLimitTopology A I),
      ∀ x, e.ringEquiv x = Chapter08CompletionResidues I x := by
  sorry

/-- Coordinatewise operations preserve compatibility, so there is no extra consistency datum. -/
theorem chapter08_inverse_limit_coordinatewise_operations
    {A : Type*} [CommRing A] {I : Ideal A}
    (x y : Chapter08CompatibleFamily A I) (n : ℕ) :
    (x + y).1 n = x.1 n + y.1 n ∧
      (x * y).1 n = x.1 n * y.1 n ∧
      (-x).1 n = -(x.1 n) := by
  sorry

/-- A compatible collection of maps on truncations. -/
structure Chapter08CompatibleTruncationMaps
    (A B : Type*) [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) where
  map : ∀ n : ℕ, A ⧸ I ^ (n + 1) →+* B ⧸ J ^ (n + 1)
  compatible : ∀ n : ℕ,
    (map n).comp (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) =
      (Ideal.Quotient.factorPow J (Nat.le_succ (n + 1))).comp (map (n + 1))

/-- The map on inverse limits induced by compatible maps on all truncations. -/
def Chapter08InducedMapOnCompatibleFamilies
    {A B : Type*} [CommRing A] [CommRing B]
    {I : Ideal A} {J : Ideal B}
    (φ : Chapter08CompatibleTruncationMaps A B I J) :
    Chapter08CompatibleFamily A I →+* Chapter08CompatibleFamily B J := by
  refine
    { toFun := fun x => ⟨fun n => φ.map n (x.1 n), ?_⟩
      map_one' := by sorry
      map_mul' := by sorry
      map_zero' := by sorry
      map_add' := by sorry }
  intro n
  sorry

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
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (S : Set A)
    (hI : I = Ideal.span {π})
    (hS : Chapter08IsResidueRepresentativeSet A I S)
    (x : AdicCompletion I A) (n : ℕ) :
    ∃! pref : Fin n → A, Chapter08MatchesTruncation I π S x n pref := by
  sorry

theorem chapter08_truncated_digits_are_compatible
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (S : Set A)
    {x : AdicCompletion I A} {m n : ℕ} (hmn : m ≤ n)
    {u : Fin m → A} {v : Fin n → A}
    (hu : Chapter08MatchesTruncation I π S x m u)
    (hv : Chapter08MatchesTruncation I π S x n v) :
    ∀ i : Fin m, u i = v ⟨i, lt_of_lt_of_le i.isLt hmn⟩ := by
  sorry

-- The partial sums differ from the represented element by an element of I^n. -/
theorem chapter08_digit_partial_sum_error
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (S : Set A)
    {x : AdicCompletion I A} {d : ℕ → A}
    (hd : Chapter08DigitExpansion I π S x d) (n : ℕ) :
    AdicCompletion.evalₐ I n
        (x - Chapter08DigitPartialSum I π d n) = 0 := by
  sorry

theorem chapter08_digit_terms_tend_to_zero
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (d : ℕ → A)
    (hI : I = Ideal.span {π}) :
    Chapter08AdicTendsToZero I (fun i => d i * π ^ i) := by
  sorry

-- Conversely, every digit series converges in the complete adic model. -/
theorem chapter08_every_digit_series_converges
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (d : ℕ → A)
    (hI : I = Ideal.span {π}) :
    ∃ x : AdicCompletion I A,
      Chapter08AdicConverges I (Chapter08DigitPartialSum I π d) x := by
  sorry

/-- Digit sequences with values in the chosen representative set. -/
abbrev Chapter08DigitSequences (A : Type*) (S : Set A) : Type _ :=
  {d : ℕ → A // ∀ n : ℕ, d n ∈ S}

/-! The digit expansion is a bijection of sets, not in general a coefficientwise ring map. -/
theorem chapter08_digit_expansion_set_bijection
    {A : Type*} [CommRing A] (I : Ideal A) (π : A) (S : Set A)
    (hI : I = Ideal.span {π})
    (hS : Chapter08IsResidueRepresentativeSet A I S) :
    ∃ e : AdicCompletion I A ≃ Chapter08DigitSequences A S,
      ∀ x, Chapter08DigitExpansion I π S x (e x).1 := by
  sorry

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

/-! In mixed characteristic, the absence of a coefficient-field embedding is the carry
obstruction behind the preceding set-theoretic, rather than coefficientwise-ring, model. -/
theorem chapter08_mixed_characteristic_digit_carries_obstruct_coefficientwise_addition
    {A : Type*} [CommRing A] [CharZero A] (I : Ideal A) (S : Set A)
    (p : ℕ) [Fact p.Prime]
    (hI : I = Ideal.span {(p : A)})
    (hS : Chapter08IsResidueRepresentativeSet A I S)
    (hnoembed : ¬ ∃ f : ZMod p →+* A, Function.Injective f)
    (e : AdicCompletion I A ≃ Chapter08DigitSequences A S)
    (hdigits : ∀ x, Chapter08DigitExpansion I (p : A) S x (e x).1) :
    ¬ Chapter08CoefficientwiseAdditiveCoding I S e := by
  sorry

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
  sorry

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
  sorry

/-! ### 8.3 The p-adic integers and numbers -/

/-- Mathlib's p-adic integers and p-adic numbers, named as in the book. -/
abbrev Chapter08PadicIntegers (p : ℕ) [Fact p.Prime] := PadicInt p
abbrev Chapter08PadicNumbers (p : ℕ) [Fact p.Prime] := Padic p

/-- The inverse-limit presentation of Z_p used in this chapter. -/
abbrev Chapter08PadicIntegerInverseLimit (p : ℕ) [Fact p.Prime] :=
  Chapter08CompatibleFamily ℤ (Ideal.span {(p : ℤ)})

abbrev Chapter08Zp (p : ℕ) [Fact p.Prime] := Chapter08PadicIntegerInverseLimit p
abbrev Chapter08Qp (p : ℕ) [Fact p.Prime] := Chapter08PadicNumbers p

-- The inverse-limit ring is canonically the usual Mathlib p-adic integer ring. -/
theorem chapter08_padic_integer_inverse_limit
    (p : ℕ) [Fact p.Prime] :
    Nonempty (Chapter08PadicIntegers p ≃+* Chapter08Zp p) := by
  sorry

-- Z_p is a complete DVR with uniformizer p and residue field F_p. -/
theorem chapter08_padic_integers_are_a_complete_dvr
    (p : ℕ) [Fact p.Prime] :
    IsDiscreteValuationRing (Chapter08PadicIntegers p) ∧
      CompleteSpace (Chapter08PadicIntegers p) ∧
      Irreducible (p : Chapter08PadicIntegers p) ∧
      Nonempty (IsLocalRing.ResidueField (Chapter08PadicIntegers p) ≃+* ZMod p) := by
  sorry

/-- The digit alphabet for p-adic integers. -/
abbrev Chapter08PadicDigitSequences (p : ℕ) :=
  {a : ℕ → ℕ // ∀ i : ℕ, a i < p}

/-- The finite partial sum of a p-adic digit sequence. -/
def Chapter08PadicPartialSum (p : ℕ) [Fact p.Prime]
    (a : ℕ → ℕ) (n : ℕ) : Chapter08PadicIntegers p :=
  ∑ i ∈ Finset.range n,
    (a i : Chapter08PadicIntegers p) * (p : Chapter08PadicIntegers p) ^ i

/-- A convergent p-adic digit expansion with digits 0 ≤ a_i < p. -/
def Chapter08PadicExpansion (p : ℕ) [Fact p.Prime]
    (x : Chapter08PadicIntegers p) (a : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, a i < p) ∧ Tendsto (Chapter08PadicPartialSum p a) atTop (𝓝 x)

/-! Every p-adic integer has a unique base-p expansion. -/
theorem chapter08_padic_digit_expansion_unique
    (p : ℕ) [Fact p.Prime] (x : Chapter08PadicIntegers p) :
    ∃! a : ℕ → ℕ, Chapter08PadicExpansion p x a := by
  sorry

/-- The partial sum with all digits equal to p - 1. -/
def Chapter08PadicNegOnePartialSum (p n : ℕ) [Fact p.Prime] :
    Chapter08PadicIntegers p :=
  ∑ i ∈ Finset.range n,
    ((p - 1 : ℕ) : Chapter08PadicIntegers p) * (p : Chapter08PadicIntegers p) ^ i

/-! The displayed expansion -1 = (p-1) + (p-1)p + .... -/
theorem chapter08_padic_negative_one_partial_sum
    (p n : ℕ) [Fact p.Prime] :
    Chapter08PadicNegOnePartialSum p n =
      (p : Chapter08PadicIntegers p) ^ n - 1 := by
  sorry

theorem chapter08_padic_negative_one_difference
    (p n : ℕ) [Fact p.Prime] :
    Chapter08PadicNegOnePartialSum p n - (-1) =
      (p : Chapter08PadicIntegers p) ^ n := by
  sorry

theorem chapter08_padic_powers_tend_to_zero
    (p : ℕ) [Fact p.Prime] :
    Tendsto (fun n : ℕ => (p : Chapter08PadicIntegers p) ^ n) atTop (𝓝 0) := by
  sorry

theorem chapter08_padic_negative_one_expansion
    (p : ℕ) [Fact p.Prime] :
    Tendsto (fun n => Chapter08PadicNegOnePartialSum p n) atTop (𝓝 (-1)) := by
  sorry

/-- A single digit carry moves a unit from the zeroth digit to a higher power of p. -/
theorem chapter08_padic_single_digit_carry
    (p : ℕ) [Fact p.Prime] :
    ((p - 1 : ℕ) : Chapter08PadicIntegers p) + 1 =
      (p : Chapter08PadicIntegers p) := by
  sorry

theorem chapter08_higher_powers_are_smaller_p_adically
    (p n : ℕ) [Fact p.Prime] :
    ‖(p : Chapter08PadicIntegers p) ^ (n + 1)‖ <
      ‖(p : Chapter08PadicIntegers p) ^ n‖ := by
  sorry

/-- A Laurent expansion in Q_p starts at an arbitrary integral exponent. -/
def Chapter08PadicFieldPartialSum (p : ℕ) [Fact p.Prime]
    (N : ℤ) (a : ℕ → ℕ) (n : ℕ) : Chapter08PadicNumbers p :=
  ∑ i ∈ Finset.range n,
    (a i : Chapter08PadicNumbers p) *
      (p : Chapter08PadicNumbers p) ^ (N + (i : ℤ))

def Chapter08PadicLaurentExpansion (p : ℕ) [Fact p.Prime]
    (x : Chapter08PadicNumbers p) (N : ℤ) (a : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, a i < p) ∧
    Tendsto (Chapter08PadicFieldPartialSum p N a) atTop (𝓝 x)

/-- The first exponent with a nonzero digit, or top for the zero series. -/
def Chapter08FirstNonzeroExponent (N : ℤ) (a : ℕ → ℕ) : WithTop ℤ := by
  classical
  exact if h : ∃ i : ℕ, a i ≠ 0 then
    (N + (Nat.find h : ℤ) : WithTop ℤ)
  else ⊤

theorem chapter08_padic_valuation_is_first_nonzero_digit
    (p : ℕ) [Fact p.Prime] (x : Chapter08PadicNumbers p)
    (N : ℤ) (a : ℕ → ℕ)
    (ha : Chapter08PadicLaurentExpansion p x N a)
    (hnonzero : ∃ i : ℕ, a i ≠ 0) :
    Padic.addValuation x = Chapter08FirstNonzeroExponent N a := by
  sorry

theorem chapter08_rationals_are_dense_in_Qp
    (p : ℕ) [Fact p.Prime] :
    DenseRange (fun q : ℚ => (q : Chapter08PadicNumbers p)) := by
  sorry

theorem chapter08_Qp_has_countable_dense_subfield
    (p : ℕ) [Fact p.Prime] :
    DenseRange (fun q : ℚ => (q : Chapter08PadicNumbers p)) ∧ Countable ℚ := by
  sorry

theorem chapter08_Zp_is_uncountable
    (p : ℕ) [Fact p.Prime] : ¬ Countable (Chapter08PadicIntegers p) := by
  sorry

theorem chapter08_completion_adds_p_adic_elements
    (p : ℕ) [Fact p.Prime] :
    ¬ Function.Surjective (fun q : ℚ => (q : Chapter08PadicNumbers p)) := by
  sorry

theorem chapter08_Zp_is_compact
    (p : ℕ) [Fact p.Prime] : CompactSpace (Chapter08PadicIntegers p) := by
  sorry

/-! ### 8.4 Formal power series -/

abbrev Chapter08FormalPowerSeries (k : Type*) [Semiring k] := PowerSeries k
abbrev Chapter08FormalLaurentSeries (k : Type*) [Field k] := LaurentSeries k

/-- The truncation inverse limit for the polynomial variable X. -/
abbrev Chapter08FormalPowerSeriesInverseLimit (k : Type*) [Field k] :=
  Chapter08CompatibleFamily (Polynomial k) (Ideal.span {Polynomial.X})

theorem chapter08_power_series_inverse_limit
    (k : Type*) [Field k] :
    Nonempty (PowerSeries k ≃+* Chapter08FormalPowerSeriesInverseLimit k) := by
  sorry

/-- Constants give the canonical coefficient-field embedding into formal power series. -/
def Chapter08PowerSeriesConstants (k : Type*) [Semiring k] : k →+* PowerSeries k :=
  PowerSeries.C

theorem chapter08_power_series_constants_injective
    (k : Type*) [Field k] :
    Function.Injective (Chapter08PowerSeriesConstants k) := by
  sorry

theorem chapter08_power_series_is_fraction_field_of_power_series
    (k : Type*) [Field k] :
    IsFractionRing (PowerSeries k) (Chapter08FormalLaurentSeries k) := by
  sorry

theorem chapter08_formal_laurent_series_are_complete
    (k : Type*) [Field k] : CompleteSpace (Chapter08FormalLaurentSeries k) := by
  sorry

/-- Coefficientwise Cauchy data for a Laurent-series sequence. -/
def Chapter08LaurentCoefficientwiseCauchy
    {k : Type*} [Field k] (u : ℕ → Chapter08FormalLaurentSeries k) : Prop :=
  ∀ d : ℤ, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    (u m).coeff d = (u n).coeff d

/-- A common lower bound on the exponents occurring in a sequence of Laurent series. -/
def Chapter08CommonLaurentLowerBound
    {k : Type*} [Field k] (u : ℕ → Chapter08FormalLaurentSeries k) : Prop :=
  ∃ L : ℤ, ∀ n : ℕ, ∀ d : ℤ, d < L → (u n).coeff d = 0

-- The coefficientwise construction gives a common lower-bounded Laurent series limit. -/
theorem chapter08_laurent_series_cauchy_coefficient_construction
    (k : Type*) [Field k] (u : ℕ → Chapter08FormalLaurentSeries k)
    (hu : Chapter08LaurentCoefficientwiseCauchy u)
    (hL : Chapter08CommonLaurentLowerBound u) :
    ∃ x : Chapter08FormalLaurentSeries k,
      (∀ d : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (u n).coeff d = x.coeff d) ∧
        Tendsto u atTop (𝓝 x) := by
  sorry

/-! The filtration analogy Z_p ↔ k[[t]], Q_p ↔ k((t)), p ↔ t. -/
theorem chapter08_padic_formal_series_filtration_analogy
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] :
    IsDiscreteValuationRing (Chapter08PadicIntegers p) ∧
      IsDiscreteValuationRing (PowerSeries k) ∧
      CompleteSpace (Chapter08PadicIntegers p) ∧
      CompleteSpace (Chapter08FormalLaurentSeries k) := by
  sorry

theorem chapter08_formal_power_series_residue_field_is_constants
    (k : Type*) [Field k] :
    Nonempty (IsLocalRing.ResidueField (PowerSeries k) ≃+* k) := by
  sorry

theorem chapter08_power_series_preserves_characteristic
    (k : Type*) [Field k] (q : ℕ) [CharP k q] : CharP (PowerSeries k) q := by
  sorry

theorem chapter08_padic_numbers_have_characteristic_zero
    (p : ℕ) [Fact p.Prime] : CharZero (Chapter08PadicNumbers p) := by
  sorry

theorem chapter08_no_Fp_embedding_in_characteristic_zero
    {A : Type*} [Ring A] [CharZero A] (p : ℕ) [Fact p.Prime] :
    ¬ ∃ f : ZMod p →+* A, Function.Injective f := by
  sorry

/-! ### 8.5 Units and principal units -/

/-- The subgroup 1 + I ^ n inside the unit group. -/
def Chapter08UnitLayer
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) : Subgroup Aˣ where
  carrier := {u | ((u : Aˣ) : A) - 1 ∈ I ^ n}
  one_mem' := by
    simp
  mul_mem' := by
    intro u v hu hv
    sorry
  inv_mem' := by
    intro u hu
    sorry

/-- The first principal-unit group in a local ring. -/
abbrev Chapter08PrincipalUnitGroup
    (A : Type*) [CommRing A] [IsLocalRing A] : Subgroup Aˣ :=
  Chapter08UnitLayer A (IsLocalRing.maximalIdeal A) 1

/-- Reduction of units to units in the residue field. -/
def Chapter08UnitReduction
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Aˣ →* (IsLocalRing.ResidueField A)ˣ :=
  Units.map (IsLocalRing.residue A).toMonoidHom

theorem chapter08_unit_reduction_kernel
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (Chapter08UnitReduction A).ker = Chapter08PrincipalUnitGroup A := by
  sorry

-- Reduction gives A^× / U^1 ≅ k^×. -/
theorem chapter08_units_mod_principal_units
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Nonempty ((Aˣ ⧸ Chapter08PrincipalUnitGroup A) ≃*
      (IsLocalRing.ResidueField A)ˣ) := by
  sorry

/-- The additive residue-field layer represented inside the quotient modulo I^(n+1). -/
def Chapter08IdealLayer
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) :
    AddSubgroup (A ⧸ I ^ (n + 1)) :=
  ((I ^ n).map (Ideal.Quotient.mk (I ^ (n + 1)))).toAddSubgroup

/-- The (n+1)-st unit layer viewed as a subgroup of the n-th layer. -/
def Chapter08UnitLayerIn
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) :
    Subgroup (Chapter08UnitLayer A I n) :=
  (Chapter08UnitLayer A I (n + 1)).comap
    (Chapter08UnitLayer A I n).subtype

/-- The map 1+x ↦ x into the additive layer. -/
def Chapter08UnitLayerToIdealLayer
    (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ)
    (u : Chapter08UnitLayer A I n) : Chapter08IdealLayer A I n := by
  refine ⟨Ideal.Quotient.mk (I ^ (n + 1)) (((u : Aˣ) : A) - 1), ?_⟩
  sorry

/-! Each multiplicative layer is one copy of the additive residue-field layer. -/
theorem chapter08_principal_unit_layer_quotient
    (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hI : I = IsLocalRing.maximalIdeal A) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (Additive
          (Chapter08UnitLayer A I n ⧸ Chapter08UnitLayerIn A I n) ≃+
        Chapter08IdealLayer A I n) := by
  sorry

theorem chapter08_principal_unit_layer_formula
    (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hI : I = IsLocalRing.maximalIdeal A) (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : Additive
          (Chapter08UnitLayer A I n ⧸ Chapter08UnitLayerIn A I n) ≃+
        Chapter08IdealLayer A I n,
      ∀ u : Chapter08UnitLayer A I n,
        e (QuotientGroup.mk' (Chapter08UnitLayerIn A I n) u) =
          Chapter08UnitLayerToIdealLayer A I n u := by
  sorry

/-- Partial products of principal units in the adic completion. -/
def Chapter08PrincipalUnitPartialProduct
    {A : Type*} [CommRing A] (I : Ideal A) (a : ℕ → A) (m : ℕ) :
    AdicCompletion I A :=
  ∏ i ∈ Finset.range m, (1 + algebraMap A (AdicCompletion I A) (a i))

def Chapter08PrincipalUnitProductConverges
    {A : Type*} [CommRing A] (I : Ideal A) (a : ℕ → A)
    (x : AdicCompletion I A) : Prop :=
  Chapter08AdicConverges I (Chapter08PrincipalUnitPartialProduct I a) x

-- Infinite products of principal units converge when a_n tends to zero adically. -/
theorem chapter08_infinite_principal_unit_product_converges
    {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) (a : ℕ → A)
    (hI : I = IsLocalRing.maximalIdeal A)
    (ha : ∀ n : ℕ, a n ∈ I)
    (htends : Chapter08AdicTendsToZero I a) :
    ∃ x : AdicCompletion I A, Chapter08PrincipalUnitProductConverges I a x := by
  sorry

/-- Separating the valuation leaves a unit times a power of a uniformizer. -/
theorem chapter08_dvr_unit_power_separation
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) {x : A} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : Aˣ, x = (u : A) * π ^ n := by
  sorry

/-! ### 8.6 Complete does not mean algebraically closed -/

/-- An approximate root modulo I ^ n. -/
def Chapter08ApproximateRoot
    {A : Type*} [CommRing A] (I : Ideal A) (f : A[X]) (a : A) (n : ℕ) : Prop :=
  f.eval a ∈ I ^ n

/-- A unit whose residue is not a square. -/
def Chapter08NonsquareResidueUnit
    (A : Type*) [CommRing A] [IsLocalRing A] (u : A) : Prop :=
  IsUnit u ∧
    ¬ ∃ y : IsLocalRing.ResidueField A,
      y ^ 2 = IsLocalRing.residue A u

/-- A nonsquare residue unit cannot be a square in the local ring. -/
theorem chapter08_nonsquare_residue_unit_not_square
    (A : Type*) [CommRing A] [IsLocalRing A] (u : A)
    (hu : IsUnit u)
    (hns : ¬ ∃ y : IsLocalRing.ResidueField A,
      y ^ 2 = IsLocalRing.residue A u) :
    ¬ ∃ x : A, x ^ 2 = u := by
  sorry

-- The quadratic X^2-u is an explicit algebraic obstruction. -/
theorem chapter08_quadratic_without_root_from_nonsquare_residue
    (A : Type*) [CommRing A] [IsLocalRing A] (u : A)
    (hu : IsUnit u)
    (hns : ¬ ∃ y : IsLocalRing.ResidueField A,
      y ^ 2 = IsLocalRing.residue A u) :
    ¬ ∃ x : A, (Polynomial.X ^ 2 - Polynomial.C u).eval x = 0 := by
  sorry

theorem chapter08_complete_padic_field_not_algebraically_closed
    (p : ℕ) [Fact p.Prime] :
    CompleteSpace (Chapter08PadicNumbers p) ∧
      ¬ IsAlgClosed (Chapter08PadicNumbers p) := by
  sorry

/-! Simple roots do lift: this is the Henselian principle deferred to the next chapter. -/
theorem chapter08_simple_root_lifts_in_complete_local_ring
    (A : Type*) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    ∀ f : A[X], f.Monic →
      ∀ a₀ : IsLocalRing.ResidueField A,
        aeval a₀ f = 0 →
        aeval a₀ f.derivative ≠ 0 →
        ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
  sorry

theorem chapter08_complete_local_ring_is_henselian
    (A : Type*) [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    HenselianLocalRing A := by
  sorry

end
end ValuationsBook.Chapter08
