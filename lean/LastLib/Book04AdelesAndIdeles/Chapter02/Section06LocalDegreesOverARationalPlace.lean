import LastLib.Book04AdelesAndIdeles.Chapter02.Section02TheGlobalNormalization
import LastLib.Book04AdelesAndIdeles.Chapter02.Section03TheRationalModelForAllNormalizations
import LastLib.Book04AdelesAndIdeles.Chapter02.Section04LocalIntegersAndLocalUnits
import LastLib.Book04AdelesAndIdeles.Chapter02.Section05ExtensionAndLocalNorms
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RamificationInertia.Basic

namespace LastLib.Book04AdelesAndIdeles.Chapter02

noncomputable section

universe u

open NumberField
open scoped BigOperators Classical NumberField.LiesOver WithZero

/-! ## 2.6. Local degrees over a rational place -/

/-- The ideal `p 𝓞_K` attached to a rational prime. -/
def Chapter02RationalPrimeIdeal
    {K : Type*} [Field K] [NumberField K]
    (p : Chapter02RationalPrime) : Ideal (𝓞 K) :=
  Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p.1 : ℤ)})

/-- Height-one primes of `𝓞_K` lying over the rational prime `p`. -/
def Chapter02PrimeAbove
    (K : Type*) [Field K] [NumberField K]
    (p : Chapter02RationalPrime) : Type _ :=
  {q : IsDedekindDomain.HeightOneSpectrum (𝓞 K) //
    q.asIdeal.LiesOver (Ideal.span {(p.1 : ℤ)})}

def Chapter02RamificationIndex
    {K : Type*} [Field K] [NumberField K]
    {p : Chapter02RationalPrime} (q : Chapter02PrimeAbove K p) : ℕ :=
  q.1.asIdeal.ramificationIdx ℤ

def Chapter02ResidueDegree
    {K : Type*} [Field K] [NumberField K]
    {p : Chapter02RationalPrime} (q : Chapter02PrimeAbove K p) : ℕ :=
  q.1.asIdeal.inertiaDeg ℤ

def Chapter02LocalDegree
    {K : Type*} [Field K] [NumberField K]
    {p : Chapter02RationalPrime} (q : Chapter02PrimeAbove K p) : ℕ :=
  Chapter02RamificationIndex q * Chapter02ResidueDegree q

theorem chapter02_local_degree_pos
    {K : Type*} [Field K] [NumberField K]
    {p : Chapter02RationalPrime} (q : Chapter02PrimeAbove K p) :
    0 < Chapter02LocalDegree q := by
  exact Nat.mul_pos (Ideal.ramificationIdx_pos q.1.asIdeal ℤ)
    (Ideal.inertiaDeg_pos q.1.asIdeal ℤ)

/-- Factorization of `p 𝓞_K` into the primes above `p`. -/
theorem chapter02_rational_prime_factorization
    {K : Type*} [Field K] [NumberField K]
    (p : Chapter02RationalPrime) [Fintype (Chapter02PrimeAbove K p)] :
    Chapter02RationalPrimeIdeal p =
      ∏ q : Chapter02PrimeAbove K p,
        q.1.asIdeal ^ Chapter02RamificationIndex q := by
  let : Fact p.1.Prime := ⟨p.2⟩
  have hp0 : (Ideal.span {(p.1 : ℤ)} : Ideal ℤ) ≠ 0 := by
    simp [p.2.ne_zero]
  let e : Chapter02PrimeAbove K p ≃
      (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K) :=
    { toFun := fun q => ⟨q.1.asIdeal, ⟨q.1.isPrime, q.2⟩⟩
      invFun := fun P =>
        ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver hp0 P.2⟩, P.2.2⟩
      left_inv := by
        intro q
        apply Subtype.ext
        rfl
      right_inv := by
        intro P
        apply Subtype.ext
        rfl }
  have hfac := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 K)
    (p := Ideal.span {(p.1 : ℤ)}) hp0
  calc
    Chapter02RationalPrimeIdeal p =
        Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p.1 : ℤ)}) := rfl
    _ = ∏ P ∈ (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K),
        P ^ P.ramificationIdx ℤ := hfac
    _ = ∏ P : (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K),
        P.1 ^ P.1.ramificationIdx ℤ := by
      exact (Finset.prod_set_coe _).symm
    _ = ∏ q : Chapter02PrimeAbove K p,
        q.1.asIdeal ^ Chapter02RamificationIndex q := by
      exact (Fintype.prod_equiv e _ _ (fun q => rfl)).symm

theorem chapter02_rational_prime_residue_field_cardinality
    {K : Type*} [Field K] [NumberField K]
    (p : Chapter02RationalPrime) (q : Chapter02PrimeAbove K p) :
    Chapter02LocalResidueCardinality q.1 =
      p.1 ^ Chapter02ResidueDegree q := by
  let : q.1.asIdeal.LiesOver (Ideal.span {(p.1 : ℤ)}) := q.2
  exact (Ideal.pow_inertiaDeg p.1 q.1.asIdeal).symm

theorem chapter02_sum_of_local_degrees_is_the_global_degree
    {K : Type*} [Field K] [NumberField K]
    (p : Chapter02RationalPrime) [Fintype (Chapter02PrimeAbove K p)] :
    (∑ q : Chapter02PrimeAbove K p, Chapter02LocalDegree q) =
      Chapter02GlobalDegree K := by
  let pI : Ideal ℤ := Ideal.span {(p.1 : ℤ)}
  have hp0 : pI ≠ 0 := by
    simp [pI, p.2.ne_zero]
  have hpIprime : pI.IsPrime := by
    dsimp [pI]
    exact (Ideal.span_singleton_prime (α := ℤ)
      (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
  have pIprime' : pI.IsPrime := hpIprime
  have hpImax : pI.IsMaximal := Ideal.IsPrime.isMaximal hpIprime hp0
  have pImax' : pI.IsMaximal := hpImax
  let e : Chapter02PrimeAbove K p ≃ pI.primesOver (𝓞 K) :=
    { toFun := fun q => ⟨q.1.asIdeal, ⟨q.1.isPrime, q.2⟩⟩
      invFun := fun P =>
        ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver hp0 P.2⟩, P.2.2⟩
      left_inv := by
        intro q
        apply Subtype.ext
        rfl
      right_inv := by
        intro P
        apply Subtype.ext
        rfl }
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (p := pI) (S := 𝓞 K)
  calc
    (∑ q : Chapter02PrimeAbove K p, Chapter02LocalDegree q) =
        ∑ P : pI.primesOver (𝓞 K),
          P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ :=
      Fintype.sum_equiv e _ _ (fun q => rfl)
    _ = Module.finrank ℤ (𝓞 K) := hsum
    _ = Chapter02GlobalDegree K := by
      simpa [Chapter02GlobalDegree] using NumberField.RingOfIntegers.rank K

/-- The local-degree formula `[K_𝔭 : ℚ_p] = e_𝔭 f_𝔭`, with the compatible
`ℚ_[p]`-algebra on the finite completion made explicit. -/
theorem chapter02_local_completion_degree_formula
    {K : Type u} [Field K] [NumberField K]
    (p : Chapter02RationalPrime) (q : Chapter02PrimeAbove K p)
    [Algebra (@Padic p.1 ⟨p.2⟩) (Chapter02LocalField q.1)]
    [FiniteDimensional (@Padic p.1 ⟨p.2⟩) (Chapter02LocalField q.1)]
    [IsScalarTower ℚ (@Padic p.1 ⟨p.2⟩) (Chapter02LocalField q.1)]
    (hcompatible :
      ∀ a : ℚ,
        algebraMap (@Padic p.1 ⟨p.2⟩) (Chapter02LocalField q.1)
            (algebraMap ℚ (@Padic p.1 ⟨p.2⟩) a) =
          algebraMap K (Chapter02LocalField q.1) (algebraMap ℚ K a))
    (hcontinuous :
      Continuous (algebraMap (@Padic p.1 ⟨p.2⟩) (Chapter02LocalField q.1))) :
    Module.finrank (@Padic p.1 ⟨p.2⟩) (Chapter02LocalField q.1) =
      Chapter02LocalDegree q := by
  sorry

theorem chapter02_padic_scalar_restriction_power
    {p : ℕ} [Fact p.Prime]
    {Kp : Type*} [Field Kp] [Algebra ℚ_[p] Kp]
    [FiniteDimensional ℚ_[p] Kp]
    (D : Chapter02NormalizedLocalNormData (ℚ_[p]) Kp) (a : ℚ_[p]) :
    D.abvL (algebraMap ℚ_[p] Kp a) =
      D.abvK a ^ Module.finrank ℚ_[p] Kp := by
  exact chapter02_normalized_local_scalar_restriction D a

/-- The canonical rational `p`-adic order on `ℚˣ`. -/
noncomputable def Chapter02RationalPAdicOrder
    (p : Chapter02RationalPrime) (a : ℚˣ) : ℤ :=
  letI : Fact p.1.Prime := ⟨p.2⟩
  (-(WithZero.unzero
      ((Rat.padicValuation p.1).ne_zero_iff.mpr a.ne_zero)).toAdd)

/-- On scalar elements, the finite order is `e_𝔭 v_p`. -/
theorem chapter02_scalar_order_is_ramification_times_rational_order
    {K : Type*} [Field K] [NumberField K]
    (p : Chapter02RationalPrime) (q : Chapter02PrimeAbove K p) (a : ℚˣ) :
    LastLib.Book04AdelesAndIdeles.Chapter01.chapter01UnitOrder q.1
        (Units.map (algebraMap ℚ K) a) =
      (Chapter02RamificationIndex q : ℤ) * Chapter02RationalPAdicOrder p a := by
  sorry

/-- The finite-place scalar norm is the rational `p`-adic norm raised to the
local degree. -/
theorem chapter02_rational_scalar_value_at_a_finite_place
    {K : Type*} [Field K] [NumberField K]
    (p : Chapter02RationalPrime) (q : Chapter02PrimeAbove K p) (a : ℚ) :
    NumberField.FinitePlace.mk q.1 (algebraMap ℚ K a) =
      Chapter02RationalPadicValue p a ^ Chapter02LocalDegree q := by
  sorry

theorem chapter02_finite_place_restriction_exponent_is_local_degree
    {K : Type*} [Field K] [NumberField K]
    (p : Chapter02RationalPrime) (q : Chapter02PrimeAbove K p) :
    Chapter02RestrictionHasDegreeExponent
      (Sum.inl (NumberField.FinitePlace.mk q.1) : Chapter02Place K)
      (Chapter02RationalNormalizedPlace.finite p) (Chapter02LocalDegree q) := by
  sorry

theorem chapter02_product_over_places_above_a_rational_prime
    {K : Type*} [Field K] [NumberField K]
    (p : Chapter02RationalPrime) [Fintype (Chapter02PrimeAbove K p)] (a : ℚ) :
    (∏ q : Chapter02PrimeAbove K p,
      NumberField.FinitePlace.mk q.1 (algebraMap ℚ K a)) =
      Chapter02RationalPadicValue p a ^ Chapter02GlobalDegree K := by
  sorry

/-- The infinite-place local degree identity is Mathlib's `mult` formula. -/
theorem chapter02_infinite_local_degree_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L)
    [w.LiesOver v] :
    v.mult * Module.finrank v.Completion w.Completion = w.mult := by
  exact NumberField.InfinitePlace.mult_mul_finrank v w

theorem chapter02_infinite_place_restriction_exponent_is_weight
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace ℚ) (w : NumberField.InfinitePlace K)
    [w.LiesOver v] :
    Chapter02RestrictionHasDegreeExponent
      (Sum.inr w : Chapter02Place K)
      Chapter02RationalNormalizedPlace.real w.mult := by
  exact fun a => by
    change (w (algebraMap ℚ K a) ^ w.mult) =
      (Rat.AbsoluteValue.real a ^ w.mult)
    have hv0 := congrArg (fun f : AbsoluteValue ℚ ℝ => f a)
      (AbsoluteValue.LiesOver.comp_eq w.1 v.1)
    change w (algebraMap ℚ K a) = v a at hv0
    rw [hv0, Rat.infinitePlace_apply, Rat.AbsoluteValue.real_eq_abs]

theorem chapter02_real_infinite_place_local_degree_is_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L)
    [w.LiesOver v] (hw : w.IsReal) :
    Module.finrank v.Completion w.Completion = 1 := by
  exact NumberField.InfinitePlace.IsUnramified.finrank_eq_one v (hw.isUnramified K)

theorem chapter02_complex_infinite_place_local_degree_is_two_over_a_real_place
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L)
    [w.LiesOver v] (hv : v.IsReal) (hw : w.IsComplex) :
    Module.finrank v.Completion w.Completion = 2 := by
  have hram : w.IsRamified K := by
    rw [NumberField.InfinitePlace.isRamified_iff,
      NumberField.InfinitePlace.LiesOver.comap_eq w v]
    exact ⟨hw, hv⟩
  rw [hram.finrank_eq_two v]

/-- Infinite places lying over a fixed rational infinite place. -/
abbrev Chapter02InfinitePlaceAbove
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace ℚ) : Type _ :=
  {w : NumberField.InfinitePlace K // w.LiesOver v}

theorem chapter02_product_over_infinite_places_above_a_rational_place
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace ℚ) (a : ℚ) :
    (∏ w : Chapter02InfinitePlaceAbove K v,
      w.1 (algebraMap ℚ K a) ^ w.1.mult) =
      v a ^ Chapter02GlobalDegree K := by
  sorry

/-- Every rational scalar sees total local degree `n=[K:ℚ]`. -/
theorem chapter02_rational_scalar_product_over_all_places
    {K : Type*} [Field K] [NumberField K]
    {a : ℚ} (ha : a ≠ 0) :
    Chapter02GlobalProduct (algebraMap ℚ K a) =
      Chapter02RationalGlobalProduct a ^ Chapter02GlobalDegree K := by
  sorry

theorem chapter02_infinite_weights_sum_to_the_global_degree
    {K : Type*} [Field K] [NumberField K] :
    ∑ w : Chapter02InfinitePlace K, w.mult = Chapter02GlobalDegree K := by
  exact NumberField.InfinitePlace.sum_mult_eq

/-- The global degree is multiplicative in a finite tower. -/
theorem chapter02_global_degree_is_multiplicative_in_a_tower
    {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [Module.Finite K L] [IsScalarTower ℚ K L] :
    Chapter02GlobalDegree L = Chapter02GlobalDegree K * Module.finrank K L := by
  sorry

/-- The local norm map is normalized without inserting an additional local-degree
power; the degree appears in scalar restriction instead. -/
theorem chapter02_local_norm_map_has_no_correction_exponent
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter02NormalizedLocalNormData K L) :
    ∀ y : L, D.abvK (Algebra.norm K y) = D.abvL y := by
  exact fun y => chapter02_normalized_local_norm_identity D y

end

end LastLib.Book04AdelesAndIdeles.Chapter02
