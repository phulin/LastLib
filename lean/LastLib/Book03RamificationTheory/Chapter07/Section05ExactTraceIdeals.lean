import LastLib.Book03RamificationTheory.Chapter07.Section04KaehlerDifferentials

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.5. Exact trace ideals -/

/-- The trace image of a fractional `B`-ideal. -/
def chapter07TraceImage
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (I : FractionalIdeal B⁰ L) : Set K :=
  Algebra.trace K L '' (I : Set L)

theorem chapter07_mem_trace_image_iff
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (I : FractionalIdeal B⁰ L) (x : K) :
    x ∈ chapter07TraceImage A B K L I ↔
      ∃ y : L, y ∈ (I : Set L) ∧ Algebra.trace K L y = x := Iff.rfl

/-- The integer exponent on the base side of the exact trace formula. -/
def chapter07TraceImageExponent (n : ℤ) (d e : ℕ) : ℤ :=
  chapter07FloorDiv n (d : ℤ) e

theorem chapter07TraceImageExponent_eq_displayed_floor
    (n : ℤ) (d e : ℕ) (he : 0 < e) :
    chapter07TraceImageExponent n d e =
      ⌊(n + d : ℚ) / e⌋ := by
  exact chapter07FloorDiv_eq_floor n (d : ℤ) e he

/-- The exact trace-image formula for all integral and fractional powers. -/
theorem chapter07_trace_fractional_power_formula
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B) (e d : ℕ)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (he : 0 < e)
    (hmap :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        chapter07FractionalIdealPower B L mB (e : ℤ))
    (hD : chapter07DifferentIdeal A B = mB ^ d) (n : ℤ) :
    chapter07TraceImage A B K L
        (chapter07FractionalIdealPower B L mB n) =
      (chapter07FractionalIdealPower A K mA
        (chapter07TraceImageExponent n d e) : Set K) := by
  sorry

theorem chapter07_trace_fractional_power_contained_iff
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B) (e d : ℕ)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (he : 0 < e)
    (hmap :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        chapter07FractionalIdealPower B L mB (e : ℤ))
    (hD : chapter07DifferentIdeal A B = mB ^ d) (n r : ℤ) :
    chapter07TraceImage A B K L
        (chapter07FractionalIdealPower B L mB n) ⊆
      (chapter07FractionalIdealPower A K mA r : Set K) ↔
        r ≤ chapter07TraceImageExponent n d e := by
  sorry

def chapter07IntegralRingSet
    (B L : Type*) [CommRing B] [Field L] [Algebra B L] : Set L :=
  Set.range (algebraMap B L)

def chapter07MaximalIdealSet
    (B L : Type*) [CommRing B] [Field L] [Algebra B L]
    (mB : Ideal B) : Set L :=
  {x | ∃ b : B, b ∈ mB ∧ x = algebraMap B L b}

theorem chapter07_unramified_exact_integral_trace
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hmap :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        chapter07FractionalIdealPower B L mB (1 : ℤ))
    (hD : chapter07DifferentIdeal A B = mB ^ 0) :
    Algebra.trace K L '' chapter07IntegralRingSet B L =
        Set.range (algebraMap A K) ∧
      Algebra.trace K L '' chapter07MaximalIdealSet B L mB =
        chapter07MaximalIdealSet A K mA := by
  sorry

theorem chapter07_tame_exact_integral_and_maximal_trace
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B) (e : ℕ)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (he : 0 < e)
    (hmap :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        chapter07FractionalIdealPower B L mB (e : ℤ))
    (hD : chapter07DifferentIdeal A B = mB ^ (e - 1)) :
    Algebra.trace K L '' chapter07IntegralRingSet B L =
        Set.range (algebraMap A K) ∧
      Algebra.trace K L '' chapter07MaximalIdealSet B L mB =
        chapter07MaximalIdealSet A K mA := by
  sorry

/- The quadratic trace computation used for `Q_2(sqrt 2)`. -/
def chapter07QuadraticTraceModel
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (θ : L) : Prop :=
  Module.finrank K L = 2 ∧ Algebra.trace K L θ = 0

theorem chapter07_quadratic_trace_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (θ : L)
    (hmodel : chapter07QuadraticTraceModel K L θ) (a b : K) :
    Algebra.trace K L
        (algebraMap K L a + algebraMap K L b * θ) = 2 * a := by
  sorry

theorem chapter07_sqrt_two_trace_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (sqrtTwo : L)
    (hmodel : chapter07QuadraticTraceModel K L sqrtTwo)
    (hsquare : sqrtTwo ^ 2 = algebraMap K L 2) (a b : K) :
    Algebra.trace K L
        (algebraMap K L a + algebraMap K L b * sqrtTwo) = 2 * a := by
  exact chapter07_quadratic_trace_formula K L sqrtTwo hmodel a b

theorem chapter07_sqrt_two_integral_trace_is_two_adic
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (sqrtTwo : L)
    (hmodel : chapter07QuadraticTraceModel K L sqrtTwo)
    (hsquare : sqrtTwo ^ 2 = algebraMap K L 2)
    (hintegral_trace : ∀ a : K, ∃ x : K,
      Algebra.trace K L (algebraMap K L a +
        algebraMap K L 0 * sqrtTwo) = 2 * x) :
    ∀ a b : K,
      Algebra.trace K L (algebraMap K L a + algebraMap K L b * sqrtTwo) =
        2 * a := by
  intro a b
  exact chapter07_sqrt_two_trace_formula K L sqrtTwo hmodel hsquare a b

/- The exact linear term in the norm expansion, with the higher terms named. -/
theorem chapter07_norm_one_add_trace_remainder
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.norm K (1 + x) =
      1 + Algebra.trace K L x +
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormRemainder
          K L x := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_norm_one_add_linearizes_to_trace
    K L x

/-- A precise predicate for the norm-lifting obstruction mentioned after the
    first-order expansion. -/
def chapter07NormLiftingFailure
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    (ρK : K →+* k) (ρL : L →+* l)
    (unitLayerL : Set L) (unitLayerK : Set K) : Prop :=
  Function.Surjective (Algebra.norm k (S := l)) ∧
    ¬Set.SurjOn (Algebra.norm K (S := L)) unitLayerL unitLayerK

end

end LastLib.Book03RamificationTheory.Chapter07
