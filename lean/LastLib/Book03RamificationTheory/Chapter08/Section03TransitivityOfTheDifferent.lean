import LastLib.Book03RamificationTheory.Chapter08.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter08

noncomputable section

open Ideal
open scoped BigOperators nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-! ## 8.3. Transitivity of the different -/

/- The displayed Hom-identification is used below only through its trace
   compatibility.  This formulation avoids choosing a noncanonical module
   structure on the `A`-dual of `B`. -/
theorem chapter08_trace_hom_tower_identification
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Free A B] [Module.Finite A B]
    [Module.Free B C] [Module.Finite B C]
    (x : C) (b : B) :
    Algebra.trace A C (x * algebraMap B C b) =
      Algebra.trace A B (Algebra.trace B C x * b) := by
  sorry

noncomputable def chapter08_trace_hom_tower_equivalence
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Free A B] [Module.Finite A B]
    [Module.Free B C] [Module.Finite B C] :
    Chapter08TraceHomTowerEquivalence A B C := by
  sorry

theorem chapter08_trace_hom_tower_compatibility
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Free A B] [Module.Finite A B]
    [Module.Free B C] [Module.Finite B C] :
    chapter08TraceHomTowerCompatibility A B C := by
  intro x b
  exact chapter08_trace_hom_tower_identification A B C x b

/- The fractional-lattice form of trace transitivity is retained separately
   from the ideal formula.  It is the form used when passing to codifferents. -/
theorem chapter08_different_ideal_transitivity
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
    chapter08DifferentIdeal A C =
      chapter08DifferentIdeal B C *
        (chapter08DifferentIdeal A B).map (algebraMap B C) := by
  sorry

theorem chapter08_different_ideal_transitivity_canonical
    (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsDomain A] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
    differentIdeal A C =
      differentIdeal B C * (differentIdeal A B).map (algebraMap B C) := by
  sorry

/- The fractional-ideal transitivity formula extends the middle ideal
   upstairs; the inverse-lattice version is recorded immediately below. -/
theorem chapter08_different_fractional_transitivity
    (A B C K M N : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A]
    [Field K] [Field M] [Field N]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra K M] [Algebra M N] [Algebra K N] [Algebra A M]
    [Algebra B M] [Algebra C N] [Algebra A N] [Algebra B N]
    [IsScalarTower A B C] [IsScalarTower A K M]
    [IsScalarTower A B M]
    [IsScalarTower K M N] [IsScalarTower A M N]
    [IsScalarTower A K N] [IsScalarTower A B N]
    [IsScalarTower B M N] [IsScalarTower B C N]
    [IsScalarTower A C N]
    [IsFractionRing A K] [IsFractionRing B M] [IsFractionRing C N]
    [FiniteDimensional K M] [FiniteDimensional M N] [FiniteDimensional K N]
    [Algebra.IsSeparable K M] [Algebra.IsSeparable M N]
    [Algebra.IsSeparable K N]
    [IsIntegralClosure B A M] [IsIntegralClosure C B N]
    [IsIntegralClosure C A N] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C] :
    LastLib.Book03RamificationTheory.Chapter07.chapter07DifferentFractionalIdeal A C K N =
      LastLib.Book03RamificationTheory.Chapter07.chapter07DifferentFractionalIdeal B C M N *
        FractionalIdeal.extendedHom N C
          (LastLib.Book03RamificationTheory.Chapter07.chapter07DifferentFractionalIdeal A B K M) := by
  sorry

theorem chapter08_trace_dual_product_formula
    (A B C K M N : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A]
    [Field K] [Field M] [Field N]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra K M] [Algebra M N] [Algebra K N] [Algebra A M]
    [Algebra B M] [Algebra C N] [Algebra A N] [Algebra B N]
    [IsScalarTower A B C] [IsScalarTower A K M]
    [IsScalarTower A B M]
    [IsScalarTower K M N] [IsScalarTower A M N]
    [IsScalarTower A K N] [IsScalarTower A B N]
    [IsScalarTower B M N] [IsScalarTower B C N]
    [IsScalarTower A C N]
    [IsFractionRing A K] [IsFractionRing B M] [IsFractionRing C N]
    [FiniteDimensional K M] [FiniteDimensional M N] [FiniteDimensional K N]
    [Algebra.IsSeparable K M] [Algebra.IsSeparable M N]
    [Algebra.IsSeparable K N]
    [IsIntegralClosure B A M] [IsIntegralClosure C B N]
    [IsIntegralClosure C A N] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C] :
    LastLib.Book03RamificationTheory.Chapter07.chapter07CodifferentFractionalIdeal A C K N =
      LastLib.Book03RamificationTheory.Chapter07.chapter07CodifferentFractionalIdeal B C M N *
        FractionalIdeal.extendedHom N C
          (LastLib.Book03RamificationTheory.Chapter07.chapter07CodifferentFractionalIdeal A B K M) := by
  sorry

/- The valuation exponent of an extended ideal is multiplied by the
   ramification index. -/
theorem chapter08_extended_power
    (B C : Type*) [CommRing B] [CommRing C] [Algebra B C]
    (mB : Ideal B) (mC : Ideal C) (e : ℕ)
    (hmap : Ideal.map (algebraMap B C) mB = mC ^ e) (d : ℕ) :
    Ideal.map (algebraMap B C) (mB ^ d) = mC ^ (e * d) := by
  sorry

theorem chapter08_different_exponent_transitivity
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C]
    [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    (mB : Ideal B) (mC : Ideal C) (dAB dBC dAC eBC : ℕ)
    (hAB : chapter08DifferentIdeal A B = mB ^ dAB)
    (hBC : chapter08DifferentIdeal B C = mC ^ dBC)
    (hAC : chapter08DifferentIdeal A C = mC ^ dAC)
    (hmap : Ideal.map (algebraMap B C) mB = mC ^ eBC)
    (hpow_unique : ∀ {i j : ℕ}, mC ^ i = mC ^ j → i = j) :
    dAC = dBC + eBC * dAB := by
  sorry

theorem chapter08_different_exponent_transitivity_from_unique_exponents
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C]
    [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    (mB : Ideal B) (mC : Ideal C) (eBC : ℕ)
    (hmap : Ideal.map (algebraMap B C) mB = mC ^ eBC)
    (hAB : ∃! d : ℕ, chapter08DifferentIdeal A B = mB ^ d)
    (hBC : ∃! d : ℕ, chapter08DifferentIdeal B C = mC ^ d)
    (hAC : ∃! d : ℕ, chapter08DifferentIdeal A C = mC ^ d)
    (hpow_unique : ∀ {i j : ℕ}, mC ^ i = mC ^ j → i = j) :
    chapter08UniqueIdealExponent mC (chapter08DifferentIdeal A C) hAC =
      chapter08UniqueIdealExponent mC (chapter08DifferentIdeal B C) hBC +
        eBC * chapter08UniqueIdealExponent mB (chapter08DifferentIdeal A B) hAB := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter08
