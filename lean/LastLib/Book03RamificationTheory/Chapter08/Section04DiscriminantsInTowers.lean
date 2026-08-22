import LastLib.Book03RamificationTheory.Chapter08.Section01FromADualLatticeToAnIdealDownstairs
import LastLib.Book03RamificationTheory.Chapter08.Section03TransitivityOfTheDifferent

namespace LastLib.Book03RamificationTheory.Chapter08

noncomputable section

open Ideal
open scoped BigOperators nonZeroDivisors

/-! ## 8.4. Discriminants in towers -/

/- LOCAL_DEPENDENCY_GUESS: the preceding chapters provide the numerical
   invariants `e`, `f`, `d`, and `δ` attached to a finite extension, but do not
   yet expose them in one tower record.  This record contains only the
   multiplicativity and trace-dual identities used by the displayed tower
   calculation; it does not assume the discriminant formula as a conclusion.
-/
structure Chapter08TowerNumericalData where
  degreeLK : ℕ
  degreeLM : ℕ
  degreeMK : ℕ
  ramificationLK : ℕ
  ramificationLM : ℕ
  ramificationMK : ℕ
  residueLK : ℕ
  residueLM : ℕ
  residueMK : ℕ
  differentLK : ℕ
  differentLM : ℕ
  differentMK : ℕ
  discriminantLK : ℕ
  discriminantLM : ℕ
  discriminantMK : ℕ
  degree_mul : degreeLK = degreeLM * degreeMK
  degreeLM_eq_ramification_mul_residue :
    degreeLM = ramificationLM * residueLM
  degreeMK_eq_ramification_mul_residue :
    degreeMK = ramificationMK * residueMK
  ramification_mul : ramificationLK = ramificationLM * ramificationMK
  residue_mul : residueLK = residueLM * residueMK
  different_transitivity :
    differentLK = differentLM + ramificationLM * differentMK
  discriminant_eq_residue_mul_different :
    discriminantLK = residueLK * differentLK
  middle_discriminant_eq_residue_mul_different :
    discriminantLM = residueLM * differentLM
  base_discriminant_eq_residue_mul_different :
    discriminantMK = residueMK * differentMK

theorem chapter08_tower_discriminant_exponent_formula
    (T : Chapter08TowerNumericalData) :
    T.discriminantLK = T.degreeLM * T.discriminantMK +
      T.residueMK * T.discriminantLM := by
  rw [T.discriminant_eq_residue_mul_different, T.different_transitivity,
    T.residue_mul, T.middle_discriminant_eq_residue_mul_different,
    T.base_discriminant_eq_residue_mul_different,
    T.degreeLM_eq_ramification_mul_residue]; ring

/- The ideal-valued formula is stated with the complete finite-separable
   integral-closure interface.  In particular, no Galois typeclass occurs. -/
theorem chapter08_discriminant_ideal_tower_formula
    (A B C K M L : Type*) [CommRing A]
    [CommRing B] [CommRing C]
    [Field K] [Field M] [Field L]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra K M] [Algebra M L]
    [Algebra K L]
    [Algebra A M] [Algebra B M] [Algebra C L]
    [Algebra B L] [Algebra A L]
    [IsScalarTower A B C] [IsScalarTower A K M]
    [IsScalarTower K M L] [IsScalarTower A M L]
    [IsScalarTower A B L] [IsScalarTower B C L]
    [IsScalarTower A C L]
    [IsFractionRing A K] [IsFractionRing B M] [IsFractionRing C L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K M] [Algebra.IsSeparable M L]
    [Algebra.IsSeparable K L]
    [IsIntegralClosure B A M] [IsIntegralClosure C B L]
    [IsIntegralClosure C A L]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Module.Finite B C] [Module.Free B C] [Module.IsTorsionFree B C]
    [Module.Finite A C] [Module.Free A C] [Module.IsTorsionFree A C]
    [Algebra.IsIntegral A B] [Algebra.IsIntegral B C]
    [Algebra.IsIntegral A C] :
    chapter08RelativeDiscriminantIdeal A C =
      chapter08RelativeDiscriminantIdeal A B ^ (Module.finrank M L) *
        Ideal.relNorm A (chapter08RelativeDiscriminantIdeal B C) := by
  sorry

theorem chapter08_discriminant_ideal_tower_formula_expanded
    (A B C K M L : Type*) [CommRing A]
    [CommRing B] [CommRing C]
    [Field K] [Field M] [Field L]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra K M] [Algebra M L]
    [Algebra K L]
    [Algebra A M] [Algebra B M] [Algebra C L]
    [Algebra B L] [Algebra A L]
    [IsScalarTower A B C] [IsScalarTower A K M]
    [IsScalarTower K M L] [IsScalarTower A M L]
    [IsScalarTower A B L] [IsScalarTower B C L]
    [IsScalarTower A C L]
    [IsFractionRing A K] [IsFractionRing B M] [IsFractionRing C L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K M] [Algebra.IsSeparable M L]
    [Algebra.IsSeparable K L]
    [IsIntegralClosure B A M] [IsIntegralClosure C B L]
    [IsIntegralClosure C A L]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Module.Finite B C] [Module.Free B C] [Module.IsTorsionFree B C]
    [Module.Finite A C] [Module.Free A C] [Module.IsTorsionFree A C]
    [Algebra.IsIntegral A B] [Algebra.IsIntegral B C]
    [Algebra.IsIntegral A C] :
    chapter08RelativeDiscriminantIdeal A C =
      chapter08RelativeDiscriminantIdeal A B ^ (Module.finrank M L) *
        Ideal.relNorm A (Ideal.relNorm B (chapter08DifferentIdeal B C)) := by
  sorry

/- The same intrinsic identity is deliberately exposed without a Galois
   hypothesis, recording the source's nongalois warning as an API fact. -/
theorem chapter08_nongalois_discriminant_formula_is_intrinsic
    (A B K L : Type*) [CommRing A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] :
    chapter08RelativeDiscriminantIdeal A B =
      Ideal.relNorm A (chapter08DifferentIdeal A B) := by
  exact chapter08_relative_discriminant_ideal_eq_norm_different A B K L

end

end LastLib.Book03RamificationTheory.Chapter08
