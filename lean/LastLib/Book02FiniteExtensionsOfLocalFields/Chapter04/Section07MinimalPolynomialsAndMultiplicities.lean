import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section06TracePairingsAndSeparability

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

open IntermediateField
open scoped BigOperators Polynomial

/-! ## 4.7. Minimal polynomials and multiplicities -/

/- The trace formula records the `[L : K(x)]` multiplicity (§4.7). -/
theorem chapter04_trace_minpoly_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.trace K L x =
      Module.finrank K K⟮x⟯ * -(minpoly K x).nextCoeff := by
  sorry

/- The norm formula records the same multiplicity (§4.7). -/
theorem chapter04_norm_minpoly_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.norm K x =
      (((-1 : K) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^
        Module.finrank K K⟮x⟯) := by
  sorry

/- Purely inseparable minimal polynomials are Frobenius powers (§4.7). -/
theorem chapter04_purely_inseparable_minpoly_shape
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] (p : ℕ) [ExpChar K p] (x : L) :
    ∃ r : ℕ, ∃ a : K,
      minpoly K x = (Polynomial.X : K[X]) ^ (p ^ r) - Polynomial.C a := by
  sorry

/- The trace vanishes for the purely inseparable minimal-polynomial shapes
from §4.7, while the norm retains the constant term. -/
theorem chapter04_purely_inseparable_generator_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) [Fact p.Prime] [CharP K p]
    (α : L) (a : K) (hpower : α ^ p = algebraMap K L a)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = p) :
    Algebra.norm K α = (-1 : K) ^ (p + 1) * a := by
  sorry

/- Coefficients of the minimal polynomial of an integral element lie in the
integrally closed base ring (§4.7). -/
theorem chapter04_integral_minpoly_coefficients_in_base
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (x : B) :
    ∀ i : ℕ, ∃ a : A,
      algebraMap A K a = (minpoly K (algebraMap B L x)).coeff i := by
  sorry

/- A unit has a unit constant coefficient in its minimal polynomial (§4.7). -/
theorem chapter04_integral_unit_minpoly_constant_coefficient_is_unit
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (x : B) (hx : IsUnit x) :
    ∃ u : Aˣ,
      algebraMap A K (u : A) =
        (minpoly K (algebraMap B L x)).coeff 0 := by
  sorry

/-
The totally ramified uniformizer case has Eisenstein shape (§4.7).  The
conclusion uses Book 1 Chapter 12's coefficient-level Eisenstein interface.
-/
theorem chapter04_totally_ramified_uniformizer_minpoly_is_eisenstein
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [IsLocalRing A]
    [IsLocalRing B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal]
    [P.LiesOver (IsLocalRing.maximalIdeal A)] (πA : A) (x : B)
    (hπA : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.isUniformizerElement (R := A) πA)
    (hπB : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.isUniformizerElement (R := B) x)
    (hP : P = IsLocalRing.maximalIdeal B)
    (htotal : P.ramificationIdx A = Module.finrank K L ∧
      P.inertiaDeg A = 1)
    (hgen : Algebra.adjoin K ({algebraMap B L x} : Set L) = ⊤) :
    ∃ f : A[X], f.Monic ∧
      Polynomial.map (algebraMap A K) f =
        minpoly K (algebraMap B L x) ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt πA f := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
