import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section01LinearAlgebraTurnedIntoArithmetic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

open scoped BigOperators Polynomial

/-! ## 4.2. Characteristic polynomials and integral restriction -/

/-
For a finite free `A`-module `B`, Mathlib's `LinearMap.charpoly` already has
type `A[X]`; the following theorem records the arithmetic consequence for the
field trace and norm after passing to fraction fields.
-/
theorem chapter04_integral_trace_and_norm
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (x : B) :
    ∃ a b : A,
      algebraMap A K a = Algebra.trace K L (algebraMap B L x) ∧
        algebraMap A K b = Algebra.norm K (algebraMap B L x) := by
  rcases LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_integral_trace_and_norm_stay_integral
      A B K L x with
    ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a, b, ha, hb⟩

/- The characteristic polynomial of multiplication descends from the finite
free integral basis to the fraction-field extension (§4.2). -/
theorem chapter04_integral_characteristic_polynomial
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (x : B) :
    Polynomial.map (algebraMap A K)
        (LinearMap.charpoly (Algebra.lmul A B x)) =
      LinearMap.charpoly (Algebra.lmul K L (algebraMap B L x)) := by
  classical
  letI : IsIntegralClosure B A L := IsIntegralClosure.of_isIntegrallyClosed B A L
  let b := Module.Free.chooseBasis A B
  let bK := b.localizationLocalization K (nonZeroDivisors A) L
  calc
    Polynomial.map (algebraMap A K)
        (LinearMap.charpoly (Algebra.lmul A B x)) =
        Polynomial.map (algebraMap A K)
          (Matrix.charpoly (Algebra.leftMulMatrix b x)) := by
      rw [← LinearMap.charpoly_toMatrix (Algebra.lmul A B x) b,
        Algebra.leftMulMatrix_apply]
    _ = Matrix.charpoly
        ((algebraMap A K).mapMatrix (Algebra.leftMulMatrix b x)) := by
      rw [← Matrix.charpoly_map]
      congr 1
    _ = Matrix.charpoly (Algebra.leftMulMatrix bK (algebraMap B L x)) := by
      rw [Algebra.map_leftMulMatrix_localization (R := A) (Rₘ := K) (Sₘ := L)
        (nonZeroDivisors A) b x]
    _ = LinearMap.charpoly (Algebra.lmul K L (algebraMap B L x)) := by
      rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]

/- The norm of an integral unit is a unit of the base ring (§4.2). -/
theorem chapter04_norm_of_integral_unit_is_base_unit
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (u : Bˣ) :
    ∃ a : Aˣ,
      algebraMap A K (a : A) = Algebra.norm K (algebraMap B L (u : B)) := by
  refine ⟨Units.map (Algebra.intNorm A B) u, ?_⟩
  simpa using (Algebra.algebraMap_intNorm (A := A) (B := B)
    (K := K) (L := L) (u : B))

/-
Trace need not preserve units: a separable quadratic extension in
characteristic different from two has a trace-zero field unit (§4.2).
-/
theorem chapter04_quadratic_trace_zero_unit
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hdegree : Module.finrank K L = 2) (hchar : (2 : K) ≠ 0) :
    ∃ u : Lˣ,
      Algebra.trace K L (u : L) = 0 ∧
        ¬IsUnit (Algebra.trace K L (u : L)) := by
  have hker : LinearMap.ker (Algebra.trace K L) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_self, hdegree]
    norm_num
  rcases (Submodule.ne_bot_iff _).mp hker with ⟨z, hz, hz0⟩
  refine ⟨Units.mk0 z hz0, ?_, ?_⟩
  · exact (LinearMap.mem_ker.mp hz)
  · simpa [LinearMap.mem_ker.mp hz]

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
