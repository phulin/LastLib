import LastLib.Book03RamificationTheory.Chapter07.Section01MeasuringTheDefectOfIntegralTraceDuality

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.2. Unramifiedness and the different -/

/-- The numerical and residue-field profile of an unramified extension. -/
def chapter07UnramifiedProfile
    (e : ℕ) (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] : Prop :=
  e = 1 ∧ Algebra.IsSeparable k l

@[simp] theorem chapter07UnramifiedProfile_iff
    (e : ℕ) (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] :
    chapter07UnramifiedProfile e k l ↔ e = 1 ∧ Algebra.IsSeparable k l :=
  Iff.rfl

/- Perfectness of the integral trace pairing is stated as a lattice
   isomorphism, rather than as an informal determinant condition. -/
def chapter07IntegralTracePairingPerfect
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Prop :=
  ∃ e : B ≃ₗ[A] (B →ₗ[A] A),
    ∀ x y : B,
      algebraMap A K ((e x) y) =
        Algebra.trace K L (algebraMap B L x * algebraMap B L y)

theorem chapter07_integral_trace_pairing_perfect_iff
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] :
    chapter07IntegralTracePairingPerfect A B K L ↔
      ∃ e : B ≃ₗ[A] (B →ₗ[A] A),
        ∀ x y : B,
          algebraMap A K ((e x) y) =
            Algebra.trace K L (algebraMap B L x * algebraMap B L y) := Iff.rfl

/- The unramified lift of a separating residue generator gives a perfect
   integral trace pairing and the unit different. -/
theorem chapter07_unramified_trace_pairing_perfect
    (A B K L k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [Algebra k l] [FiniteDimensional k l]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (e : ℕ) (hunram : chapter07UnramifiedProfile e k l)
    (hpower :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (hdegree : Module.finrank K L = Module.finrank k l)
    (hresidue_model : chapter07CompatibleResidueModel A B k l) :
    chapter07IntegralTracePairingPerfect A B K L ∧
      chapter07DifferentIdeal A B = ⊤ ∧ e = 1 := by
  sorry

/- A trace matrix records the determinant criterion used in the forward
   direction. -/
def chapter07IntegralTraceMatrix
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} (tr : B →ₗ[A] A) (b : ι → B) : Matrix ι ι A :=
  fun i j => tr (b i * b j)

theorem chapter07_perfect_trace_pairing_has_unit_trace_determinant
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tr : B →ₗ[A] A)
    (hperfect : chapter07IntegralTracePairingPerfect A B K L)
    (hbasis : Module.Basis ι A B)
    (htrace : ∀ x y : B,
      algebraMap A K (tr (x * y)) =
        Algebra.trace K L (algebraMap B L x * algebraMap B L y)) :
    IsUnit (Matrix.det
      (chapter07IntegralTraceMatrix A B tr (fun i => hbasis i))) := by
  sorry

/- The trace pairing on a finite algebra over a field is represented by the
   trace of its multiplication operators. -/
def chapter07FiniteAlgebraTracePairing
    (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    [FiniteDimensional k R] (x y : R) : k :=
  LinearMap.trace k R (Algebra.lmul k R (x * y))

def chapter07TracePairingNondegenerate
    (R k : Type*) [Field k] [CommRing R] [Algebra k R]
    (pair : R → R → k) : Prop :=
  ∀ x : R, (∀ y : R, pair x y = 0) → x = 0

theorem chapter07_nilpotent_is_in_trace_radical
    (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    [FiniteDimensional k R] (z : R) (hz : IsNilpotent z) :
    ∀ y : R, chapter07FiniteAlgebraTracePairing k R z y = 0 := by
  sorry

theorem chapter07_reduced_finite_local_algebra_is_a_field
    (k R : Type*) [Field k] [CommRing R] [Algebra k R]
    [FiniteDimensional k R] [IsLocalRing R] [IsReduced R] :
    IsField R := by
  sorry

theorem chapter07_field_trace_pairing_nondegenerate_iff_separable
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] :
    chapter07TracePairingNondegenerate l k
        (chapter07FiniteAlgebraTracePairing k l) ↔
      Algebra.IsSeparable k l := by
  sorry

/- If the different is the unit ideal, the reduced quotient argument forces
   both value-group invariants and residue separability. -/
theorem chapter07_zero_different_implies_unramified
    (A B K L k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [Algebra k l] [FiniteDimensional k l] [IsScalarTower A K L]
    [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (e : ℕ) (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hpower :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (hzero : chapter07DifferentIdeal A B = ⊤)
    (hquotient_reduced : chapter07DifferentIdeal A B = ⊤ →
      IsReduced (B ⧸ Ideal.map (algebraMap A B) mA))
    (hresidue : Nonempty ((B ⧸ mB) ≃+* l))
    (htrace_nondegenerate : chapter07DifferentIdeal A B = ⊤ →
      chapter07TracePairingNondegenerate l k
        (chapter07FiniteAlgebraTracePairing k l)) :
    chapter07UnramifiedProfile e k l := by
  sorry

theorem chapter07_different_zero_iff_unramified
    (A B K L k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [Algebra k l] [FiniteDimensional k l] [IsScalarTower A K L]
    [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (e : ℕ) (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hpower :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (hdegree : Module.finrank K L = Module.finrank k l)
    (hresidue_model : chapter07CompatibleResidueModel A B k l)
    (hquotient_reduced : chapter07DifferentIdeal A B = ⊤ →
      IsReduced (B ⧸ Ideal.map (algebraMap A B) mA))
    (htrace_nondegenerate : chapter07DifferentIdeal A B = ⊤ →
      chapter07TracePairingNondegenerate l k
        (chapter07FiniteAlgebraTracePairing k l)) :
    chapter07DifferentIdeal A B = ⊤ ↔
      chapter07UnramifiedProfile e k l := by
  sorry

/- The value group may be unchanged while inseparable residue growth still
   forces a nontrivial different. -/
theorem chapter07_e_one_inseparable_residue_forces_nontrivial_different
    (A B K L k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [Algebra k l] [FiniteDimensional k l] [IsScalarTower A K L]
    [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hpower :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (1 : ℤ))
    (hdegree : Module.finrank K L = Module.finrank k l)
    (hresidue_model : chapter07CompatibleResidueModel A B k l)
    (hquotient_reduced : chapter07DifferentIdeal A B = ⊤ →
      IsReduced (B ⧸ Ideal.map (algebraMap A B) mA))
    (htrace_nondegenerate : chapter07DifferentIdeal A B = ⊤ →
      chapter07TracePairingNondegenerate l k
        (chapter07FiniteAlgebraTracePairing k l))
    (hinsep : ¬Algebra.IsSeparable k l) :
    chapter07DifferentIdeal A B ≠ ⊤ := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter07
