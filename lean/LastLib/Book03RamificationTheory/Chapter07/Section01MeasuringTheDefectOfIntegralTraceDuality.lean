import LastLib.Book03RamificationTheory.Chapter07.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.1. Measuring the defect of integral trace duality -/

/-- The trace pairing on the field extension. -/
def chapter07TracePairing
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : LinearMap.BilinForm K L :=
  Algebra.traceForm K L

@[simp] theorem chapter07TracePairing_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x y : L) :
    chapter07TracePairing K L x y = Algebra.trace K L (x * y) := by
  rfl

/- The displayed codifferent, kept as a set for the book-facing definition. -/
def chapter07CodifferentSet
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Set L :=
  {x | ∀ y : B, ∃ a : A,
    algebraMap A K a = Algebra.trace K L (x * algebraMap B L y)}

@[simp] theorem chapter07_mem_codifferentSet_iff
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (x : L) :
    x ∈ chapter07CodifferentSet A B K L ↔
      ∀ y : B, ∃ a : A,
        algebraMap A K a = Algebra.trace K L (x * algebraMap B L y) := Iff.rfl

/- The canonical Mathlib submodule underlying the same fractional lattice. -/
def chapter07Codifferent
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] : Submodule B L :=
  Submodule.traceDual A K (1 : Submodule B L)

theorem chapter07_codifferent_coe_eq_set
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] :
    (chapter07Codifferent A B K L : Set L) =
      chapter07CodifferentSet A B K L := by
  sorry

/- The fractional-ideal realization of the codifferent. -/
noncomputable def chapter07CodifferentFractionalIdeal
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] :
    FractionalIdeal B⁰ L :=
  FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)

theorem chapter07_codifferent_fractional_coe_eq
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] :
    (chapter07CodifferentFractionalIdeal A B K L : Set L) =
      chapter07CodifferentSet A B K L := by
  sorry

/- The trace-dual representation makes the Hom description explicit. -/
def chapter07TraceDualRepresentation
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (x : L) (φ : B →ₗ[A] A) : Prop :=
  ∀ y : B,
    algebraMap A K (φ y) = Algebra.trace K L (x * algebraMap B L y)

theorem chapter07_codifferent_iff_unique_trace_dual
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B]
    (x : L) :
    x ∈ chapter07CodifferentSet A B K L ↔
      ∃! φ : B →ₗ[A] A, chapter07TraceDualRepresentation A B K L x φ := by
  sorry

/- The natural action of an integral element on the A-dual is by
   precomposition with multiplication. -/
def chapter07TraceHomAction
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (φ : B →ₗ[A] A) : B →ₗ[A] A :=
  φ.comp (LinearMap.mulLeft A b)

theorem chapter07_trace_hom_action_one
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (φ : B →ₗ[A] A) :
    chapter07TraceHomAction A B 1 φ = φ := by
  sorry

theorem chapter07_trace_hom_action_mul
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (b c : B) (φ : B →ₗ[A] A) :
    chapter07TraceHomAction A B (b * c) φ =
      chapter07TraceHomAction A B b (chapter07TraceHomAction A B c φ) := by
  sorry

/- The different is Mathlib's canonical inverse trace-dual ideal. -/
noncomputable def chapter07DifferentIdeal
    (A B : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    [Algebra A B] [IsDedekindDomain B] [Module.IsTorsionFree A B] : Ideal B :=
  differentIdeal A B

noncomputable def chapter07DifferentFractionalIdeal
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] :
    FractionalIdeal B⁰ L :=
  (chapter07CodifferentFractionalIdeal A B K L)⁻¹

theorem chapter07_different_fractional_is_inverse_codifferent
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] :
    chapter07DifferentFractionalIdeal A B K L =
      (chapter07CodifferentFractionalIdeal A B K L)⁻¹ := by
  rfl

theorem chapter07_integral_ring_le_codifferent
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] :
    (1 : FractionalIdeal B⁰ L) ≤
      chapter07CodifferentFractionalIdeal A B K L := by
  sorry

theorem chapter07_different_fractional_coe_eq
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] :
    (chapter07DifferentIdeal A B : FractionalIdeal B⁰ L) =
      chapter07DifferentFractionalIdeal A B K L := by
  sorry

/- A DVR has a unique exponent for every nonzero ideal, applied to the
   different. -/
theorem chapter07_different_is_unique_maximal_power
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B] :
    ∃! d : ℕ,
      chapter07DifferentIdeal A B =
        (IsLocalRing.maximalIdeal B) ^ d := by
  sorry

noncomputable def chapter07DifferentExponent
    {B : Type*} [CommRing B] (mB D : Ideal B)
    (hD : ∃! d : ℕ, D = mB ^ d) : ℕ :=
  Classical.choose hD

theorem chapter07DifferentExponent_spec
    {B : Type*} [CommRing B] (mB D : Ideal B)
    (hD : ∃! d : ℕ, D = mB ^ d) :
    D = mB ^ chapter07DifferentExponent mB D hD := by
  exact (Classical.choose_spec hD).1

end

end LastLib.Book03RamificationTheory.Chapter07
