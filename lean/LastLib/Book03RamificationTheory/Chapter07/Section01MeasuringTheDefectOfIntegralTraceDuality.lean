import LastLib.Book03RamificationTheory.Chapter07.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.1. Measuring the defect of integral trace duality -/

theorem chapter07_codifferent_coe_eq_set
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] :
    (Submodule.traceDual A K (1 : Submodule B L) : Set L) =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04TraceDual A B K L := by
  ext x
  constructor
  · intro hx y
    have hx' := (Submodule.mem_traceDual.mp hx)
      (algebraMap B L y) (by simp [Submodule.one_eq_range])
    rcases hx' with ⟨a, ha⟩
    exact ⟨a, by simpa [Algebra.traceForm_apply] using ha⟩
  · intro hx
    apply Submodule.mem_traceDual.mpr
    intro b hb
    rcases (show ∃ y : B, algebraMap B L y = b by
      simpa [Submodule.one_eq_range] using hb) with ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hx y
    exact ⟨a, by simpa [Algebra.traceForm_apply] using ha⟩

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
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04TraceDual A B K L := by
  calc
    (chapter07CodifferentFractionalIdeal A B K L : Set L) =
        (Submodule.traceDual A K (1 : Submodule B L) : Set L) := by
      have hcoe :
          (chapter07CodifferentFractionalIdeal A B K L : Submodule B L) =
            Submodule.traceDual A K (1 : Submodule B L) := by
        dsimp [chapter07CodifferentFractionalIdeal]
        simpa only using
          (FractionalIdeal.coe_dual_one (A := A) (K := K) (B := B) (L := L))
      ext z
      change z ∈ (chapter07CodifferentFractionalIdeal A B K L : Submodule B L) ↔
        z ∈ Submodule.traceDual A K (1 : Submodule B L)
      rw [hcoe]
    _ = LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04TraceDual
        A B K L := chapter07_codifferent_coe_eq_set A B K L

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
    x ∈ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04TraceDual A B K L ↔
      ∃! φ : B →ₗ[A] A, chapter07TraceDualRepresentation A B K L x φ := by
  constructor
  · intro hx
    change ∀ y : B, ∃ a : A,
      algebraMap A K a = Algebra.trace K L (x * algebraMap B L y) at hx
    choose f hf using hx
    let φ : B →ₗ[A] A :=
      { toFun := f
        map_add' := by
          intro y z
          apply IsFractionRing.injective A K
          calc
            algebraMap A K (f (y + z)) =
                Algebra.trace K L (x * algebraMap B L (y + z)) := hf (y + z)
            _ = Algebra.trace K L (x * algebraMap B L y) +
                Algebra.trace K L (x * algebraMap B L z) := by
              simp [mul_add]
            _ = algebraMap A K (f y + f z) := by
              rw [map_add, hf y, hf z]
        map_smul' := by
          intro a y
          apply IsFractionRing.injective A K
          calc
            algebraMap A K (f (a • y)) =
                Algebra.trace K L (x * algebraMap B L (a • y)) := hf (a • y)
            _ = algebraMap A K a *
                Algebra.trace K L (x * algebraMap B L y) := by
              have hmap :
                  algebraMap B L (a • y) =
                    (algebraMap A K a) • algebraMap B L y := by
                rw [Algebra.smul_def (R := A) (A := B), map_mul,
                  ← IsScalarTower.algebraMap_apply A B L,
                  IsScalarTower.algebraMap_apply A K L,
                  Algebra.smul_def (R := K) (A := L)]
              calc
                Algebra.trace K L (x * algebraMap B L (a • y)) =
                    Algebra.trace K L
                      (x * ((algebraMap A K a) •
                        algebraMap B L y)) := by rw [hmap]
                _ = Algebra.trace K L
                      ((algebraMap A K a) •
                        (x * algebraMap B L y)) := by
                  congr 1
                  rw [Algebra.smul_def (R := K) (A := L),
                    Algebra.smul_def (R := K) (A := L)]
                  ac_rfl
                _ = (algebraMap A K a) •
                      Algebra.trace K L (x * algebraMap B L y) := by
                  rw [LinearMap.map_smul_of_tower]
                _ = algebraMap A K a *
                      Algebra.trace K L (x * algebraMap B L y) := by
                  simp
            _ = algebraMap A K (a • f y) := by
              rw [← hf y]
              simp
      }
    refine ⟨φ, ?_, ?_⟩
    · intro y
      exact hf y
    · intro ψ hψ
      ext y
      change ψ y = f y
      apply IsFractionRing.injective A K
      rw [hψ y, hf y]
  · rintro ⟨φ, hφ, _⟩
    change ∀ y : B, ∃ a : A,
      algebraMap A K a = Algebra.trace K L (x * algebraMap B L y)
    intro y
    exact ⟨φ y, hφ y⟩

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
  ext y
  simp [chapter07TraceHomAction]

theorem chapter07_trace_hom_action_mul
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (b c : B) (φ : B →ₗ[A] A) :
    chapter07TraceHomAction A B (b * c) φ =
      chapter07TraceHomAction A B b (chapter07TraceHomAction A B c φ) := by
  ext y
  simp [chapter07TraceHomAction, mul_left_comm]

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
  simpa [chapter07CodifferentFractionalIdeal] using
    (FractionalIdeal.one_le_dual_one A K (L := L) (B := B))

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
  change (differentIdeal A B : FractionalIdeal B⁰ L) =
    (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹
  exact coeIdeal_differentIdeal A K L B

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
  have hDfrac :
      (chapter07DifferentIdeal A B : FractionalIdeal B⁰ L) ≠ 0 := by
    rw [chapter07_different_fractional_coe_eq A B K L]
    exact inv_ne_zero (FractionalIdeal.dual_ne_zero A K one_ne_zero)
  have hD : chapter07DifferentIdeal A B ≠ ⊥ :=
    (FractionalIdeal.coeIdeal_ne_zero).mp hDfrac
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨d, hd⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hD hϖ
  have hd' : chapter07DifferentIdeal A B =
      (IsLocalRing.maximalIdeal B) ^ d := by
    rw [hd, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  refine ⟨d, hd', ?_⟩
  intro n hn
  have hco := congrArg Order.coheight hn
  rw [hd', IsDiscreteValuationRing.coheight_pow_maximalIdeal,
    IsDiscreteValuationRing.coheight_pow_maximalIdeal] at hco
  exact_mod_cast hco.symm

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
