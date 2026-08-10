import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section01FromOneLocalRingToSeveral

universe u v

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

noncomputable section

open Ideal IsLocalRing
open Polynomial
open scoped BigOperators TensorProduct WithZero Polynomial nonZeroDivisors

/-! # Chapter 11: several places above one place

This file is a statement-only formalization of sections 11.1--11.9 of Book 1.
The declarations are intentionally local to this namespace because the chapters
are generated independently.
-/

/-! # Book 1, Chapter 11, Section 11.2: Finiteness Hypotheses
-/

/-! ## 11.2. Finiteness and the generic fiber -/

/-- A uniformizer for a local ideal. -/
def chapter11IsUniformizer (A : Type*) [CommRing A] (m : Ideal A) (π : A) : Prop :=
  m = Ideal.span {π}

/-- The generic fiber of a finite `A`-algebra. -/
abbrev chapter11GenericFiber (A B K : Type*) [CommRing A] [CommRing B] [Field K]
    [Algebra A B] [Algebra A K] : Type _ :=
  B ⊗[A] K

/-- The expected identification of the generic fiber with the given field extension. -/
def chapter11GenericFiberIdentification
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] : Prop :=
  Nonempty (chapter11GenericFiber A B K ≃+* L)

/-- Finite torsion-free modules over a PID are free. -/
theorem chapter11_finite_torsion_free_over_pid_is_free
    (A M : Type*) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsTorsionFree A M] :
    Module.Free A M := by
  exact Module.free_of_finite_type_torsion_free'

/-- The rank of the normalization agrees with the degree of the generic field extension. -/
theorem chapter11_normalization_rank_eq_field_degree
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L]
    [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsFractionRing B L] [Module.Free A B] [Module.Finite A B] :
    Cardinal.toNat (Module.rank A B) = Module.finrank K L := by
  have hr := congrArg Cardinal.toNat
    (Module.finrank_eq_rank (R := A) (M := B))
  calc
    Cardinal.toNat (Module.rank A B) = Module.finrank A B := by
      simpa only [Cardinal.toNat_natCast] using hr.symm
    _ = Module.finrank K L := (IsFractionRing.finrank_eq A K B L).symm

/-- The generic fiber is the field `L` after inverting the nonzero elements of `A`. -/
theorem chapter11_generic_fiber_is_the_field_extension
    (A B K L : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L] [FiniteDimensional K L]
    (hfinite : Module.Finite A B) :
    chapter11GenericFiberIdentification A B K L := by
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰)
      (B ⊗[A] K) := IsLocalization.tensor K A⁰
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  exact ⟨(IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B A⁰)
    (B ⊗[A] K) L).toRingEquiv⟩

/-- The generic-fiber identification can be kept as a scalar-compatible ring
equivalence over `K`, recording the canonical compatibility omitted by the
weaker ring-equivalence wrapper above. -/
def chapter11GenericFiberKIdentification
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L] : Prop :=
  ∃ e : chapter11GenericFiber A B K ≃+* L,
    ∀ k : K, e (Algebra.TensorProduct.includeRight k) = algebraMap K L k

theorem chapter11_generic_fiber_is_the_field_extension_as_K_algebra
    (A B K L : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L] [FiniteDimensional K L]
    (hfinite : Module.Finite A B) :
    chapter11GenericFiberKIdentification A B K L := by
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰)
      (B ⊗[A] K) := IsLocalization.tensor K A⁰
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  let eAlg : (B ⊗[A] K) ≃ₐ[B] L :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B A⁰) (B ⊗[A] K) L
  let e : (B ⊗[A] K) ≃+* L := eAlg.toRingEquiv
  refine ⟨e, ?_⟩
  have heq :
      e.toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom :
        K →+* (B ⊗[A] K)) = algebraMap K L := by
    apply IsLocalization.ringHom_ext A⁰
    apply RingHom.ext
    intro a
    change eAlg ((Algebra.TensorProduct.includeRight.toRingHom.comp
      (algebraMap A K)) a) =
      algebraMap K L (algebraMap A K a)
    rw [← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]
    change eAlg (algebraMap A (B ⊗[A] K) a) =
      algebraMap K L (algebraMap A K a)
    rw [IsScalarTower.algebraMap_apply A B (B ⊗[A] K) a]
    rw [eAlg.commutes]
    rw [← IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply A K L]
  intro k
  exact RingHom.congr_fun heq k

/-- A DVR clears denominators by a power of a uniformizer. -/
def chapter11DenominatorCleared (A B L : Type*) [CommRing A] [CommRing B] [CommRing L]
    [Algebra A L] [Algebra B L] (π : A) (x : L) : Prop :=
  ∃ n : ℕ, ∃ b : B, (algebraMap A L π) ^ n * x = algebraMap B L b

/-- Every element of the fraction field of the normalization is denominator-cleared. -/
theorem chapter11_denominators_are_powers_of_a_uniformizer
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing B L] [IsIntegralClosure B A L]
    [FiniteDimensional K L] (m : Ideal A) (π : A)
    (hm : m = IsLocalRing.maximalIdeal A) (hm0 : m ≠ ⊥)
    (hπ : chapter11IsUniformizer A m π) (hfinite : Module.Finite A B) (x : L) :
    chapter11DenominatorCleared A B L π x := by
  have hπ0 : π ≠ 0 := by
    intro hzero
    apply hm0
    rw [hπ, hzero, Ideal.span_singleton_zero]
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A) := by
    rw [← hπ, hm]
  have hπirr : Irreducible π := by
    exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ0 hmax
  letI : IsDomain B := (IsIntegralClosure.algebraMap_injective B A L).isDomain
  letI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B x
  obtain ⟨d, hd, c, hc⟩ :=
    (Algebra.IsIntegral.isIntegral (R := A) b).isAlgebraic.exists_nonzero_dvd
      hb
  obtain ⟨n, u, hud⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπirr
  refine ⟨n, ?_⟩
  refine ⟨algebraMap A B (↑(u⁻¹) : A) * c * a, ?_⟩
  have hpow : π ^ n = (↑(u⁻¹) : A) * d := by
    rw [hud]
    simp [mul_assoc]
  have hcL : algebraMap A L d =
      algebraMap B L b * algebraMap B L c := by
    rw [IsScalarTower.algebraMap_apply A B L d, ← map_mul]
    exact congrArg (algebraMap B L) hc
  have hcleared :
      algebraMap A L d * (algebraMap B L a / algebraMap B L b) =
        algebraMap B L (c * a) := by
    rw [hcL]
    have hbL : algebraMap B L b ≠ 0 :=
      map_ne_zero_of_mem_nonZeroDivisors (algebraMap B L)
        (IsIntegralClosure.algebraMap_injective B A L) hb
    field_simp [hbL]
    rw [map_mul]
  calc
    algebraMap A L π ^ n * (algebraMap B L a / algebraMap B L b) =
        algebraMap A L ((↑(u⁻¹) : A) * d) *
          (algebraMap B L a / algebraMap B L b) := by
      rw [← map_pow, hpow, map_mul]
    _ = algebraMap A L (↑(u⁻¹) : A) * algebraMap B L (c * a) := by
      rw [map_mul]
      calc
        algebraMap A L (↑(u⁻¹) : A) * algebraMap A L d *
            (algebraMap B L a / algebraMap B L b) =
            algebraMap A L (↑(u⁻¹) : A) *
              (algebraMap A L d * (algebraMap B L a / algebraMap B L b) : L) := by
                ring
        _ = _ := by rw [hcleared]
    _ = algebraMap B L (algebraMap A B (↑(u⁻¹) : A) * c * a) := by
      rw [IsScalarTower.algebraMap_apply A B L, ← map_mul]
      simp [mul_assoc]

/-- A finite separable extension of the fraction field of a DVR has finite
integral closure, via the trace-dual boundedness argument. -/
theorem chapter11_separable_extension_gives_finite_normalization
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    chapter11NormalizationFinite A L := by
  change Module.Finite A (integralClosure A L)
  exact IsIntegralClosure.finite A K L (integralClosure A L)

/-- Completeness or the Japanese hypothesis is the standard source of normalization finiteness. -/
theorem chapter11_complete_or_japanese_gives_finite_normalization
    (A K L : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hsource : chapter11IsCompleteDVR A ∨ chapter11IsJapanese A) :
    chapter11NormalizationFinite A L := by
  rcases hsource with hcomplete | hjapanese
  · letI : Chapter11CompleteDVR A := hcomplete
    change Module.Finite A (integralClosure A L)
    exact Chapter11CompleteDVR.normalization_finite (A := A) K L
  · letI : Chapter11Japanese A := hjapanese
    change Module.Finite A (integralClosure A L)
    exact Chapter11Japanese.finite_integral_closure (R := A) K L

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
