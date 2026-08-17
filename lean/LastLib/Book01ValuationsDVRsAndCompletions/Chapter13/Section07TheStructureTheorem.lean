import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section06LiftingAndUniquenessOfCohenRings
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.RegularLocalRing.Defs

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Ideal IsLocalRing

noncomputable section

/-! # Book 1, Chapter 13, Section 13.7: The structure theorem -/

universe u

/-- The package of completeness, regularity, domain structure, and dimension used for
the regular power-series models. -/
def Chapter13CompleteRegularLocalDomain
    (R : Type u) [CommRing R] (I : Ideal R) (d : ℕ) : Prop :=
  IsAdicComplete I R ∧ IsRegularLocalRing R ∧ IsDomain R ∧ ringKrullDim R = d

/-- A family generates the maximal ideal, as for a system of local coordinates. -/
def Chapter13MaximalIdealGenerators
    {A : Type u} [CommRing A] [IsLocalRing A]
    (x : Fin n → A) : Prop :=
  Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A

/-- The mixed-characteristic unramified condition `p ∉ 𝔪²`. -/
def Chapter13UnramifiedAtPrime
    (A : Type u) [CommRing A] [IsLocalRing A] (p : ℕ) : Prop :=
  (p : A) ∉ (IsLocalRing.maximalIdeal A) ^ 2

/-- The finite-length parameter condition used for the finite-coordinate theorem. -/
def Chapter13FiniteLengthParameterFamily
    {A : Type u} [CommRing A]
    (I : Ideal A) : Prop :=
  IsFiniteLength A (A ⧸ I)

/-- Finiteness of the target as a module through a specified power-series map. -/
def Chapter13FinitePowerSeriesModule
    {P A : Type u} [CommRing P] [CommRing A]
    (F : P →+* A) : Prop :=
  letI : Module P A := Module.compHom A F
  Module.Finite P A

/-! ### The regular power-series models -/

theorem chapter13_power_series_over_field_is_regular
    (k : Type u) [Field k] (n : ℕ) :
    Chapter13CompleteRegularLocalDomain
      (MvPowerSeries (Fin n) k) (Chapter13PowerSeriesMaximalIdeal k n) n := by
  sorry

theorem chapter13_power_series_over_cohen_ring_is_regular
    (C k : Type u) [CommRing C] [IsLocalRing C] [Field k] (p n : ℕ)
    (hC : Chapter13IsCohenRing C k p) :
    Chapter13CompleteRegularLocalDomain
      (MvPowerSeries (Fin n) C) (Chapter13PowerSeriesMaximalIdeal C n) (n + 1) := by
  sorry

/-! ### Cohen's presentation theorem -/

theorem chapter13_cohen_structure_equal_characteristic
    {A k : Type u} [CommRing A] [IsLocalRing A] [Field k]
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (σ : k →+* A) (hσ : Chapter13LocalHom σ)
    (hres : Function.Bijective ((Chapter13ResidueMap A).comp σ))
    (n : ℕ) (x : Fin n → A)
    (hx : ∀ i : Fin n, x i ∈ IsLocalRing.maximalIdeal A)
    (hgen : Chapter13MaximalIdealGenerators x) :
    ∃ F : MvPowerSeries (Fin n) k →+* A,
      Chapter13PowerSeriesEvaluationData n σ x F ∧ Function.Surjective F := by
  have hk : Chapter13CompleteNoetherianLocalRing k := by
    constructor
    · infer_instance
    · simpa [IsLocalRing.maximalIdeal_eq_bot] using
        (inferInstance : IsAdicComplete (⊥ : Ideal k) k)
  obtain ⟨F, hF, _⟩ := chapter13_power_series_evaluation_exists_unique
    hk hA n σ hσ x hx
  refine ⟨F, hF, (chapter13_power_series_evaluation_surjective_iff
    hk hA n σ x F hF).2 ?_⟩
  intro a
  obtain ⟨r, hr⟩ := hres.2 (Chapter13ResidueMap A a)
  have hm : a - σ r ∈ IsLocalRing.maximalIdeal A := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change Chapter13ResidueMap A (a - σ r) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hr.symm
  rw [← hgen] at hm
  refine ⟨r, a - σ r, Ideal.mem_sup_right hm, ?_⟩
  simp

theorem chapter13_cohen_structure_mixed_characteristic
    {A C k : Type u} [CommRing A] [IsLocalRing A]
    [CommRing C] [IsLocalRing C] [Field k] (p n : ℕ)
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (_hmixed : Chapter13MixedCharacteristic A p)
    (hC : Chapter13IsCohenRing C k p)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* k)
    (u : C →+* A) (hu : IsLocalHom u)
    (hres : Chapter13ResidueMapCompatibility eC eA (RingHom.id k) u)
    (x : Fin n → A)
    (hx : ∀ i : Fin n, x i ∈ IsLocalRing.maximalIdeal A)
    (hgen : Chapter13MaximalIdealGenerators x) :
    ∃ F : MvPowerSeries (Fin n) C →+* A,
      Chapter13PowerSeriesEvaluationData n u x F ∧ Function.Surjective F := by
  obtain ⟨hdomC, hDvrC⟩ := hC.1.1
  have hCnoeth : IsNoetherianRing C :=
    ⟨fun I => hDvrC.toIsPrincipalIdealRing.principal I |>.fg⟩
  have hCcomplete : Chapter13CompleteNoetherianLocalRing C :=
    ⟨hCnoeth, hC.2⟩
  have hsurj : Function.Surjective
      ((Chapter13ResidueMap A).comp u) := by
    intro y
    let q : Chapter13ResidueRing C := eC.symm (eA y)
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨c, eA.injective ?_⟩
    calc
      eA (Chapter13ResidueMap A (u c)) = eC (Chapter13ResidueMap C c) := by
        simpa using hres c
      _ = eC q := by
        simpa [Chapter13ResidueMap] using congrArg eC hc
      _ = eA y := by simp [q]
  obtain ⟨F, hF, _⟩ := chapter13_power_series_evaluation_exists_unique
    hCcomplete hA n u hu x hx
  refine ⟨F, hF, (chapter13_power_series_evaluation_surjective_iff
    hCcomplete hA n u x F hF).2 ?_⟩
  intro a
  obtain ⟨r, hr⟩ := hsurj (Chapter13ResidueMap A a)
  have hm : a - u r ∈ IsLocalRing.maximalIdeal A := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change Chapter13ResidueMap A (a - u r) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hr.symm
  rw [← hgen] at hm
  refine ⟨r, a - u r, Ideal.mem_sup_right hm, ?_⟩
  simp

/-! ### Immediate quotient and regularity consequences -/

theorem chapter13_complete_local_quotient_of_regular_model
    {A Q : Type u} [CommRing A] [IsLocalRing A] [CommRing Q]
    (_hA : Chapter13CompleteNoetherianLocalRing A)
    (I : Ideal Q) (d : ℕ)
    (_hQ : Chapter13CompleteRegularLocalDomain Q I d)
    (F : Q →+* A) (hF : Function.Surjective F) :
    Nonempty ((Q ⧸ RingHom.ker F) ≃+* A) := by
  exact ⟨RingHom.quotientKerEquivOfSurjective hF⟩

theorem chapter13_equal_characteristic_complete_regular_is_power_series
    {A k : Type u} [CommRing A] [IsLocalRing A] [Field k] (d : ℕ)
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (hregular : IsRegularLocalRing A)
    (hdim : ringKrullDim A = d)
    (hcontains : Chapter13ContainsField A)
    (σ : k →+* A) (hσ : IsLocalHom σ)
    (hres : Function.Bijective ((Chapter13ResidueMap A).comp σ)) :
    Nonempty (MvPowerSeries (Fin d) k ≃+* A) := by
  sorry

theorem chapter13_mixed_characteristic_complete_regular_quotient
    {A C k : Type u} [CommRing A] [IsLocalRing A]
    [CommRing C] [IsLocalRing C] [Field k] (p d : ℕ)
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (hregular : IsRegularLocalRing A)
    (hdim : ringKrullDim A = d)
    (hmixed : Chapter13MixedCharacteristic A p)
    (hC : Chapter13IsCohenRing C k p)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* k)
    (u : C →+* A) (hu : IsLocalHom u)
    (hres : Chapter13ResidueMapCompatibility eC eA (RingHom.id k) u) :
    ∃ F : MvPowerSeries (Fin d) C →+* A, Function.Surjective F := by
  sorry

theorem chapter13_mixed_characteristic_unramified_is_power_series
    {A C k : Type u} [CommRing A] [IsLocalRing A]
    [CommRing C] [IsLocalRing C] [Field k] (p d : ℕ)
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (hregular : IsRegularLocalRing A)
    (hdim : ringKrullDim A = d)
    (hdimpos : 1 ≤ d)
    (hmixed : Chapter13MixedCharacteristic A p)
    (hunramified : Chapter13UnramifiedAtPrime A p)
    (hC : Chapter13IsCohenRing C k p)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* k)
    (u : C →+* A) (hu : IsLocalHom u)
    (hres : Chapter13ResidueMapCompatibility eC eA (RingHom.id k) u) :
    Nonempty (MvPowerSeries (Fin (d - 1)) C ≃+* A) := by
  sorry

/-! ### Finite extensions over a power-series subring -/

theorem chapter13_finite_over_equal_power_series
    {A k : Type u} [CommRing A] [IsLocalRing A] [Field k]
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (σ : k →+* A) (hσ : IsLocalHom σ)
    (hres : Function.Bijective ((Chapter13ResidueMap A).comp σ))
    (s : ℕ) (x : Fin s → A)
    (hx : ∀ i : Fin s, x i ∈ IsLocalRing.maximalIdeal A)
    (hfinite : Chapter13FiniteLengthParameterFamily
      (Ideal.span (Set.range x))) :
    ∃ F : MvPowerSeries (Fin s) k →+* A,
      Chapter13PowerSeriesEvaluationData s σ x F ∧
        Chapter13FinitePowerSeriesModule F := by
  sorry

theorem chapter13_finite_over_mixed_power_series
    {A C k : Type u} [CommRing A] [IsLocalRing A]
    [CommRing C] [IsLocalRing C] [Field k] (p : ℕ)
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (hmixed : Chapter13MixedCharacteristic A p)
    (hC : Chapter13IsCohenRing C k p)
    (eC : Chapter13ResidueRing C ≃+* k)
    (eA : Chapter13ResidueRing A ≃+* k)
    (u : C →+* A) (hu : IsLocalHom u)
    (hres : Chapter13ResidueMapCompatibility eC eA (RingHom.id k) u)
    (s : ℕ) (x : Fin s → A)
    (hx : ∀ i : Fin s, x i ∈ IsLocalRing.maximalIdeal A)
    (hfinite : Chapter13FiniteLengthParameterFamily
      (Ideal.span ({(p : A)} ∪ Set.range x))) :
    ∃ F : MvPowerSeries (Fin s) C →+* A,
      Chapter13PowerSeriesEvaluationData s u x F ∧
        Chapter13FinitePowerSeriesModule F := by
  sorry

theorem chapter13_finite_power_series_map_injective
    {A Q : Type u} [CommRing A] [IsLocalRing A] [CommRing Q]
    (I : Ideal Q) (d : ℕ)
    (hQ : Chapter13CompleteRegularLocalDomain Q I d)
    (F : Q →+* A)
    (hfinite : Chapter13FinitePowerSeriesModule F)
    (hdomain : IsDomain A)
    (hdim : ringKrullDim Q = ringKrullDim A) :
    Function.Injective F := by
  sorry

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
