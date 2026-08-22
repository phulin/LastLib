import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section06LiftingAndUniquenessOfCohenRings
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.LocalRing.Length

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
  classical
  obtain ⟨hdomC, hDvrC⟩ := hC.1.1
  letI : IsDomain C := hdomC
  letI : IsDiscreteValuationRing C := hDvrC
  let hCnoeth : IsNoetherianRing C :=
    ⟨fun I => hDvrC.toIsPrincipalIdealRing.principal I |>.fg⟩
  letI : IsNoetherianRing C := hCnoeth
  let S := MvPowerSeries (Fin n) C
  have hlocal := chapter13_power_series_complete_local C hC.2 n
  let g : Fin (n + 1) → S :=
    Fin.cases (p : S) (fun i => MvPowerSeries.X i)
  have hrange : Set.range g = {(p : S)} ∪
      Set.range (MvPowerSeries.X : Fin n → S) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
    · intro hz
      rcases hz with rfl | ⟨j, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨Fin.succ j, rfl⟩
  have hgenideal : Chapter13PowerSeriesMaximalIdeal C n =
      Ideal.span (Set.range g) := by
    rw [Chapter13PowerSeriesMaximalIdeal, hrange, Ideal.span_union]
    rw [hC.1.2.1, Ideal.map_span]
    simp
    rfl
  have hpC : (p : C) ≠ 0 := by
    intro hp
    apply IsDiscreteValuationRing.not_isField C
    apply IsLocalRing.isField_iff_maximalIdeal_eq.mpr
    calc
      IsLocalRing.maximalIdeal C = Ideal.span {(p : C)} := hC.1.2.1
      _ = ⊥ := by rw [hp]; exact Ideal.span_singleton_zero
  have hg_inj : Function.Injective g := by
    intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · rfl
      · have hp0 : (p : C) = 0 := by
          have hcoeff := congrArg (MvPowerSeries.constantCoeff : S →+* C) hij
          simpa [g] using hcoeff
        exact (hpC hp0).elim
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · have hp0 : (0 : C) = p := by
          have hcoeff := congrArg (MvPowerSeries.constantCoeff : S →+* C) hij
          simpa [g] using hcoeff
        exact (hpC hp0.symm).elim
      · exact congrArg Fin.succ (MvPowerSeries.X_inj.mp (by simpa [g] using hij))
  have hspan : (IsLocalRing.maximalIdeal S).spanFinrank ≤ n + 1 := by
    rw [hlocal.2.1, hgenideal]
    have hgfin : (Set.range g).Finite := Set.finite_range g
    have hcard : (Set.range g).ncard = n + 1 := by
      rw [Set.ncard_range_of_injective hg_inj]
      simp
    exact (Submodule.spanFinrank_span_le_ncard_of_finite hgfin).trans
      hcard.le
  have hspan' : (↑(IsLocalRing.maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ ↑(n + 1) := by
    exact_mod_cast hspan
  have hdim_lower_all : ∀ m : ℕ,
      (↑(m + 1) : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin m) C) := by
    intro m
    induction m with
    | zero =>
        have hdim0 : ringKrullDim (MvPowerSeries (Fin 0) C) = 1 := by
          rw [ringKrullDim_eq_of_ringEquiv
            (MvPowerSeries.isEmptyEquiv (Fin 0) C).toRingEquiv]
          exact IsDiscreteValuationRing.ringKrullDim_eq_one C
        simpa using hdim0.ge
    | succ n ih =>
        let e := MvPowerSeries.finSuccEquiv C n
        have hpow : ringKrullDim (MvPowerSeries (Fin n) C) + 1 ≤
            ringKrullDim (PowerSeries (MvPowerSeries (Fin n) C)) :=
          ringKrullDim_succ_le_ringKrullDim_powerseries
        calc
          (↑(n.succ + 1) : WithBot ℕ∞) = ↑(n + 1) + 1 := by norm_num
          _ ≤ ringKrullDim (MvPowerSeries (Fin n) C) + 1 := by
            simpa [add_comm] using add_le_add_right ih (1 : WithBot ℕ∞)
          _ ≤ ringKrullDim (MvPowerSeries (Fin (n + 1)) C) := by
            rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
            exact hpow
  have hdim_lower : (↑(n + 1) : WithBot ℕ∞) ≤ ringKrullDim S := hdim_lower_all n
  have hdim_upper : ringKrullDim S ≤ (↑(n + 1) : WithBot ℕ∞) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal S).trans hspan'
  have hdim : ringKrullDim S = n + 1 := le_antisymm hdim_upper hdim_lower
  have hreg : IsRegularLocalRing S :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le S (hspan'.trans hdim_lower)
  have hcomplete : IsAdicComplete (Chapter13PowerSeriesMaximalIdeal C n) S := by
    rw [← hlocal.2.1]
    exact hlocal.1.2
  letI : IsDomain S := NoZeroDivisors.to_isDomain S
  exact ⟨hcomplete, hreg, inferInstance, hdim⟩

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
    · exact ((IsArtinianRing.tfae k k).out 2 1).mp
        (inferInstance : IsArtinianRing k)
    · rw [IsLocalRing.maximalIdeal_eq_bot]
      exact (inferInstance : IsAdicComplete (⊥ : Ideal k) k)
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
  classical
  letI : IsRegularLocalRing A := hregular
  letI : IsNoetherianRing A := hA.1
  have hfg : (IsLocalRing.maximalIdeal A).FG :=
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  obtain ⟨s, hs_card, hs_span⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have hcard : s.card = d := by
    have hcast : (↑s.card : WithBot ℕ∞) = ↑d := by
      calc
        (↑s.card : WithBot ℕ∞) = ↑(IsLocalRing.maximalIdeal A).spanFinrank := by
          rw [hs_card]
        _ = ringKrullDim A := hregular.spanFinrank_maximalIdeal
        _ = ↑d := by exact_mod_cast hdim
    exact_mod_cast hcast
  let e : Fin d ≃ s := (Finset.equivFinOfCardEq hcard).symm
  let x : Fin d → A := fun i => (e i).1
  have hrange : Set.range x = (s : Set A) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro ha
      have he := congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)
      exact ⟨e.symm ⟨a, ha⟩, he⟩
  have hxspan : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A := by
    rw [hrange]
    exact hs_span
  have hx : ∀ i : Fin d, x i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hxspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hgen : Chapter13MaximalIdealGenerators x := hxspan
  obtain ⟨F, hF, hsurj⟩ := chapter13_cohen_structure_equal_characteristic
    hA σ hσ hres d x hx hgen
  let P := MvPowerSeries (Fin d) k
  have hP := chapter13_power_series_over_field_is_regular k d
  have hker : RingHom.ker F = ⊥ := by
    by_contra hker
    obtain ⟨r, hr, hr0⟩ : ∃ r : P, r ∈ RingHom.ker F ∧ r ≠ 0 := by
      by_contra hnone
      apply hker
      apply le_antisymm
      · intro r hr
        by_contra hr0
        exact hnone ⟨r, hr, hr0⟩
      · exact bot_le
    have hdimle := ringKrullDim_succ_le_of_surjective F hsurj
      (mem_nonZeroDivisors_of_ne_zero hr0) hr
    have hcontra : (↑d : WithBot ℕ∞) + 1 ≤ ↑d := by
      simpa [P, hP.2.2.2, hdim] using hdimle
    exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self d)) hcontra
  refine ⟨RingEquiv.ofBijective F ?_⟩
  exact ⟨(RingHom.injective_iff_ker_eq_bot F).mpr hker, hsurj⟩

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
  classical
  letI : IsRegularLocalRing A := hregular
  letI : IsNoetherianRing A := hA.1
  have hfg : (IsLocalRing.maximalIdeal A).FG :=
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  obtain ⟨s, hs_card, hs_span⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  have hcard : s.card = d := by
    have hcast : (↑s.card : WithBot ℕ∞) = ↑d := by
      calc
        (↑s.card : WithBot ℕ∞) = ↑(IsLocalRing.maximalIdeal A).spanFinrank := by
          rw [hs_card]
        _ = ringKrullDim A := hregular.spanFinrank_maximalIdeal
        _ = ↑d := by exact_mod_cast hdim
    exact_mod_cast hcast
  let e : Fin d ≃ s := (Finset.equivFinOfCardEq hcard).symm
  let x : Fin d → A := fun i => (e i).1
  have hrange : Set.range x = (s : Set A) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro ha
      have he := congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)
      exact ⟨e.symm ⟨a, ha⟩, he⟩
  have hxspan : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A := by
    rw [hrange]
    exact hs_span
  have hx : ∀ i : Fin d, x i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hxspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨F, _, hF⟩ := chapter13_cohen_structure_mixed_characteristic
    p d hA hmixed hC eC eA u hu hres x hx hxspan
  exact ⟨F, hF⟩

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
  classical
  letI : IsRegularLocalRing A := hregular
  letI : IsNoetherianRing A := hA.1
  letI : CharP (Chapter13ResidueRing A) p := hmixed.2.1
  have hfg : (IsLocalRing.maximalIdeal A).FG :=
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  letI : Module.Finite A (IsLocalRing.maximalIdeal A) := Module.Finite.of_fg hfg
  letI : Module.Finite A (IsLocalRing.CotangentSpace A) :=
    Module.Finite.quotient A (IsLocalRing.maximalIdeal A •
      (⊤ : Submodule A (IsLocalRing.maximalIdeal A)))
  letI : Module.Finite (Chapter13ResidueRing A) (IsLocalRing.CotangentSpace A) :=
    Module.Finite.of_restrictScalars_finite A (Chapter13ResidueRing A)
      (IsLocalRing.CotangentSpace A)
  have hpmem : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change (p : Chapter13ResidueRing A) = 0
    exact CharP.cast_eq_zero (Chapter13ResidueRing A) p
  let pM : IsLocalRing.maximalIdeal A := ⟨p, hpmem⟩
  let pclass : IsLocalRing.CotangentSpace A :=
    (IsLocalRing.maximalIdeal A).toCotangent pM
  have hpclass : pclass ≠ 0 := by
    intro hpclass
    apply hunramified
    exact ((IsLocalRing.maximalIdeal A).toCotangent_eq_zero pM).mp hpclass
  have hfinrank : Module.finrank (Chapter13ResidueRing A)
      (IsLocalRing.CotangentSpace A) = d := by
    have hspan : (IsLocalRing.maximalIdeal A).spanFinrank =
        Module.finrank (Chapter13ResidueRing A) (IsLocalRing.CotangentSpace A) :=
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace A
    have hspan' : (↑(IsLocalRing.maximalIdeal A).spanFinrank : WithBot ℕ∞) =
        (d : WithBot ℕ∞) := by
      calc
        (↑(IsLocalRing.maximalIdeal A).spanFinrank : WithBot ℕ∞) =
            ringKrullDim A := hregular.spanFinrank_maximalIdeal
        _ = d := by exact_mod_cast hdim
    calc
      Module.finrank (Chapter13ResidueRing A) (IsLocalRing.CotangentSpace A) =
          (IsLocalRing.maximalIdeal A).spanFinrank := hspan.symm
      _ = d := by exact_mod_cast hspan'
  have hpind : LinearIndependent (Chapter13ResidueRing A)
      (fun _ : Fin 1 => pclass) := by
    rw [linearIndependent_subsingleton_index_iff]
    simpa [pclass] using hpclass
  let b : Module.Basis
      (Fin 1 ⊕ (Module.Basis.sumExtendIndex (v := fun _ : Fin 1 => pclass) hpind : Type _))
      (Chapter13ResidueRing A) (IsLocalRing.CotangentSpace A) :=
    Module.Basis.sumExtend (v := fun _ : Fin 1 => pclass) hpind
  let I := Module.Basis.sumExtendIndex (v := fun _ : Fin 1 => pclass) hpind
  letI : Fintype (Fin 1 ⊕
      (Module.Basis.sumExtendIndex (v := fun _ : Fin 1 => pclass) hpind : Type _)) :=
    FiniteDimensional.fintypeBasisIndex b
  letI : Finite (I : Type _) := Finite.of_injective
    (fun i : (I : Type _) => (Sum.inr i : Fin 1 ⊕ (I : Type _)))
    (fun _ _ h => Sum.inr.inj h)
  letI : Fintype (I : Type _) := Fintype.ofFinite I
  have hcard_basis : Fintype.card (Fin 1 ⊕ (I : Type _)) = d := by
    rw [← Module.finrank_eq_card_basis b, hfinrank]
  have hcardI : Fintype.card (I : Type _) = d - 1 := by
    have hcard_sum : 1 + Fintype.card (I : Type _) = d := by
      have hcard_sum' : Fintype.card (Fin 1 ⊕ (I : Type _)) =
          1 + Fintype.card (I : Type _) := by
        calc
          Fintype.card (Fin 1 ⊕ (I : Type _)) =
              Fintype.card (Fin 1 ⊕ Fin (Fintype.card (I : Type _))) :=
            Fintype.card_congr
              (Equiv.sumCongr (Equiv.refl (Fin 1)) (Fintype.equivFin (I : Type _)))
          _ = 1 + Fintype.card (I : Type _) := by simp
      calc
        1 + Fintype.card (I : Type _) = Fintype.card (Fin 1 ⊕ (I : Type _)) :=
          hcard_sum'.symm
        _ = d := hcard_basis
    omega
  let e : Fin (d - 1) ≃ (I : Type _) := Fintype.equivOfCardEq (by
    simpa using hcardI.symm)
  let T := hpind.linearIndepOn_id.extend (Set.subset_univ _)
  let b0 : Module.Basis (T : Type _) (Chapter13ResidueRing A)
      (IsLocalRing.CotangentSpace A) := Module.Basis.extend hpind.linearIndepOn_id
  let liftI : ↥I → ↥T := fun i => ⟨i.1, i.property.1⟩
  let y : Fin (d - 1) → IsLocalRing.CotangentSpace A :=
    fun i => b0 (liftI (e i))
  have hspanQ : Submodule.span (Chapter13ResidueRing A)
      ({pclass} ∪ Set.range y) = ⊤ := by
    rw [← b0.span_eq]
    apply le_antisymm
    · apply Submodule.span_le.2
      intro q hq
      rcases hq with hq | ⟨i, rfl⟩
      · rw [b0.span_eq]
        exact Set.mem_univ q
      · exact Submodule.subset_span ⟨liftI (e i), rfl⟩
    · apply Submodule.span_le.2
      rintro q ⟨j, rfl⟩
      by_cases hj : (j : IsLocalRing.CotangentSpace A) ∈
          Set.range (fun _ : Fin 1 => pclass)
      · let qj : Set.range (fun _ : Fin 1 => pclass) := ⟨j, hj⟩
        have hT : Set.range (fun _ : Fin 1 => pclass) ⊆ T :=
          hpind.linearIndepOn_id.subset_extend (Set.subset_univ _)
        have hj' : j = Set.inclusion hT qj := by
          exact Subtype.ext rfl
        have hbj : b0 j = (j : IsLocalRing.CotangentSpace A) := by
          calc
            b0 j = b0 (Set.inclusion hT qj) :=
              congrArg b0 hj'
            _ = (j : IsLocalRing.CotangentSpace A) :=
              Module.Basis.extend_apply_self hpind.linearIndepOn_id (Set.inclusion hT qj)
        rw [hbj]
        obtain ⟨a, ha⟩ := hj
        have hval : (j : IsLocalRing.CotangentSpace A) = pclass := by
          simpa [Fin.eq_zero a] using ha.symm
        rw [hval]
        exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_singleton _))
      · have hjI : (j : IsLocalRing.CotangentSpace A) ∈ (I : Set _) :=
          ⟨j.property, hj⟩
        obtain ⟨i, hi⟩ := e.surjective ⟨j, hjI⟩
        have hje : liftI (e i) = j := by
          have hv : (e i : IsLocalRing.CotangentSpace A) =
              (j : IsLocalRing.CotangentSpace A) :=
            congrArg (fun q : I => (q : IsLocalRing.CotangentSpace A)) hi
          apply Subtype.ext
          exact hv
        rw [← hje]
        exact Submodule.subset_span (Set.mem_union_right _ ⟨i, rfl⟩)
  let z : Fin (d - 1) → IsLocalRing.maximalIdeal A := fun i =>
    Classical.choose ((IsLocalRing.maximalIdeal A).toCotangent_surjective (y i))
  have hz : ∀ i, (IsLocalRing.maximalIdeal A).toCotangent (z i) = y i := by
    intro i
    exact Classical.choose_spec
      ((IsLocalRing.maximalIdeal A).toCotangent_surjective (y i))
  have himage : (IsLocalRing.maximalIdeal A).toCotangent ''
      ({pM} ∪ Set.range z) = {pclass} ∪ Set.range y := by
    ext q
    constructor
    · rintro ⟨v, (rfl | ⟨i, rfl⟩), rfl⟩
      · exact Set.mem_union_left _ (Set.mem_singleton _)
      · exact Set.mem_union_right _ ⟨i, (hz i).symm⟩
    · intro hq
      rcases hq with rfl | ⟨i, rfl⟩
      · exact ⟨pM, Or.inl rfl, rfl⟩
      · exact ⟨z i, Or.inr ⟨i, rfl⟩, hz i⟩
  have hspanM : Submodule.span A ({pM} ∪ Set.range z) = ⊤ := by
    apply (IsLocalRing.CotangentSpace.span_image_eq_top_iff).mp
    rw [himage]
    exact hspanQ
  let x : Fin (d - 1) → A := fun i => (z i).1
  have hmaptop :
      Submodule.map (IsLocalRing.maximalIdeal A).subtype
        (Submodule.span A ({pM} ∪ Set.range z)) =
        (IsLocalRing.maximalIdeal A).subtype.range := by
    rw [hspanM, Submodule.map_top]
  have himage' : (IsLocalRing.maximalIdeal A).subtype ''
      ({pM} ∪ Set.range z) = {(p : A)} ∪ Set.range x := by
    ext a
    constructor
    · rintro ⟨v, (rfl | ⟨i, rfl⟩), rfl⟩
      · exact Set.mem_union_left _ (Set.mem_singleton _)
      · exact Set.mem_union_right _ ⟨i, rfl⟩
    · intro ha
      rcases ha with rfl | ⟨i, rfl⟩
      · exact ⟨pM, Or.inl rfl, rfl⟩
      · exact ⟨z i, Or.inr ⟨i, rfl⟩, rfl⟩
  have hgen : Ideal.span ({(p : A)} ∪ Set.range x) = IsLocalRing.maximalIdeal A := by
    calc
      Ideal.span ({(p : A)} ∪ Set.range x) =
          Submodule.map (IsLocalRing.maximalIdeal A).subtype
            (Submodule.span A ({pM} ∪ Set.range z)) := by
        change Submodule.span A ({(p : A)} ∪ Set.range x) = _
        rw [Submodule.map_span, himage']
      _ = (IsLocalRing.maximalIdeal A).subtype.range := hmaptop
      _ = IsLocalRing.maximalIdeal A := Submodule.range_subtype _
  have hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    exact (z i).property
  have hspan_le : Ideal.span ({(p : A)} ∪ Set.range x) ≤
      Ideal.map u (IsLocalRing.maximalIdeal C) ⊔ Ideal.span (Set.range x) := by
    apply Ideal.span_le.2
    rintro a (ha | ⟨i, rfl⟩)
    · rcases ha with rfl
      refine Ideal.mem_sup_left ?_
      have hpC : (p : C) ∈ IsLocalRing.maximalIdeal C := by
        rw [hC.1.2.1]
        exact Ideal.subset_span (Set.mem_singleton _)
      have hpm := Ideal.mem_map_of_mem u hpC
      simpa using hpm
    · exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨hdomC, hDvrC⟩ := hC.1.1
  have hCnoeth : IsNoetherianRing C :=
    ⟨fun I => hDvrC.toIsPrincipalIdealRing.principal I |>.fg⟩
  have hCcomplete : Chapter13CompleteNoetherianLocalRing C :=
    ⟨hCnoeth, hC.2⟩
  have hres_surj : Function.Surjective
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
    hCcomplete hA (d - 1) u hu x hx
  have hsurj : Function.Surjective F := by
    apply (chapter13_power_series_evaluation_surjective_iff
      hCcomplete hA (d - 1) u x F hF).2
    intro a
    obtain ⟨r, hr⟩ := hres_surj (Chapter13ResidueMap A a)
    have hm : a - u r ∈ IsLocalRing.maximalIdeal A := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      change Chapter13ResidueMap A (a - u r) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hr.symm
    rw [← hgen] at hm
    refine ⟨r, a - u r, hspan_le hm, ?_⟩
    simp
  let P := MvPowerSeries (Fin (d - 1)) C
  have hP := chapter13_power_series_over_cohen_ring_is_regular C k p (d - 1) hC
  letI : IsDomain P := by
    simpa [P] using hP.2.2.1
  have hPdim : ringKrullDim P = d := by
    calc
      ringKrullDim P = (↑(d - 1) : WithBot ℕ∞) + 1 := by
        simpa [P] using hP.2.2.2
      _ = (d : WithBot ℕ∞) := by
        exact_mod_cast Nat.sub_add_cancel hdimpos
  have hker : RingHom.ker F = ⊥ := by
    by_contra hker
    obtain ⟨r, hr, hr0⟩ : ∃ r : P, r ∈ RingHom.ker F ∧ r ≠ 0 := by
      by_contra hnone
      apply hker
      apply le_antisymm
      · intro r hr
        by_contra hr0
        exact hnone ⟨r, hr, hr0⟩
      · exact bot_le
    have hdimle := ringKrullDim_succ_le_of_surjective F hsurj
      (mem_nonZeroDivisors_of_ne_zero hr0) hr
    have hcontra : (↑d : WithBot ℕ∞) + 1 ≤ ↑d := by
      simpa [P, hPdim, hdim] using hdimle
    exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self d)) hcontra
  refine ⟨RingEquiv.ofBijective F ?_⟩
  exact ⟨(RingHom.injective_iff_ker_eq_bot F).mpr hker, hsurj⟩

private theorem chapter13_finite_length_quotient_finite_over_coeff
    {A k : Type u} [CommRing A] [IsLocalRing A] [Field k]
    (σ : k →+* A) (hσ : IsLocalHom σ)
    (hres : Function.Bijective ((Chapter13ResidueMap A).comp σ))
    (I : Ideal A) (hI : IsFiniteLength A (A ⧸ I)) :
    letI : Algebra k A := σ.toAlgebra
    letI : Module k (A ⧸ I) := Module.compHom (A ⧸ I) (algebraMap k A)
    Module.Finite k (A ⧸ I) := by
  letI : Algebra k A := σ.toAlgebra
  letI : IsLocalHom (algebraMap k A) := hσ
  letI : Module k (A ⧸ I) := Module.compHom (A ⧸ I) (algebraMap k A)
  letI : IsScalarTower k A (A ⧸ I) := IsScalarTower.of_algebraMap_eq' rfl
  change Function.Bijective
    ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp σ) at hres
  have hres' : Function.Bijective
      ((IsLocalRing.residue A).comp (algebraMap k A)) := by
    change Function.Bijective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp (algebraMap k A))
    simpa [RingHom.algebraMap_toAlgebra] using hres
  have hmap : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField A)) := by
    intro y
    obtain ⟨a, ha⟩ := hres'.2 y
    refine ⟨IsLocalRing.residue k a, ?_⟩
    change ((IsLocalRing.ResidueField.map (algebraMap k A)).comp
      (IsLocalRing.residue k)) a = y
    rw [IsLocalRing.ResidueField.map_comp_residue]
    exact ha
  have hreslen : Module.length (IsLocalRing.ResidueField k)
      (IsLocalRing.ResidueField A) = 1 := by
    rw [Module.length_eq_of_surjective (M := IsLocalRing.ResidueField A) hmap]
    exact Module.length_eq_one _ _
  have hlength := IsLocalRing.length_restrictScalars k A (A ⧸ I)
  have hfinitek : IsFiniteLength k (A ⧸ I) := by
    have hI' := (isFiniteLength_iff_isNoetherian_isArtinian.mp hI)
    letI : IsNoetherian A (A ⧸ I) := hI'.1
    letI : IsArtinian A (A ⧸ I) := hI'.2
    apply (Module.length_ne_top_iff).mp
    rw [hlength, hreslen, mul_one]
    exact Module.length_ne_top (R := A) (M := A ⧸ I)
  exact (IsArtinianRing.tfae k (A ⧸ I)).out 3 0 |>.mp hfinitek

private theorem chapter13_isPrecomplete_fin_pi
    {P : Type u} [CommRing P] (K : Ideal P) (r : ℕ)
    [IsAdicComplete K P] : IsPrecomplete K (Fin r → P) := by
  rw [isPrecomplete_iff]
  intro f hf
  have hproj : ∀ (i : Fin r) {m n : ℕ}, m ≤ n →
      f m i ≡ f n i [SMOD (K ^ m • (⊤ : Submodule P P))] := by
    intro i m n hmn
    have hmf := hf hmn
    rw [SModEq.sub_mem] at hmf ⊢
    have hmap : (K ^ m • (⊤ : Submodule P (Fin r → P))).map
        (LinearMap.proj (R := P) i) ≤ K ^ m • (⊤ : Submodule P P) := by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr (LinearMap.proj_surjective (R := P) i)]
    have hmem := hmap
      (Submodule.mem_map_of_mem hmf)
    simpa using hmem
  choose g hg using fun i : Fin r =>
    (inferInstance : IsPrecomplete K P).prec (hproj i)
  let g' : Fin r → P := g
  refine ⟨g', ?_⟩
  intro n
  rw [SModEq.sub_mem]
  have hcoord : ∀ i : Fin r,
      f n i - g' i ∈ K ^ n := by
    intro i
    simpa [SModEq.sub_mem, Ideal.smul_top_eq_map] using hg i n
  have hsum : f n - g' = ∑ i : Fin r, (f n i - g' i) • Pi.single i 1 := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem_smul
  · exact hcoord i
  · exact Submodule.mem_top

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
  classical
  have hk : Chapter13CompleteNoetherianLocalRing k := by
    constructor
    · exact ((IsArtinianRing.tfae k k).out 2 1).mp
        (inferInstance : IsArtinianRing k)
    · rw [IsLocalRing.maximalIdeal_eq_bot]
      exact (inferInstance : IsAdicComplete (⊥ : Ideal k) k)
  obtain ⟨F, hF, _⟩ := chapter13_power_series_evaluation_exists_unique
    hk hA s σ hσ x hx
  let P := MvPowerSeries (Fin s) k
  let K : Ideal P := Chapter13PowerSeriesMaximalIdeal k s
  have hJ : Ideal.map F K = Ideal.span (Set.range x) := by
    dsimp [K, Chapter13PowerSeriesMaximalIdeal]
    rw [Ideal.map_sup, Ideal.map_map, hF.1, Ideal.map_span]
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot, bot_sup_eq]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rw [hF.2.1 i]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨MvPowerSeries.X i, ⟨i, rfl⟩, hF.2.1 i⟩
  let I : Ideal A := Ideal.span (Set.range x)
  have hfiniteI : IsFiniteLength A (A ⧸ I) := by
    simpa [Chapter13FiniteLengthParameterFamily, I] using hfinite
  letI : Algebra k A := σ.toAlgebra
  letI : Module k (A ⧸ I) := Module.compHom (A ⧸ I) (algebraMap k A)
  letI : IsScalarTower k A (A ⧸ I) := IsScalarTower.of_algebraMap_eq' rfl
  have hquot : Module.Finite k (A ⧸ I) :=
    chapter13_finite_length_quotient_finite_over_coeff σ hσ hres I hfiniteI
  letI : Module.Finite k (A ⧸ I) := hquot
  obtain ⟨r, q, hq⟩ := Module.Finite.exists_fin' k (A ⧸ I)
  let b : Module.Basis (Fin r) k (Fin r → k) := Pi.basisFun k (Fin r)
  choose y hy using fun i : Fin r =>
    Ideal.Quotient.mk_surjective (q (b i))
  letI : Algebra P A := F.toAlgebra
  let f : (Fin r → P) →ₗ[P] A :=
    LinearMap.lsum P (fun _ : Fin r => P) P
      (fun i => (Algebra.linearMap P A).smulRight (y i))
  have hf_single : ∀ i : Fin r, f (Pi.single i 1) = y i := by
    intro i
    simp [f, Pi.single_apply, Algebra.smul_def]
  have htower : (algebraMap k A) =
      (algebraMap P A).comp (algebraMap k P) := by
    ext a
    change σ a = F (MvPowerSeries.C a)
    exact congrArg (fun g => g a) hF.1.symm
  letI : IsScalarTower k P A :=
    IsScalarTower.of_algebraMap_eq' htower
  have hPcomplete : IsAdicComplete K P := by
    change IsAdicComplete (Chapter13PowerSeriesMaximalIdeal k s)
      (MvPowerSeries (Fin s) k)
    have hlocal := chapter13_power_series_complete_local k hk.2 s
    rw [← hlocal.2.1]
    exact hlocal.1.2
  letI : IsAdicComplete K P := hPcomplete
  letI : IsPrecomplete K (Fin r → P) :=
    chapter13_isPrecomplete_fin_pi K r
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := hA.2
  have hJle : Ideal.map F K ≤ IsLocalRing.maximalIdeal A := by
    rw [hJ]
    apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    exact hx i
  letI : IsHausdorff K A := IsHausdorff.of_map hJle
  let cₗ : (Fin r → k) →ₗ[k] (Fin r → P) :=
    LinearMap.piMap (fun _ => Algebra.linearMap k P)
  let fₗ : (Fin r → P) →ₗ[k] A := f.restrictScalars k
  let mkₗ : A →ₗ[k] A ⧸ I :=
    (Ideal.Quotient.mkₐ k I).toLinearMap
  let qf : (Fin r → k) →ₗ[k] A ⧸ I :=
    mkₗ.comp (fₗ.comp cₗ)
  have hqf : qf = q := by
    apply Module.Basis.ext b
    intro i
    have hc : cₗ (b i) = Pi.single i (1 : P) := by
      funext j
      change algebraMap k P ((b i) j) =
        (Pi.single i (1 : P) : Fin r → P) j
      rw [MvPowerSeries.algebraMap_apply]
      by_cases hij : i = j
      · subst j
        simp [b, Pi.basisFun]
      · simp [b, Pi.basisFun, hij]
    dsimp [qf, mkₗ, fₗ]
    rw [hc]
    change Ideal.Quotient.mk I (f (Pi.single i 1)) = q (b i)
    rw [hf_single i]
    exact hy i
  have hbase : Function.Surjective
      ((K • (⊤ : Submodule P A)).mkQ.comp f) := by
    intro a
    obtain ⟨a, rfl⟩ := (K • (⊤ : Submodule P A)).mkQ_surjective a
    obtain ⟨v, hv⟩ := hq (Ideal.Quotient.mk I a)
    refine ⟨cₗ v, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    have heq : Ideal.Quotient.mk I (f (cₗ v)) =
        Ideal.Quotient.mk I a := by
      calc
        Ideal.Quotient.mk I (f (cₗ v)) = qf v := by rfl
        _ = q v := by rw [hqf]
        _ = Ideal.Quotient.mk I a := hv
    have hmemI : f (cₗ v) - a ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr heq
    change f (cₗ v) - a ∈ Ideal.span (Set.range x) at hmemI
    rw [← hJ] at hmemI
    rw [Ideal.smul_top_eq_map]
    change f (cₗ v) - a ∈ Ideal.map F K
    exact hmemI
  have hsurj : Function.Surjective f := by
    exact surjective_of_mkQ_comp_surjective hbase
  exact ⟨F, hF, by
    dsimp [Chapter13FinitePowerSeriesModule]
    exact Module.Finite.of_surjective f hsurj⟩

private theorem chapter13_finite_length_quotient_finite_over_local_coeff
    {A R : Type u} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (u : R →+* A) (hu : IsLocalHom u)
    (hres : Function.Surjective ((Chapter13ResidueMap A).comp u))
    (I : Ideal A) (hI : IsFiniteLength A (A ⧸ I)) :
    letI : Algebra R A := u.toAlgebra
    letI : Module R (A ⧸ I) := Module.compHom (A ⧸ I) (algebraMap R A)
    Module.Finite R (A ⧸ I) := by
  letI : Algebra R A := u.toAlgebra
  letI : IsLocalHom (algebraMap R A) := hu
  letI : Module R (A ⧸ I) := Module.compHom (A ⧸ I) (algebraMap R A)
  letI : IsScalarTower R A (A ⧸ I) := IsScalarTower.of_algebraMap_eq' rfl
  change Function.Surjective
    ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp u) at hres
  have hres' : Function.Surjective
      ((IsLocalRing.residue A).comp (algebraMap R A)) := by
    change Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp (algebraMap R A))
    simpa [RingHom.algebraMap_toAlgebra] using hres
  have hmap : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)) := by
    intro y
    obtain ⟨a, ha⟩ := hres' y
    refine ⟨IsLocalRing.residue R a, ?_⟩
    change ((IsLocalRing.ResidueField.map (algebraMap R A)).comp
      (IsLocalRing.residue R)) a = y
    rw [IsLocalRing.ResidueField.map_comp_residue]
    exact ha
  have hreslen : Module.length (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField A) = 1 := by
    rw [Module.length_eq_of_surjective (M := IsLocalRing.ResidueField A) hmap]
    exact Module.length_eq_one _ _
  have hlength := IsLocalRing.length_restrictScalars R A (A ⧸ I)
  have hfiniteR : IsFiniteLength R (A ⧸ I) := by
    have hI' := (isFiniteLength_iff_isNoetherian_isArtinian.mp hI)
    letI : IsNoetherian A (A ⧸ I) := hI'.1
    letI : IsArtinian A (A ⧸ I) := hI'.2
    apply (Module.length_ne_top_iff).mp
    rw [hlength, hreslen, mul_one]
    exact Module.length_ne_top (R := A) (M := A ⧸ I)
  have hfiniteR' := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteR)
  letI : IsNoetherian R (A ⧸ I) := hfiniteR'.1
  exact inferInstance

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
  classical
  obtain ⟨_hdomC, hDvrC⟩ := hC.1.1
  have hCnoeth : IsNoetherianRing C :=
    ⟨fun I => hDvrC.toIsPrincipalIdealRing.principal I |>.fg⟩
  letI : IsNoetherianRing C := hCnoeth
  have hCcomplete : Chapter13CompleteNoetherianLocalRing C :=
    ⟨hCnoeth, hC.2⟩
  obtain ⟨F, hF, _⟩ := chapter13_power_series_evaluation_exists_unique
    hCcomplete hA s u hu x hx
  have hres_surj : Function.Surjective
      ((Chapter13ResidueMap A).comp u) := by
    intro y
    let q : Chapter13ResidueRing C := eC.symm (eA y)
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨c, eA.injective ?_⟩
    calc
      eA (Chapter13ResidueMap A (u c)) =
          eC (Chapter13ResidueMap C c) := by
        simpa using hres c
      _ = eC q := by
        simpa [Chapter13ResidueMap] using congrArg eC hc
      _ = eA y := by simp [q]
  let I : Ideal A :=
    Ideal.map u (IsLocalRing.maximalIdeal C) ⊔ Ideal.span (Set.range x)
  have hpmap : (p : A) ∈ Ideal.map u (IsLocalRing.maximalIdeal C) := by
    have hpC : (p : C) ∈ IsLocalRing.maximalIdeal C := by
      rw [hC.1.2.1]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hpm := Ideal.mem_map_of_mem u hpC
    simpa using hpm
  have hJI : Ideal.span ({(p : A)} ∪ Set.range x) ≤ I := by
    apply Ideal.span_le.2
    rintro a (ha | ⟨i, rfl⟩)
    · rcases ha with rfl
      exact Ideal.mem_sup_left hpmap
    · exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hfiniteI : IsFiniteLength A (A ⧸ I) := by
    let J : Ideal A := Ideal.span ({(p : A)} ∪ Set.range x)
    have hfiniteJ : IsFiniteLength A (A ⧸ J) := by
      simpa [Chapter13FiniteLengthParameterFamily, J] using hfinite
    have hJI' : J ≤ I := by
      change Ideal.span ({(p : A)} ∪ Set.range x) ≤ I
      exact hJI
    let qmap : A ⧸ J →ₗ[A] A ⧸ I :=
      (Ideal.Quotient.factorₐ A hJI').toLinearMap
    exact IsFiniteLength.of_surjective hfiniteJ
      (show Function.Surjective qmap by
        intro z
        obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective z
        refine ⟨Ideal.Quotient.mk J a, ?_⟩
        simpa [qmap] using ha)
  letI : Algebra C A := u.toAlgebra
  letI : Module C (A ⧸ I) := Module.compHom (A ⧸ I) (algebraMap C A)
  letI : IsScalarTower C A (A ⧸ I) := IsScalarTower.of_algebraMap_eq' rfl
  have hquot : Module.Finite C (A ⧸ I) :=
    chapter13_finite_length_quotient_finite_over_local_coeff
      u hu hres_surj I hfiniteI
  letI : Module.Finite C (A ⧸ I) := hquot
  obtain ⟨r, q, hq⟩ := Module.Finite.exists_fin' C (A ⧸ I)
  let b : Module.Basis (Fin r) C (Fin r → C) := Pi.basisFun C (Fin r)
  choose y hy using fun i : Fin r =>
    Ideal.Quotient.mk_surjective (q (b i))
  let P := MvPowerSeries (Fin s) C
  let K : Ideal P := Chapter13PowerSeriesMaximalIdeal C s
  have hJ : Ideal.map F K = I := by
    dsimp [K, Chapter13PowerSeriesMaximalIdeal, I]
    rw [Ideal.map_sup, Ideal.map_map, hF.1, Ideal.map_span]
    congr 1
    apply le_antisymm
    · apply Ideal.span_le.2
      rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨i, by rw [hF.2.1 i]⟩
    · apply Ideal.span_le.2
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨MvPowerSeries.X i, ⟨i, rfl⟩, hF.2.1 i⟩
  letI : Algebra P A := F.toAlgebra
  let f : (Fin r → P) →ₗ[P] A :=
    LinearMap.lsum P (fun _ : Fin r => P) P
      (fun i => (Algebra.linearMap P A).smulRight (y i))
  have hf_single : ∀ i : Fin r, f (Pi.single i 1) = y i := by
    intro i
    simp [f, Pi.single_apply, Algebra.smul_def]
  have htower : (algebraMap C A) =
      (algebraMap P A).comp (algebraMap C P) := by
    ext c
    change u c = F (MvPowerSeries.C c)
    exact congrArg (fun g => g c) hF.1.symm
  letI : IsScalarTower C P A :=
    IsScalarTower.of_algebraMap_eq' htower
  have hPcomplete : IsAdicComplete K P := by
    change IsAdicComplete (Chapter13PowerSeriesMaximalIdeal C s)
      (MvPowerSeries (Fin s) C)
    have hlocal := chapter13_power_series_complete_local C hC.2 s
    rw [← hlocal.2.1]
    exact hlocal.1.2
  letI : IsAdicComplete K P := hPcomplete
  letI : IsPrecomplete K (Fin r → P) :=
    chapter13_isPrecomplete_fin_pi K r
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := hA.2
  letI : IsLocalHom u := hu
  have hJle : Ideal.map F K ≤ IsLocalRing.maximalIdeal A := by
    rw [hJ]
    exact sup_le (IsLocalRing.map_maximalIdeal_le u)
      (Ideal.span_le.2 (by
        rintro _ ⟨i, rfl⟩
        exact hx i))
  letI : IsHausdorff K A := IsHausdorff.of_map hJle
  let cₗ : (Fin r → C) →ₗ[C] (Fin r → P) :=
    LinearMap.piMap (fun _ => Algebra.linearMap C P)
  let fₗ : (Fin r → P) →ₗ[C] A := f.restrictScalars C
  let mkₗ : A →ₗ[C] A ⧸ I :=
    (Ideal.Quotient.mkₐ C I).toLinearMap
  let qf : (Fin r → C) →ₗ[C] A ⧸ I :=
    mkₗ.comp (fₗ.comp cₗ)
  have hqf : qf = q := by
    apply Module.Basis.ext b
    intro i
    have hc : cₗ (b i) = Pi.single i (1 : P) := by
      funext j
      change algebraMap C P ((b i) j) =
        (Pi.single i (1 : P) : Fin r → P) j
      rw [MvPowerSeries.algebraMap_apply]
      by_cases hij : i = j
      · subst j
        simp [b, Pi.basisFun]
      · simp [b, Pi.basisFun, hij]
    dsimp [qf, mkₗ, fₗ]
    rw [hc]
    change Ideal.Quotient.mk I (f (Pi.single i 1)) = q (b i)
    rw [hf_single i]
    exact hy i
  have hbase : Function.Surjective
      ((K • (⊤ : Submodule P A)).mkQ.comp f) := by
    intro a
    obtain ⟨a, rfl⟩ := (K • (⊤ : Submodule P A)).mkQ_surjective a
    obtain ⟨v, hv⟩ := hq (Ideal.Quotient.mk I a)
    refine ⟨cₗ v, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    have heq : Ideal.Quotient.mk I (f (cₗ v)) =
        Ideal.Quotient.mk I a := by
      calc
        Ideal.Quotient.mk I (f (cₗ v)) = qf v := by rfl
        _ = q v := by rw [hqf]
        _ = Ideal.Quotient.mk I a := hv
    have hmemI : f (cₗ v) - a ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr heq
    rw [← hJ] at hmemI
    rw [Ideal.smul_top_eq_map]
    change f (cₗ v) - a ∈ Ideal.map F K
    exact hmemI
  have hsurj : Function.Surjective f := by
    exact surjective_of_mkQ_comp_surjective hbase
  exact ⟨F, hF, by
    dsimp [Chapter13FinitePowerSeriesModule]
    exact Module.Finite.of_surjective f hsurj⟩

theorem chapter13_finite_power_series_map_injective
    {A Q : Type u} [CommRing A] [IsLocalRing A] [CommRing Q]
    (I : Ideal Q) (d : ℕ)
    (hQ : Chapter13CompleteRegularLocalDomain Q I d)
    (F : Q →+* A)
    (hfinite : Chapter13FinitePowerSeriesModule F)
    (hdomain : IsDomain A)
    (hdim : ringKrullDim Q = ringKrullDim A) :
    Function.Injective F := by
  letI : Algebra Q A := F.toAlgebra
  letI : Module Q A := Module.compHom A F
  letI : Module.Finite Q A := by
    simpa [Chapter13FinitePowerSeriesModule] using hfinite
  have hann : Module.annihilator Q A = RingHom.ker F := by
    ext q
    constructor
    · intro hq
      have h1 : q • (1 : A) = 0 := (Module.mem_annihilator.mp hq) 1
      change F q * (1 : A) = 0 at h1
      simpa using h1
    · intro hq
      rw [Module.mem_annihilator]
      intro a
      rw [show q • a = F q * a by rfl, RingHom.mem_ker.mp hq, zero_mul]
  let B := Q ⧸ RingHom.ker F
  let g : B →+* A := Ideal.Quotient.lift (RingHom.ker F) F
    (fun a ha => RingHom.mem_ker.mp ha)
  letI : Algebra B A := g.toAlgebra
  letI : Module B A := Module.compHom A g
  letI : Module Q B := Module.compHom B (Ideal.Quotient.mk (RingHom.ker F))
  have hcomp : F = g.comp (Ideal.Quotient.mk (RingHom.ker F)) := by
    ext q
    rfl
  letI : IsScalarTower Q B A := IsScalarTower.of_algebraMap_eq' (by
    change F = g.comp (Ideal.Quotient.mk (RingHom.ker F))
    exact hcomp)
  letI : Module.Finite B A := Module.Finite.of_restrictScalars_finite Q B A
  letI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have hdimA_le : ringKrullDim A ≤ ringKrullDim B := by
    let φ : PrimeSpectrum A → PrimeSpectrum B :=
      PrimeSpectrum.comap (algebraMap B A)
    have hφ : StrictMono φ := by
      intro p q hpq
      change p.asIdeal.comap (algebraMap B A) <
        q.asIdeal.comap (algebraMap B A)
      exact IsIntegral.comap_lt_comap hpq
    exact Order.krullDim_le_of_strictMono _ hφ
  have hdimquot : ringKrullDim B = ringKrullDim A := by
    have hs : Module.supportDim Q A =
        ringKrullDim (Q ⧸ Module.annihilator Q A) :=
      Module.supportDim_eq_ringKrullDim_quotient_annihilator Q A
    rw [hann] at hs
    have hB_leQ : ringKrullDim B ≤ ringKrullDim Q := by
      simpa [B] using (hs.symm ▸ Module.supportDim_le_ringKrullDim Q A)
    exact le_antisymm (hB_leQ.trans (le_of_eq hdim)) hdimA_le
  intro x y hxy
  by_contra hxy'
  have hker : RingHom.ker F ≠ ⊥ := by
    intro hker
    apply hxy'
    apply (RingHom.injective_iff_ker_eq_bot F).mpr hker
    exact hxy
  obtain ⟨r, hr, hr0⟩ : ∃ r : Q, r ∈ RingHom.ker F ∧ r ≠ 0 := by
    by_contra hn
    apply hker
    apply le_antisymm
    · intro q hq
      by_contra hq0
      exact hn ⟨q, hq, hq0⟩
    · exact bot_le
  letI : IsDomain Q := hQ.2.2.1
  have hqdim := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.mk (RingHom.ker F)) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  change ringKrullDim B + 1 ≤ ringKrullDim Q at hqdim
  have hplusAB : ringKrullDim A + 1 ≤ ringKrullDim B + 1 := by
    simpa [add_comm] using add_le_add_right hdimA_le (1 : WithBot ℕ∞)
  have hplus := hplusAB.trans hqdim
  rw [← hdim, hQ.2.2.2] at hplus
  exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self d)) hplus

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
