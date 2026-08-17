import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section04HenselianLocalRings
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.CharP.MixedCharZero
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.RegularLocalRing.Defs

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Filter Ideal IsLocalRing
open scoped BigOperators MvPowerSeries Topology

noncomputable section

/-! # Book 1, Chapter 13, Section 13.1: Coordinates for a complete local ring -/

universe u v

/-- The residue ring of a local ring, using Mathlib's canonical quotient. -/
abbrev Chapter13ResidueRing (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  A ⧸ IsLocalRing.maximalIdeal A

/-- The residue quotient of a local ring carries its canonical field structure. -/
noncomputable instance chapter13ResidueRingField
    (A : Type u) [CommRing A] [IsLocalRing A] : Field (Chapter13ResidueRing A) :=
  Ideal.Quotient.field (IsLocalRing.maximalIdeal A)

/-- The canonical reduction map to the residue ring. -/
def Chapter13ResidueMap (A : Type u) [CommRing A] [IsLocalRing A] :
    A →+* Chapter13ResidueRing A :=
  Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)

/-- The adic notion of continuity used throughout the chapter. -/
def Chapter13AdicContinuous
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, ∀ x : R, x ∈ I ^ m → f x ∈ J ^ n

/-- Complete and separated Noetherian local rings. -/
def Chapter13CompleteNoetherianLocalRing
    (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  IsNoetherianRing A ∧ IsAdicComplete (IsLocalRing.maximalIdeal A) A

/-- The condition `A = σ(R) + J` in the power-series evaluation lemma. -/
def Chapter13CoefficientPlusIdeal
    {R A : Type*} [CommRing R] [CommRing A]
    (σ : R →+* A) (J : Ideal A) : Prop :=
  ∀ a : A, ∃ r : R, ∃ j : A, j ∈ J ∧ a = σ r + j

/-- A subfield of a possibly non-domain ambient ring. -/
structure Chapter13Subfield (A : Type u) [CommRing A] where
  carrier : Subring A
  field_carrier : IsField carrier

/-- The image of a subfield in the residue ring. -/
def Chapter13SubfieldResidueImage
    {A : Type u} [CommRing A] [IsLocalRing A]
    (K : Chapter13Subfield A) : Set (Chapter13ResidueRing A) :=
  Set.range ((Chapter13ResidueMap A).comp K.carrier.subtype)

/-- A subfield is a coefficient field exactly when its reduction is bijective. -/
def Chapter13IsCoefficientField
    {A : Type u} [CommRing A] [IsLocalRing A]
    (K : Chapter13Subfield A) : Prop :=
  Function.Bijective ((Chapter13ResidueMap A).comp K.carrier.subtype)

/-- Maximality among subfields of the ambient ring. -/
def Chapter13IsMaximalSubfield
    {A : Type u} [CommRing A] (K : Chapter13Subfield A) : Prop :=
  ∀ L : Chapter13Subfield A, K.carrier ≤ L.carrier → L.carrier ≤ K.carrier

/-- The coefficient-field decomposition of an element into a residue coefficient and an error. -/
def Chapter13CoefficientDecomposition
    {A : Type u} [CommRing A] [IsLocalRing A]
    (K : Chapter13Subfield A) : Prop :=
  ∀ a : A, ∃ k : K.carrier, ∃ m : A,
    m ∈ IsLocalRing.maximalIdeal A ∧ a = k.1 + m

/-- Equal characteristic zero. -/
def Chapter13EqualCharacteristicZero
    (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  CharP A 0 ∧ CharP (Chapter13ResidueRing A) 0

/-- Equal characteristic `p`. -/
def Chapter13EqualCharacteristicPrime
    (A : Type u) [CommRing A] [IsLocalRing A] (p : ℕ) : Prop :=
  Nat.Prime p ∧ CharP A p ∧ CharP (Chapter13ResidueRing A) p

/-- Mixed characteristic with residue characteristic `p`. -/
def Chapter13MixedCharacteristic
    (A : Type u) [CommRing A] [IsLocalRing A] (p : ℕ) : Prop :=
  Nat.Prime p ∧ CharP (Chapter13ResidueRing A) p ∧ ¬ CharP A p

/-- A ring contains a field, expressed by the subfield package used in this chapter. -/
def Chapter13ContainsField (A : Type u) [CommRing A] : Prop :=
  Nonempty (Chapter13Subfield A)

/-- A local ring homomorphism in the sense used by the source. -/
abbrev Chapter13LocalHom
    {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) : Prop :=
  IsLocalHom f

/-- The maximal ideal of a finite-variable power-series ring over `R`. -/
def Chapter13PowerSeriesMaximalIdeal
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :
    Ideal (MvPowerSeries (Fin n) R) :=
  (IsLocalRing.maximalIdeal R).map
      (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) ⊔
    Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R))

/-- The finite-module filtration used in Lemma 13.1. -/
def Chapter13SpansModuloMaximalIdeal
    {A M : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] (n : ℕ) (m : Fin n → M) : Prop :=
  Submodule.span A (Set.range m) ⊔
      (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M) = ⊤

/-- Adic convergence of the partial sums of a series in a module. -/
def Chapter13AdicConvergesSeries
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (z : ℕ → M) (x : M) : Prop :=
  ∀ n : ℕ, Filter.Eventually
    (fun m : ℕ => Finset.sum (Finset.range m) z - x ∈ (I ^ n) • (⊤ : Submodule A M))
    (atTop : Filter ℕ)

/-- A series has its `n`th term in the `n`th adic layer. -/
def Chapter13AdicTermsVanish
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (z : ℕ → M) : Prop :=
  ∀ n : ℕ, z n ∈ (I ^ n) • (⊤ : Submodule A M)

/-! ### The three preliminary lemmas -/

theorem chapter13_finite_module_krull_intersection
    {A M : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hA : Chapter13CompleteNoetherianLocalRing A) :
    (∀ x : M, (∀ n : ℕ,
      x ∈ (IsLocalRing.maximalIdeal A) ^ n • (⊤ : Submodule A M)) → x = 0) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal A) M := by
  letI instNoetherian : IsNoetherianRing A := hA.1
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx' : x ∈ (⨅ n : ℕ,
        (IsLocalRing.maximalIdeal A) ^ n • (⊤ : Submodule A M)) :=
      by exact (Submodule.mem_iInf _).mpr hx
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing
      (I := IsLocalRing.maximalIdeal A) (M := M)
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top] at hx'
    exact hx'
  · obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
    let I : Ideal A := IsLocalRing.maximalIdeal A
    have hOfA : Function.Bijective (AdicCompletion.of I A) :=
      AdicCompletion.of_bijective_iff.mpr hA.2
    have hFbij : Function.Bijective
        (AdicCompletion.of I (Fin n → A)) := by
      constructor
      · intro x y hxy
        funext i
        apply hOfA.1
        have hcoord := congrArg (fun z =>
          (AdicCompletion.piEquivFin I n z) i) hxy
        simpa only [AdicCompletion.piEquivFin_apply,
          AdicCompletion.piEquivOfFintype_apply, AdicCompletion.pi,
          LinearMap.pi_apply, AdicCompletion.map_of, LinearMap.proj_apply] using hcoord
      · intro y
        choose x hx using fun i : Fin n => hOfA.2 ((AdicCompletion.piEquivFin I n y) i)
        refine ⟨fun i => x i, ?_⟩
        apply (AdicCompletion.piEquivFin I n).injective
        funext i
        have hi := hx i
        simpa only [AdicCompletion.piEquivFin_apply,
          AdicCompletion.piEquivOfFintype_apply, AdicCompletion.pi,
          LinearMap.pi_apply, AdicCompletion.map_of, LinearMap.proj_apply] using hi
    have hmap : Function.Surjective
        (AdicCompletion.map I f) := AdicCompletion.map_surjective I hf
    have hof : Function.Surjective (AdicCompletion.of I M) := by
      intro y
      obtain ⟨y', hy'⟩ := hmap y
      obtain ⟨x, hx⟩ := hFbij.2 y'
      refine ⟨f x, ?_⟩
      calc
        AdicCompletion.of I M (f x) =
            AdicCompletion.map I f (AdicCompletion.of I (Fin n → A) x) :=
          (AdicCompletion.map_of I f x).symm
        _ = AdicCompletion.map I f y' := by rw [hx]
        _ = y := hy'
    have hhaus : IsHausdorff I M := inferInstance
    letI : IsHausdorff I M := hhaus
    letI : IsPrecomplete I M := AdicCompletion.of_surjective_iff.mp hof
    exact (show IsAdicComplete I M from IsAdicComplete.mk)

theorem chapter13_finite_module_nakayama_generation
    {A M : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hA : Chapter13CompleteNoetherianLocalRing A) :
    ∀ (r : ℕ) (m : Fin r → M),
      Chapter13SpansModuloMaximalIdeal (A := A) r m →
        Submodule.span A (Set.range m) = ⊤ := by
  exact fun r m hm => by
    have hle : (⊤ : Submodule A M) ≤ Submodule.span A (Set.range m) := by
      apply Submodule.le_of_le_smul_of_le_jacobson_bot
      · exact Module.Finite.fg_top
      · exact IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A)
      · simpa [Chapter13SpansModuloMaximalIdeal, sup_comm] using hm
    exact top_unique hle

theorem chapter13_finite_module_adic_series
    {A M : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (z : ℕ → M) (hz : Chapter13AdicTermsVanish (IsLocalRing.maximalIdeal A) z) :
    ∃ x : M, Chapter13AdicConvergesSeries (IsLocalRing.maximalIdeal A) z x ∧
      ∀ e : Equiv.Perm ℕ,
        Chapter13AdicConvergesSeries (IsLocalRing.maximalIdeal A) (z ∘ e) x := by
  sorry

theorem chapter13_quotient_complete_noetherian_local
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (I : Ideal R)
    (hI : I ≠ ⊤) :
    @Chapter13CompleteNoetherianLocalRing (R ⧸ I) _
      (@IsLocalRing.of_surjective' R (R ⧸ I) _ _ _
        (Ideal.Quotient.nontrivial_iff.mpr hI) (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective) := by
  let S := R ⧸ I
  letI : IsLocalRing S :=
    @IsLocalRing.of_surjective' R S _ _ _
      (Ideal.Quotient.nontrivial_iff.mpr hI) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hS : IsAdicComplete (IsLocalRing.maximalIdeal R) S :=
    (chapter13_finite_module_krull_intersection
      (A := R) (M := S) ⟨inferInstance, hR⟩).2
  have hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
      IsLocalRing.maximalIdeal S := by
    simpa [S, Ideal.Quotient.algebraMap_eq] using
      (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective)
  have hS' : IsAdicComplete
      ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) S :=
    (IsAdicComplete.map_algebraMap_iff
      (I := IsLocalRing.maximalIdeal R) (M := S)).mpr hS
  rw [hmap] at hS'
  exact ⟨inferInstance, hS'⟩

theorem chapter13_power_series_complete_local
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (n : ℕ) :
    Chapter13CompleteNoetherianLocalRing (MvPowerSeries (Fin n) R) ∧
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R) =
        Chapter13PowerSeriesMaximalIdeal R n ∧
      Nonempty
        ((MvPowerSeries (Fin n) R ⧸ Chapter13PowerSeriesMaximalIdeal R n) ≃+*
          Chapter13ResidueRing R) := by
  sorry

/-- Evaluation data for the unique power-series homomorphism in Lemma 13.3. -/
def Chapter13PowerSeriesEvaluationData
    {R A : Type u} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    (n : ℕ) (σ : R →+* A) (x : Fin n → A)
    (F : MvPowerSeries (Fin n) R →+* A) : Prop :=
  F.comp (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) = σ ∧
    (∀ i : Fin n, F (MvPowerSeries.X i) = x i) ∧
    Chapter13AdicContinuous
      (Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R)
        (IsLocalRing.maximalIdeal R) ⊔
          Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) R)))
      (IsLocalRing.maximalIdeal A) F

theorem chapter13_power_series_evaluation_exists_unique
    {R A : Type u} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    (n : ℕ) (σ : R →+* A) (hσ : Chapter13LocalHom σ) (x : Fin n → A)
    (hx : ∀ i : Fin n, x i ∈ IsLocalRing.maximalIdeal A) :
    ∃! F : MvPowerSeries (Fin n) R →+* A,
      Chapter13PowerSeriesEvaluationData n σ x F := by
  sorry

theorem chapter13_power_series_evaluation_surjective_iff
    {R A : Type u} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    (n : ℕ) (σ : R →+* A) (x : Fin n → A)
    (F : MvPowerSeries (Fin n) R →+* A)
    (hF : Chapter13PowerSeriesEvaluationData n σ x F) :
    Function.Surjective F ↔
      Chapter13CoefficientPlusIdeal σ
        (Ideal.map σ (IsLocalRing.maximalIdeal R) ⊔
            Ideal.span (Set.range x)) := by
  sorry

/-! ### Coefficient rings and characteristic cases -/

/-- A coefficient-ring map, allowing the source to be a field or a DVR. -/
def Chapter13IsCoefficientRingMap
    {C A : Type u} [CommRing C] [CommRing A] [IsLocalRing C] [IsLocalRing A]
    (u : C →+* A) : Prop :=
  Chapter13LocalHom u ∧
    Function.Bijective ((Chapter13ResidueMap A).comp u) ∧
    IsNoetherianRing C ∧ IsAdicComplete (IsLocalRing.maximalIdeal C) C

/-- The two allowed coefficient-ring kinds. -/
def Chapter13CoefficientRingKind
    (C : Type u) [CommRing C] [IsDomain C] [IsLocalRing C] (p : ℕ) : Prop :=
  IsField C ∨
    (IsDomain C ∧ IsDiscreteValuationRing C ∧
      IsLocalRing.maximalIdeal C = Ideal.span {(p : C)})

/-- A coefficient ring realized as a complete local subring of the ambient ring. -/
structure Chapter13CoefficientRingSubring
    (A : Type u) [CommRing A] [IsLocalRing A] (p : ℕ) where
  carrier : Subring A
  [carrier_domain : IsDomain carrier]
  [carrier_local : IsLocalRing carrier]
  noetherian : IsNoetherianRing carrier
  complete : IsAdicComplete (IsLocalRing.maximalIdeal carrier) carrier
  maximalIdeal_comap :
    (IsLocalRing.maximalIdeal A).comap carrier.subtype =
      IsLocalRing.maximalIdeal carrier
  residue_equiv :
    (carrier ⧸ IsLocalRing.maximalIdeal carrier) ≃+* Chapter13ResidueRing A
  kind : Chapter13CoefficientRingKind carrier p

/-- A coefficient ring is a coefficient-ring map with one of the two source kinds. -/
def Chapter13IsCoefficientRing
    {C A : Type u} [CommRing C] [IsDomain C] [CommRing A] [IsLocalRing C] [IsLocalRing A]
    (p : ℕ) (u : C →+* A) : Prop :=
  Chapter13CoefficientRingKind C p ∧ Chapter13IsCoefficientRingMap u

theorem chapter13_contains_field_iff_equal_characteristic
    {A : Type u} [CommRing A] [IsLocalRing A] :
    Chapter13ContainsField A ↔
      Chapter13EqualCharacteristicZero A ∨
        ∃ p : ℕ, Chapter13EqualCharacteristicPrime A p := by
  constructor
  · rintro ⟨K⟩
    letI : Field K.carrier := K.field_carrier.toField
    obtain ⟨p, hp⟩ := CharP.exists K.carrier
    letI : CharP K.carrier p := hp
    rcases CharP.char_is_prime_or_zero K.carrier p with hpprime | hpzero
    · refine Or.inr ⟨p, hpprime, ?_, ?_⟩
      · exact (K.carrier.subtype.charP_iff_charP p).mp hp
      · exact ((Chapter13ResidueMap A).comp K.carrier.subtype
          |>.charP_iff_charP p).mp hp
    · subst p
      refine Or.inl ⟨(K.carrier.subtype.charP_iff_charP 0).mp hp, ?_⟩
      exact ((Chapter13ResidueMap A).comp K.carrier.subtype
        |>.charP_iff_charP 0).mp hp
  · rintro (hzero | ⟨p, hpprime, hpA, hpres⟩)
    · have hforall : ∀ I : Ideal A, I ≠ ⊤ →
          CharZero (A ⧸ I) := by
        letI : CharP (Chapter13ResidueRing A) 0 := hzero.2
        intro I hI
        let hIle : I ≤ IsLocalRing.maximalIdeal A :=
          IsLocalRing.le_maximalIdeal hI
        have hchar : CharP (A ⧸ I) 0 := by
          refine ⟨fun n => ?_⟩
          constructor
          · intro hn
            have hmem : (n : A) ∈ I := by
              exact (Ideal.Quotient.eq_zero_iff_mem.mp hn)
            have hres : (n : Chapter13ResidueRing A) = 0 := by
              exact (Ideal.Quotient.eq_zero_iff_mem.mpr (hIle hmem))
            exact (CharP.cast_eq_zero_iff
              (Chapter13ResidueRing A) 0 n).mp hres
          · intro hn
            have hn0 : n = 0 := (zero_dvd_iff.mp hn)
            subst n
            simp
        exact CharP.charP_to_charZero (A ⧸ I)
      obtain ⟨hQ⟩ : Nonempty (Algebra ℚ A) :=
        (EqualCharZero.nonempty_algebraRat_iff (R := A)).mpr hforall
      letI : Algebra ℚ A := hQ
      let f : ℚ →+* A := algebraMap ℚ A
      let e : ℚ ≃+* f.range :=
        RingEquiv.ofBijective f.rangeRestrict
          ⟨fun x y h => f.injective (congrArg Subtype.val h),
            f.rangeRestrict_surjective⟩
      have hfield : IsField f.range :=
        e.symm.toMulEquiv.isField (Field.toIsField ℚ)
      exact ⟨⟨f.range, hfield⟩⟩
    · letI : CharP A p := hpA
      letI : Fact (Nat.Prime p) := ⟨hpprime⟩
      let f : ZMod p →+* A := ZMod.castHom (dvd_refl p) A
      let e : ZMod p ≃+* f.range :=
        RingEquiv.ofBijective f.rangeRestrict
          ⟨fun x y h => f.injective (congrArg Subtype.val h),
            f.rangeRestrict_surjective⟩
      have hfield : IsField f.range :=
        e.symm.toMulEquiv.isField (Field.toIsField (ZMod p))
      exact ⟨⟨f.range, hfield⟩⟩

/-- Constants give the coefficient-field map in a formal power-series ring. -/
theorem chapter13_power_series_constants_are_coefficients
    (k : Type u) [Field k] :
    Function.Bijective
      ((Chapter13ResidueMap (PowerSeries k)).comp
        (PowerSeries.C : k →+* PowerSeries k)) := by
  let g : Chapter13ResidueRing (PowerSeries k) →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal (PowerSeries k)) PowerSeries.constantCoeff (by
      intro a ha
      rw [← PowerSeries.ker_coeff_eq_max_ideal] at ha
      exact ha)
  have hg (a : PowerSeries k) : g (Ideal.Quotient.mk _ a) = PowerSeries.constantCoeff a := by
    apply Ideal.Quotient.lift_mk
  have hC (a : k) : g ((Chapter13ResidueMap (PowerSeries k)).comp PowerSeries.C a) = a := by
    change g (Ideal.Quotient.mk _ (PowerSeries.C a)) = a
    rw [hg, PowerSeries.constantCoeff_C]
  constructor
  · intro a b h
    have hh := congrArg g h
    rw [hC, hC] at hh
    exact hh
  · intro y
    refine Quotient.inductionOn y (fun a => ⟨PowerSeries.constantCoeff a, ?_⟩)
    change Ideal.Quotient.mk _ (PowerSeries.C (PowerSeries.constantCoeff a)) =
      Ideal.Quotient.mk _ a
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    rw [← PowerSeries.ker_coeff_eq_max_ideal]
    simp

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
