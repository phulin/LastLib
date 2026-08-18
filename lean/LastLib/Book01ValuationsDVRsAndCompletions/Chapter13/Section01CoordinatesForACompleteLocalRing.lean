import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section04HenselianLocalRings
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.CharP.MixedCharZero
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.RingHom
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
  let instNoetherian : IsNoetherianRing A := hA.1
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
    let : IsHausdorff I M := hhaus
    let : IsPrecomplete I M := AdicCompletion.of_surjective_iff.mp hof
    exact (show IsAdicComplete I M from IsAdicComplete.mk)

theorem chapter13_finite_module_nakayama_generation
    {A M : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (_hA : Chapter13CompleteNoetherianLocalRing A) :
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
  classical
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let instComplete : IsAdicComplete I M :=
    (chapter13_finite_module_krull_intersection (A := A) (M := M) hA).2
  have hCauchy : ∀ {m n : ℕ}, m ≤ n →
      Finset.sum (Finset.range m) z ≡ Finset.sum (Finset.range n) z
        [SMOD (I ^ m • (⊤ : Submodule A M))] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact SModEq.rfl
    | succ n hmn ih =>
        have hpow : I ^ n ≤ I ^ m := Ideal.pow_le_pow_right hmn
        have hsub : I ^ n • (⊤ : Submodule A M) ≤ I ^ m • (⊤ : Submodule A M) :=
          Submodule.smul_mono hpow le_rfl
        have hzn : z n ∈ I ^ m • (⊤ : Submodule A M) := hsub (hz n)
        have hzero : (0 : M) ≡ z n [SMOD (I ^ m • (⊤ : Submodule A M))] := by
          rw [SModEq.sub_mem]
          simpa using (Submodule.neg_mem _ hzn)
        simpa [Finset.sum_range_succ] using ih.add hzero
  obtain ⟨x, hx⟩ := IsPrecomplete.prec (I := I) (M := M)
    (inferInstance : IsPrecomplete I M)
    (f := fun m => Finset.sum (Finset.range m) z) (by
    intro m n hmn
    exact hCauchy hmn)
  refine ⟨x, ?_, ?_⟩
  · intro n
    filter_upwards [eventually_ge_atTop n] with m hm
    have hxm := hx m
    have hmn : I ^ m • (⊤ : Submodule A M) ≤ I ^ n • (⊤ : Submodule A M) :=
      Submodule.smul_mono (Ideal.pow_le_pow_right hm) (by rfl)
    exact hmn (SModEq.sub_mem.mp hxm)
  · intro e n
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j < n, e.symm j < N := by
      induction n with
      | zero => exact ⟨0, by simp⟩
      | succ n ih =>
          obtain ⟨N, hN⟩ := ih
          refine ⟨max N (e.symm n + 1), ?_⟩
          intro j hj
          by_cases hje : j = n
          · subst j
            exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
          · have hjn : j < n := by omega
            exact lt_of_lt_of_le (hN j hjn) (Nat.le_max_left _ _)
    filter_upwards [eventually_ge_atTop N] with m hm
    have hfilter :
        (Finset.filter (fun i : ℕ => e i < n) (Finset.range m)).sum (z ∘ e) =
          (Finset.range n).sum z := by
      apply Finset.sum_nbij' (fun i => e i) (fun j => e.symm j)
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro j hj
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact Finset.mem_range.mpr ((hN j (Finset.mem_range.mp hj)).trans_le hm)
        · simpa using Finset.mem_range.mp hj
      · intro i hi
        simp
      · intro j hj
        simp
      · intro i hi
        rfl
    have htail :
        (Finset.filter (fun i : ℕ => ¬ e i < n) (Finset.range m)).sum (z ∘ e) ∈
          I ^ n • (⊤ : Submodule A M) := by
      apply Submodule.sum_mem
      intro i hi
      have hi' : n ≤ e i := Nat.le_of_not_gt (Finset.mem_filter.mp hi).2
      have hpow : I ^ (e i) ≤ I ^ n := Ideal.pow_le_pow_right hi'
      exact (Submodule.smul_mono hpow le_rfl) (hz (e i))
    have htailrel :
        (Finset.filter (fun i : ℕ => ¬ e i < n) (Finset.range m)).sum (z ∘ e) ≡ 0
          [SMOD (I ^ n • (⊤ : Submodule A M))] :=
      SModEq.sub_mem.mpr (by simpa using htail)
    have hperm :
        (Finset.range m).sum (z ∘ e) ≡ (Finset.range n).sum z
          [SMOD (I ^ n • (⊤ : Submodule A M))] := by
      rw [← hfilter]
      rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.range m) (fun i : ℕ => e i < n)]
      simpa [add_comm] using
        (SModEq.add (SModEq.rfl :
          (Finset.filter (fun i : ℕ => e i < n) (Finset.range m)).sum (z ∘ e) ≡
            (Finset.filter (fun i : ℕ => e i < n) (Finset.range m)).sum (z ∘ e)
              [SMOD (I ^ n • (⊤ : Submodule A M))]) htailrel)
    exact SModEq.sub_mem.mp (hperm.trans (hx n))

theorem chapter13_quotient_complete_noetherian_local
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (I : Ideal R)
    (hI : I ≠ ⊤) :
    @Chapter13CompleteNoetherianLocalRing (R ⧸ I) _
      (@IsLocalRing.of_surjective' R (R ⧸ I) _ _ _
        (Ideal.Quotient.nontrivial_iff.mpr hI) (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective) := by
  let S := R ⧸ I
  let : IsLocalRing S :=
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
    (hR : Chapter13CompleteNoetherianLocalRing R)
    (hA : Chapter13CompleteNoetherianLocalRing A)
    (n : ℕ) (σ : R →+* A) (hσ : Chapter13LocalHom σ) (x : Fin n → A)
    (hx : ∀ i : Fin n, x i ∈ IsLocalRing.maximalIdeal A) :
    ∃! F : MvPowerSeries (Fin n) R →+* A,
      Chapter13PowerSeriesEvaluationData n σ x F := by
  classical
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let instComplete : IsAdicComplete I A := hA.2
  let pEval : MvPolynomial (Fin n) R →+* A :=
    MvPolynomial.eval₂Hom σ x
  have hvarspoly : Ideal.map pEval
      (MvPolynomial.idealOfVars (Fin n) R) ≤ I := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span]
    apply Ideal.span_le.2
    rintro _ ⟨a, ⟨i, rfl⟩, rfl⟩
    rw [MvPolynomial.eval₂Hom_X']
    exact hx i
  have hpow : ∀ j : ℕ,
      Ideal.map pEval (MvPolynomial.idealOfVars (Fin n) R ^ j) ≤ I ^ j := by
    intro j
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hvarspoly j
  let qeval : ∀ j : ℕ, MvPolynomial (Fin n) R →+* A ⧸ I ^ j := fun j =>
    (Ideal.Quotient.mk (I ^ j)).comp pEval
  have hkill : ∀ j (y : MvPolynomial (Fin n) R),
      y ∈ MvPolynomial.idealOfVars (Fin n) R ^ j → qeval j y = 0 := by
    intro j y hy
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hpow j (Ideal.mem_map_of_mem pEval hy)
  let qlift : ∀ j : ℕ,
      (MvPolynomial (Fin n) R ⧸ MvPolynomial.idealOfVars (Fin n) R ^ j) →+*
        A ⧸ I ^ j :=
    fun j => Ideal.Quotient.lift _ (qeval j) (hkill j)
  let f : ∀ j : ℕ, MvPowerSeries (Fin n) R →+* A ⧸ I ^ j :=
    fun j => (qlift j).comp
      (MvPowerSeries.truncTotalAlgHom (Fin n) R j).toRingHom
  have hf : ∀ {m j : ℕ} (hmj : m ≤ j),
      (Ideal.Quotient.factorPow I hmj).comp (f j) = f m := by
    intro m j hmj
    ext z
    simp [f, qlift, qeval]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have hdiff :
        pEval (MvPowerSeries.truncTotal j z) -
          pEval (MvPowerSeries.truncTotal m z) ∈ I ^ m := by
      rw [← map_sub]
      exact hpow m (Ideal.mem_map_of_mem pEval
        (MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars
          hmj (le_refl m) z))
    exact hdiff
  let F : MvPowerSeries (Fin n) R →+* A :=
    @IsAdicComplete.liftRingHom (MvPowerSeries (Fin n) R) A _ _ I
      instComplete f hf
  have hmk : ∀ (j : ℕ) (z : MvPowerSeries (Fin n) R),
      Ideal.Quotient.mk (I ^ j) (F z) = f j z := by
    intro j z
    exact @IsAdicComplete.mk_liftRingHom
      (MvPowerSeries (Fin n) R) A _ _ I instComplete f hf j z
  have htruncC : ∀ (j : ℕ) (r : R), j ≠ 0 →
      MvPowerSeries.truncTotal (R := R) j
        (MvPowerSeries.C r : MvPowerSeries (Fin n) R) =
      MvPolynomial.C r := by
    intro j r hj
    ext d
    by_cases hd : d = 0
    · subst d
      simp [MvPowerSeries.coeff_truncTotal_eq_ite,
        MvPowerSeries.coeff_C, MvPolynomial.coeff_C, hj]
    · have hd' : ¬ 0 = d := by simpa [eq_comm] using hd
      simp [MvPowerSeries.coeff_truncTotal_eq_ite,
        MvPowerSeries.coeff_C, MvPolynomial.coeff_C, hd, hd']
  have hcoeff :
      F.comp (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) = σ := by
    apply DFunLike.coe_injective
    apply IsHausdorff.funext' I
    intro j r
    cases j with
    | zero =>
        rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        simp
    | succ j =>
        simpa [f, qlift, qeval, pEval, htruncC] using
          (hmk (j + 1) (MvPowerSeries.C r))
  have htruncX : ∀ (j : ℕ) (i : Fin n), 1 < j →
      MvPowerSeries.truncTotal (R := R) j
          (MvPowerSeries.X i : MvPowerSeries (Fin n) R) =
        (MvPolynomial.X i : MvPolynomial (Fin n) R) := by
    intro j i hj
    apply MvPolynomial.ext
    intro d
    rw [MvPowerSeries.coeff_truncTotal_eq_ite,
      MvPowerSeries.coeff_X, MvPolynomial.coeff_X]
    by_cases hd : d = (Finsupp.single i 1 : Fin n →₀ ℕ)
    · subst d
      simp [Finsupp.degree_single, hj]
    · have hd' : ¬ (Finsupp.single i 1 : Fin n →₀ ℕ) = d := by
        simpa [eq_comm] using hd
      simp [hd, hd']
  have htruncX_one : ∀ (i : Fin n),
      MvPowerSeries.truncTotal (R := R) 1
          (MvPowerSeries.X i : MvPowerSeries (Fin n) R) =
        (0 : MvPolynomial (Fin n) R) := by
    intro i
    apply MvPolynomial.ext
    intro d
    rw [MvPowerSeries.coeff_truncTotal_eq_ite,
      MvPowerSeries.coeff_X, MvPolynomial.coeff_zero]
    by_cases hd : d = (Finsupp.single i 1 : Fin n →₀ ℕ)
    · subst d
      simp [Finsupp.degree_single]
    · simp [hd]
  have hquot : ∀ (j : ℕ) (i : Fin n),
      (Ideal.Quotient.mk (I ^ j)) (F (MvPowerSeries.X i)) =
        (Ideal.Quotient.mk (I ^ j)) (x i) := by
    intro j i
    cases j with
    | zero =>
        rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        simp
    | succ j =>
        cases j with
        | zero =>
            have hfirst :
                (Ideal.Quotient.mk (I ^ (0 + 1)))
                    (F (MvPowerSeries.X i)) =
                  (Ideal.Quotient.mk (I ^ (0 + 1))) 0 := by
              simpa [f, qlift, qeval, pEval, htruncX_one i, pow_one] using
                (hmk 1 (MvPowerSeries.X i))
            calc
              (Ideal.Quotient.mk (I ^ (0 + 1))) (F (MvPowerSeries.X i)) =
                  (Ideal.Quotient.mk (I ^ (0 + 1))) 0 := hfirst
              _ = (Ideal.Quotient.mk (I ^ (0 + 1))) (x i) := by
                rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
                simpa [pow_one] using (Submodule.neg_mem I (hx i))
        | succ k =>
            have ht : MvPowerSeries.truncTotal (R := R) (k + 2)
                (MvPowerSeries.X i) =
              (MvPolynomial.X i : MvPolynomial (Fin n) R) :=
              htruncX (k + 2) i (by omega)
            simpa [f, qlift, qeval, pEval, ht] using
              (hmk (k + 2) (MvPowerSeries.X i))
  have hX : ∀ i : Fin n, F (MvPowerSeries.X i) = x i := by
    intro i
    rw [IsHausdorff.eq_iff_smodEq (I := I)]
    intro j
    rw [SModEq.sub_mem]
    have hmem : F (MvPowerSeries.X i) - x i ∈ I ^ j := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact hquot j i
    simpa only [smul_eq_mul, Ideal.mul_top] using hmem
  have hconst :
      Ideal.map F
          (Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R)
            (IsLocalRing.maximalIdeal R)) ≤
        IsLocalRing.maximalIdeal A := by
    rw [Ideal.map_map, hcoeff]
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change σ r ∈ IsLocalRing.maximalIdeal A
    rw [IsLocalRing.mem_maximalIdeal] at hr ⊢
    exact fun hu => hr (hσ.map_nonunit r hu)
  have hvars :
      Ideal.map F
          (Ideal.span (Set.range (MvPowerSeries.X : Fin n →
            MvPowerSeries (Fin n) R))) ≤
        IsLocalRing.maximalIdeal A := by
    rw [Ideal.map_span]
    apply Ideal.span_le.2
    rintro _ ⟨a, ⟨i, rfl⟩, rfl⟩
    simpa [hX i] using hx i
  have hJ :
      Ideal.map F
          (Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R)
            (IsLocalRing.maximalIdeal R) ⊔
            Ideal.span (Set.range (MvPowerSeries.X : Fin n →
              MvPowerSeries (Fin n) R))) ≤
        IsLocalRing.maximalIdeal A := by
    rw [Ideal.map_sup]
    exact sup_le hconst hvars
  let J : Ideal (MvPowerSeries (Fin n) R) :=
    Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R)
        (IsLocalRing.maximalIdeal R) ⊔
      Ideal.span (Set.range (MvPowerSeries.X : Fin n →
        MvPowerSeries (Fin n) R))
  have hcont : Chapter13AdicContinuous J (IsLocalRing.maximalIdeal A) F := by
    intro q
    refine ⟨q, ?_⟩
    intro z hz
    have hz' : F z ∈ Ideal.map F (J ^ q) :=
      Ideal.mem_map_of_mem F hz
    rw [Ideal.map_pow] at hz'
    exact (Ideal.pow_right_mono hJ q) hz'
  have hdata : Chapter13PowerSeriesEvaluationData n σ x F := by
    exact ⟨hcoeff, hX, hcont⟩
  refine ⟨F, hdata, ?_⟩
  intro G hG
  rcases hG with ⟨hGcoeff, hGX, hGcont⟩
  let ePoly : MvPolynomial (Fin n) R →+* A :=
    F.comp MvPolynomial.coeToMvPowerSeries.ringHom
  let gPoly : MvPolynomial (Fin n) R →+* A :=
    G.comp MvPolynomial.coeToMvPowerSeries.ringHom
  have hpoly : ePoly = gPoly := by
    apply MvPolynomial.ringHom_ext'
    · ext r
      have hcr : F (MvPowerSeries.C r) = G (MvPowerSeries.C r) := by
        calc
          F (MvPowerSeries.C r) = σ r := by
            simpa using DFunLike.congr_fun hcoeff r
          _ = G (MvPowerSeries.C r) := by
            simpa using (DFunLike.congr_fun hGcoeff r).symm
      simpa [ePoly, gPoly] using hcr
    · intro i
      have hxi : F (MvPowerSeries.X i) = G (MvPowerSeries.X i) :=
        (hX i).trans (hGX i).symm
      simpa [ePoly, gPoly] using hxi
  let P := MvPolynomial (Fin n) R
  let K : Ideal P := MvPolynomial.idealOfVars (Fin n) R
  let Kseries : Ideal (MvPowerSeries (Fin n) R) :=
    Ideal.span (Set.range (MvPowerSeries.X : Fin n →
      MvPowerSeries (Fin n) R))
  let e : MvPowerSeries (Fin n) R ≃ₐ[P] AdicCompletion K P :=
    MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) R
  have hKmap0 :
      Ideal.map
          (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) R).toRingEquiv.toRingHom
          (Ideal.span (Set.range (MvPowerSeries.X : Fin n →
            MvPowerSeries (Fin n) R))) =
        (MvPolynomial.idealOfVars (Fin n) R).map
          (algebraMap (MvPolynomial (Fin n) R)
            (AdicCompletion (MvPolynomial.idealOfVars (Fin n) R)
              (MvPolynomial (Fin n) R))) := by
    simp_rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    ext1
    simp [AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X,
      MvPowerSeries.toAdicCompletion_coe]
  have hKmap : Ideal.map e.toRingEquiv.toRingHom Kseries =
        K.map (algebraMap P (AdicCompletion K P)) := by
    simpa [e, K, Kseries] using hKmap0
  have heval : ∀ (m : ℕ) (z : MvPowerSeries (Fin n) R),
      AdicCompletion.eval K P m
          (e (z - (MvPowerSeries.truncTotal m z :
            MvPowerSeries (Fin n) R))) = 0 := by
    intro m z
    simp only [map_sub, AdicCompletion.eval_apply]
    dsimp [e, MvPowerSeries.toAdicCompletionAlgEquiv]
    simp [MvPowerSeries.toAdicCompletion_apply_eq_mk_truncTotal,
      MvPowerSeries.toAdicCompletion_coe]
  have he_mem : ∀ (m : ℕ) (z : MvPowerSeries (Fin n) R),
      e (z - (MvPowerSeries.truncTotal m z :
        MvPowerSeries (Fin n) R)) ∈
        K ^ m • (⊤ : Submodule P (AdicCompletion K P)) := by
    intro m z
    rw [AdicCompletion.pow_smul_top_eq_ker_eval
      (MvPolynomial.idealOfVars_fg (Fin n) R)]
    exact LinearMap.mem_ker.mpr (heval m z)
  have he_mem' : ∀ (m : ℕ) (z : MvPowerSeries (Fin n) R),
      e (z - (MvPowerSeries.truncTotal m z :
        MvPowerSeries (Fin n) R)) ∈
        (Ideal.map e.toRingEquiv.toRingHom Kseries) ^ m := by
    intro m z
    rw [hKmap, ← Ideal.map_pow]
    have hm := he_mem m z
    rw [Ideal.smul_top_eq_map] at hm
    change e (z - (MvPowerSeries.truncTotal m z :
        MvPowerSeries (Fin n) R)) ∈
      Ideal.map (algebraMap P (AdicCompletion K P)) (K ^ m) at hm
    exact hm
  have htail : ∀ (m : ℕ) (z : MvPowerSeries (Fin n) R),
      z - (MvPowerSeries.truncTotal m z :
        MvPowerSeries (Fin n) R) ∈ Kseries ^ m := by
    intro m z
    have hz :
        e (z - (MvPowerSeries.truncTotal m z :
          MvPowerSeries (Fin n) R)) ∈
        Ideal.map e.toRingEquiv.toRingHom (Kseries ^ m) := by
      rw [Ideal.map_pow]
      exact he_mem' m z
    have hz' := Ideal.mem_map_of_mem
      e.symm.toRingEquiv.toRingHom hz
    have hcomp :
        e.symm.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
          RingHom.id _ := by
      ext y
      simp
    rw [Ideal.map_map, hcomp, Ideal.map_id] at hz'
    simpa using hz'
  have hpoly_eval : ∀ p : MvPolynomial (Fin n) R,
      F (p : MvPowerSeries (Fin n) R) = G (p : MvPowerSeries (Fin n) R) := by
    intro p
    simpa [ePoly, gPoly] using DFunLike.congr_fun hpoly p
  have hKleJ : Kseries ≤ J := by
    exact le_sup_right
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro q z
  obtain ⟨mF, hmF⟩ := hcont q
  obtain ⟨mG, hmG⟩ := hGcont q
  let m := max mF mG
  let t : MvPolynomial (Fin n) R := MvPowerSeries.truncTotal m z
  have htailK : z - (t : MvPowerSeries (Fin n) R) ∈ Kseries ^ m := by
    simpa [t] using htail m z
  have htailJ : z - (t : MvPowerSeries (Fin n) R) ∈ J ^ m := by
    exact (Ideal.pow_right_mono hKleJ m) htailK
  have htailF : z - (t : MvPowerSeries (Fin n) R) ∈ J ^ mF := by
    exact (Ideal.pow_le_pow_right (Nat.le_max_left mF mG)) htailJ
  have htailG : z - (t : MvPowerSeries (Fin n) R) ∈ J ^ mG := by
    exact (Ideal.pow_le_pow_right (Nat.le_max_right mF mG)) htailJ
  have hFmem : F (z - (t : MvPowerSeries (Fin n) R)) ∈ I ^ q :=
    hmF _ htailF
  have hGmem : G (z - (t : MvPowerSeries (Fin n) R)) ∈ I ^ q :=
    hmG _ htailG
  have hdiff : G z - F z ∈ I ^ q := by
    have htaildiff :
        G (z - (t : MvPowerSeries (Fin n) R)) -
          F (z - (t : MvPowerSeries (Fin n) R)) ∈ I ^ q :=
      (I ^ q).sub_mem hGmem hFmem
    have hrel :
        G z - F z =
          G (z - (t : MvPowerSeries (Fin n) R)) -
            F (z - (t : MvPowerSeries (Fin n) R)) := by
      rw [map_sub, map_sub, hpoly_eval t]
      ring
    rw [hrel]
    exact htaildiff
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact hdiff

theorem chapter13_power_series_evaluation_surjective_iff
    {R A : Type u} [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
    (hR : Chapter13CompleteNoetherianLocalRing R)
    (hA : Chapter13CompleteNoetherianLocalRing A)
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
  residue_compatibility :
    ∀ c : carrier,
      residue_equiv (Ideal.Quotient.mk _ c) =
        Chapter13ResidueMap A (carrier.subtype c)
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
    let : Field K.carrier := K.field_carrier.toField
    obtain ⟨p, hp⟩ := CharP.exists K.carrier
    let : CharP K.carrier p := hp
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
        let : CharP (Chapter13ResidueRing A) 0 := hzero.2
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
      let : Algebra ℚ A := hQ
      let f : ℚ →+* A := algebraMap ℚ A
      let e : ℚ ≃+* f.range :=
        RingEquiv.ofBijective f.rangeRestrict
          ⟨fun x y h => f.injective (congrArg Subtype.val h),
            f.rangeRestrict_surjective⟩
      have hfield : IsField f.range :=
        e.symm.toMulEquiv.isField (Field.toIsField ℚ)
      exact ⟨⟨f.range, hfield⟩⟩
    · let : CharP A p := hpA
      let : Fact (Nat.Prime p) := ⟨hpprime⟩
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
