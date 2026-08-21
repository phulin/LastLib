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

private theorem chapter13_power_series_tail_mem_span_X_pow
    {R : Type*} [CommRing R] {σ : Type*} [Finite σ]
    (m : ℕ) (f : MvPowerSeries σ R)
    (hf : ∀ d : σ →₀ ℕ, Finsupp.degree d < m →
      MvPowerSeries.coeff d f = 0) :
    f ∈ (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) ^ m := by
  classical
  let P := MvPolynomial σ R
  let I := MvPolynomial.idealOfVars σ R
  let A := AdicCompletion I P
  let e := MvPowerSeries.toAdicCompletionAlgEquiv σ R
  have htrunc : MvPowerSeries.truncTotal m f = 0 := by
    ext d
    by_cases hd : Finsupp.degree d < m
    · rw [MvPowerSeries.coeff_truncTotal _ hd, hf d hd]
      simp
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (not_lt.mp hd)]
      simp
  have heval : (e f).val m = 0 := by
    rw [MvPowerSeries.toAdicCompletionAlgEquiv_apply,
      MvPowerSeries.toAdicCompletion_apply_eq_mk_truncTotal]
    simp [htrunc]
  have hker : e f ∈ I ^ m • (⊤ : Submodule P A) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := P)
      (MvPolynomial.idealOfVars_fg σ R)]
    exact LinearMap.mem_ker.mpr heval
  have hmap : Ideal.map e.toRingEquiv
      (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) =
      I.map (algebraMap P A) := by
    dsimp [e, I, P, A]
    simp_rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    ext1
    simp [AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X,
      MvPowerSeries.toAdicCompletion_coe]
  have hef : e f ∈ Ideal.map e.toRingEquiv
      ((Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) ^ m) := by
    rw [Ideal.map_pow, hmap]
    have hker' : e f ∈ (I.map (algebraMap P A)) ^ m := by
      rw [← Ideal.map_pow]
      change e f ∈ (I ^ m).map (algebraMap P A)
      rw [← Submodule.restrictScalars_mem P, ← Ideal.smul_top_eq_map]
      exact hker
    exact hker'
  obtain ⟨g, hg, hgf⟩ :=
    (Ideal.mem_map_iff_of_surjective e.toRingEquiv e.surjective).mp hef
  exact (e.injective hgf) ▸ hg

private theorem chapter13_power_series_adic_complete
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {σ : Type*} [Finite σ] :
    IsAdicComplete
      ((IsLocalRing.maximalIdeal R).map
          (MvPowerSeries.C : R →+* MvPowerSeries σ R) ⊔
        Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)))
      (MvPowerSeries σ R) := by
  classical
  let S := MvPowerSeries σ R
  let I : Ideal R := IsLocalRing.maximalIdeal R
  let XJ : Ideal S := Ideal.span (Set.range (MvPowerSeries.X : σ → S))
  let J : Ideal S := I.map (MvPowerSeries.C : R →+* S) ⊔ XJ
  let K : ℕ → Ideal S := fun q =>
    { carrier := {f | ∀ d : σ →₀ ℕ, Finsupp.degree d < q →
          MvPowerSeries.coeff d f ∈ I ^ (q - Finsupp.degree d)}
      zero_mem' := by
        intro d hd
        simp
      add_mem' := by
        intro f g hf hg d hd
        exact (I ^ (q - Finsupp.degree d)).add_mem (hf d hd) (hg d hd)
      smul_mem' := by
        intro c f hf d hd
        rw [show c • f = c * f by rfl, MvPowerSeries.coeff_mul]
        apply Ideal.sum_mem
        rintro ⟨i, j⟩ hij
        rw [Finset.mem_antidiagonal] at hij
        have hdeg : Finsupp.degree j ≤ Finsupp.degree d := by
          rw [← hij]
          simp only [map_add]
          omega
        have hjq : Finsupp.degree j < q := lt_of_le_of_lt hdeg hd
        have hpow : I ^ (q - Finsupp.degree j) ≤ I ^ (q - Finsupp.degree d) :=
          Ideal.pow_le_pow_right (by omega)
        exact (I ^ (q - Finsupp.degree d)).mul_mem_left _ (hpow (hf j hjq)) }
  have hCstep : ∀ q (a : S), a ∈ K q → ∀ r : R, r ∈ I →
      a * MvPowerSeries.C r ∈ K (q + 1) := by
    intro q a ha r hr d hd
    by_cases hlt : Finsupp.degree d < q
    · rw [MvPowerSeries.coeff_mul_C]
      have had := ha d hlt
      have he : q + 1 - Finsupp.degree d =
          (q - Finsupp.degree d) + 1 := by omega
      rw [he, pow_succ]
      exact Ideal.mul_mem_mul had hr
    · have hdeq : Finsupp.degree d = q := by omega
      rw [MvPowerSeries.coeff_mul_C, hdeq]
      simpa using I.mul_mem_left _ hr
  have Xmem : ∀ s : σ, MvPowerSeries.X s ∈ J := by
    intro s
    exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self s))
  have hXstep : ∀ q (a : S), a ∈ K q → ∀ s : σ,
      a * MvPowerSeries.X s ∈ K (q + 1) := by
    intro q a ha s d hd
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial]
    by_cases hle : Finsupp.single s 1 ≤ d
    · rw [if_pos hle]
      have hadd : d - Finsupp.single s 1 + Finsupp.single s 1 = d :=
        tsub_add_cancel_of_le hle
      have hdeg : Finsupp.degree (d - Finsupp.single s 1) + 1 =
          Finsupp.degree d := by
        have hdeg' := congrArg Finsupp.degree hadd
        simpa only [map_add, Finsupp.degree_single] using hdeg'
      have hlt : Finsupp.degree (d - Finsupp.single s 1) < q := by omega
      have := ha (d - Finsupp.single s 1) hlt
      have he : q + 1 - Finsupp.degree d =
          q - Finsupp.degree (d - Finsupp.single s 1) := by omega
      rw [he]
      simpa only [mul_one] using this
    · simp [hle]
  have hmapstep : ∀ q (a : S), a ∈ K q → ∀ b, b ∈ I.map
      (MvPowerSeries.C : R →+* S) → a * b ∈ K (q + 1) := by
    intro q a ha b hb
    change b ∈ Ideal.span (Set.image (MvPowerSeries.C : R →+* S) (I : Set R)) at hb
    induction hb using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨r, hr, rfl⟩ := hz
        exact hCstep q a ha r hr
    | zero => simp
    | add z w hz hw ihz ihw =>
        simpa [mul_add] using (K (q + 1)).add_mem ihz ihw
    | smul c z hz ih =>
        simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
          (K (q + 1)).mul_mem_left c ih
  have hXmapstep : ∀ q (a : S), a ∈ K q → ∀ b, b ∈ XJ →
      a * b ∈ K (q + 1) := by
    intro q a ha b hb
    change b ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → S)) at hb
    induction hb using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨s, rfl⟩ := hz
        exact hXstep q a ha s
    | zero => simp
    | add z w hz hw ihz ihw =>
        simpa [mul_add] using (K (q + 1)).add_mem ihz ihw
    | smul c z hz ih =>
        simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
          (K (q + 1)).mul_mem_left c ih
  have hKstep : ∀ q, K q * J ≤ K (q + 1) := by
    intro q
    rw [Ideal.mul_le]
    intro a ha b hb
    rcases Submodule.mem_sup.mp hb with ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    rw [mul_add]
    exact (K (q + 1)).add_mem (hmapstep q a ha b₁ hb₁)
      (hXmapstep q a ha b₂ hb₂)
  have hKpow : ∀ q, J ^ q ≤ K q := by
    intro q
    induction q with
    | zero =>
        intro f hf d hd
        omega
    | succ q ih =>
        rw [pow_succ]
        exact (Ideal.mul_mono ih le_rfl).trans (hKstep q)
  have hmapIp : I.map (MvPowerSeries.C : R →+* S) ≤ J :=
    le_sup_left
  have hmapIpPow : ∀ q, (I ^ q).map (MvPowerSeries.C : R →+* S) ≤ J ^ q := by
    intro q
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hmapIp q
  have hprod : ∀ (t : Finset σ) (g : σ → ℕ),
      (∀ s ∈ t, MvPowerSeries.X s ^ g s ∈ J ^ g s) →
        (∏ s ∈ t, MvPowerSeries.X s ^ g s) ∈ J ^ (∑ s ∈ t, g s) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro g hg
        simp
    | @insert s t hs ih =>
        intro g hg
        rw [Finset.prod_insert hs, Finset.sum_insert hs]
        have hmul := Ideal.mul_mem_mul (hg s (by simp)) (ih g (by
          intro u hu
          exact hg u (by simp [hu])))
        simpa [← pow_add] using hmul
  have hmonomial : ∀ d : σ →₀ ℕ,
      MvPowerSeries.monomial d (1 : R) ∈ J ^ Finsupp.degree d := by
    intro d
    have hp := hprod d.support (fun s => d s) (by
      intro s hs
      exact Ideal.pow_mem_pow (Xmem s) (d s))
    simpa [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.degree_apply] using hp
  have htrunc_mem : ∀ q (f : S),
      (∀ d : σ →₀ ℕ, Finsupp.degree d < q →
        MvPowerSeries.coeff d f ∈ I ^ (q - Finsupp.degree d)) →
      (MvPowerSeries.truncTotal q f : S) ∈ J ^ q := by
    intro q f hf
    rw [MvPowerSeries.truncTotal, MvPowerSeries.truncFinset_apply]
    change MvPolynomial.coeToMvPowerSeries.ringHom
        (∑ d ∈ (Finsupp.finite_of_degree_lt q).toFinset,
          MvPolynomial.monomial d (MvPowerSeries.coeff d f)) ∈ J ^ q
    rw [map_sum]
    apply Ideal.sum_mem
    intro d hd
    have hdeg : Finsupp.degree d < q := by
      simpa using hd
    simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coe_monomial]
    rw [MvPowerSeries.monomial_eq']
    have hc : MvPowerSeries.C (MvPowerSeries.coeff d f) ∈
        J ^ (q - Finsupp.degree d) :=
      hmapIpPow (q - Finsupp.degree d) (Ideal.mem_map_of_mem
        (MvPowerSeries.C : R →+* S) (hf d hdeg))
    have hm := hmonomial d
    have hmul := Ideal.mul_mem_mul hc hm
    simpa [MvPowerSeries.monomial_one_eq, Finsupp.prod, ← pow_add,
      Nat.sub_add_cancel hdeg.le] using hmul
  have hcoeff_to_mem : ∀ q (f : S),
      (∀ d : σ →₀ ℕ, Finsupp.degree d < q →
        MvPowerSeries.coeff d f ∈ I ^ (q - Finsupp.degree d)) → f ∈ J ^ q := by
    intro q f hf
    have htail : f - (MvPowerSeries.truncTotal q f : S) ∈ XJ ^ q := by
      apply chapter13_power_series_tail_mem_span_X_pow q
      intro d hd
      simp [MvPowerSeries.coeff_truncTotal _ hd]
    have htail' : f - (MvPowerSeries.truncTotal q f : S) ∈ J ^ q :=
      (Ideal.pow_right_mono le_sup_right q) htail
    have hsum := (J ^ q).add_mem htail' (htrunc_mem q f hf)
    simpa [sub_add_cancel] using hsum
  have hhaus : IsHausdorff J S := by
    refine ⟨?_⟩
    intro x hx
    apply MvPowerSeries.ext
    intro d
    have hcoeff : ∀ q : ℕ, MvPowerSeries.coeff d x ∈ I ^ q := by
      intro q
      have hxmem : x ∈ J ^ (Finsupp.degree d + q) := by
        simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using
          hx (Finsupp.degree d + q)
      by_cases hq : q = 0
      · subst q
        simp
      have hxd := hKpow (Finsupp.degree d + q) hxmem d
        (by omega)
      simpa [Nat.add_sub_cancel_left] using hxd
    have hd : MvPowerSeries.coeff d x = 0 := by
      apply IsHausdorff.haus hR.toIsHausdorff
      intro q
      rw [SModEq.zero]
      simpa [smul_eq_mul, Ideal.mul_top] using hcoeff q
    exact hd
  have hpre : IsPrecomplete J S := by
    refine ⟨?_⟩
    intro f hf
    let g : (σ →₀ ℕ) → ℕ → R := fun d k =>
      MvPowerSeries.coeff d (f (k + Finsupp.degree d))
    have hg : ∀ d, ∀ {m k : ℕ}, m ≤ k →
        g d m ≡ g d k [SMOD (I ^ m • (⊤ : Submodule R R))] := by
      intro d m k hmk
      by_cases hm : m = 0
      · subst m
        simp [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      rw [SModEq.sub_mem]
      have hfdiff : f (m + Finsupp.degree d) - f (k + Finsupp.degree d) ∈
          J ^ (m + Finsupp.degree d) := by
        simpa [smul_eq_mul, Ideal.mul_top] using
          (SModEq.sub_mem.mp (hf (Nat.add_le_add_right hmk _)))
      have hcoeff := hKpow (m + Finsupp.degree d) hfdiff d (by omega)
      simpa [g, map_sub, smul_eq_mul, Ideal.mul_top] using hcoeff
    have hconv : ∀ d, ∃ a : R, ∀ k,
        g d k ≡ a [SMOD (I ^ k • (⊤ : Submodule R R))] := by
      intro d
      exact IsPrecomplete.prec hR.toIsPrecomplete (hg d)
    choose a ha using hconv
    let L : S := fun d => a d
    have hmem : ∀ k, f k - L ∈ J ^ k := by
      intro k
      apply hcoeff_to_mem k (f k - L)
      intro d hd
      have hda := SModEq.sub_mem.mp (ha d (k - Finsupp.degree d))
      have hda' :
          g d (k - Finsupp.degree d) - a d ∈ I ^ (k - Finsupp.degree d) := by
        simpa [smul_eq_mul, Ideal.mul_top] using hda
      have hcoeff_eq : g d (k - Finsupp.degree d) =
          MvPowerSeries.coeff d (f k) := by
        simp [g, Nat.sub_add_cancel hd.le]
      rw [hcoeff_eq] at hda'
      change MvPowerSeries.coeff d (f k) - a d ∈
        I ^ (k - Finsupp.degree d) at hda'
      rw [map_sub, MvPowerSeries.coeff_apply]
      change f k d - a d ∈ I ^ (k - Finsupp.degree d)
      exact hda'
    refine ⟨L, ?_⟩
    intro k
    rw [SModEq.sub_mem]
    simpa [smul_eq_mul, Ideal.mul_top] using hmem k
  change IsAdicComplete J S
  exact { toIsHausdorff := hhaus, toIsPrecomplete := hpre }

private theorem chapter13_power_series_constantCoeff_ker
    {R : Type*} [CommRing R] {σ : Type*} [Finite σ] :
    RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries σ R →+* R) =
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
  classical
  have hXker : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ≤
      RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries σ R →+* R) := by
    apply Ideal.span_le.2
    rintro _ ⟨s, rfl⟩
    simp
  apply le_antisymm
  · intro f hf
    have hpow : f ∈
        (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) ^ 1 := by
      apply chapter13_power_series_tail_mem_span_X_pow (σ := σ) 1 f
      intro d hd
      change MvPowerSeries.constantCoeff f = 0 at hf
      have hdeg : Finsupp.degree d = 0 := by omega
      have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hdeg
      subst d
      simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hf
    simpa using hpow
  · intro f hf
    exact hXker hf

theorem chapter13_power_series_complete_local
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (n : ℕ) :
    Chapter13CompleteNoetherianLocalRing (MvPowerSeries (Fin n) R) ∧
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) R) =
        Chapter13PowerSeriesMaximalIdeal R n ∧
      Nonempty
        ((MvPowerSeries (Fin n) R ⧸ Chapter13PowerSeriesMaximalIdeal R n) ≃+*
          Chapter13ResidueRing R) := by
  classical
  let S := MvPowerSeries (Fin n) R
  let I : Ideal R := IsLocalRing.maximalIdeal R
  let XJ : Ideal S := Ideal.span (Set.range (MvPowerSeries.X : Fin n → S))
  let J : Ideal S := I.map (MvPowerSeries.C : R →+* S) ⊔ XJ
  have hcompleteJ : IsAdicComplete J S := by
    dsimp [J, I, XJ]
    exact chapter13_power_series_adic_complete (R := R) hR (σ := Fin n)
  have hker_const :
      RingHom.ker (MvPowerSeries.constantCoeff : S →+* R) = XJ := by
    dsimp [S, XJ]
    exact chapter13_power_series_constantCoeff_ker (R := R) (σ := Fin n)
  have hJ_le_comap : J ≤ I.comap
      (MvPowerSeries.constantCoeff : S →+* R) := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      change MvPowerSeries.constantCoeff (MvPowerSeries.C r) ∈ I
      simpa [I] using hr
    · intro f hf
      change MvPowerSeries.constantCoeff f ∈ I
      have hfker : f ∈ RingHom.ker
          (MvPowerSeries.constantCoeff : S →+* R) := by
        rw [hker_const]
        exact hf
      have hzero : MvPowerSeries.constantCoeff f = 0 :=
        RingHom.mem_ker.mp hfker
      rw [hzero]
      exact I.zero_mem
  have hdecomp : ∀ f : S, MvPowerSeries.constantCoeff f ∈ I → f ∈ J := by
    intro f hc
    have htail : f - MvPowerSeries.C (MvPowerSeries.constantCoeff f) ∈ XJ := by
      rw [← hker_const]
      rw [RingHom.mem_ker]
      rw [map_sub, MvPowerSeries.constantCoeff_C]
      exact sub_self _
    have hcoef : MvPowerSeries.C (MvPowerSeries.constantCoeff f) ∈
        I.map (MvPowerSeries.C : R →+* S) :=
      Ideal.mem_map_of_mem (MvPowerSeries.C : R →+* S) hc
    have hsum : MvPowerSeries.C (MvPowerSeries.constantCoeff f) +
        (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) ∈
        I.map (MvPowerSeries.C : R →+* S) ⊔ XJ :=
      (I.map (MvPowerSeries.C : R →+* S) ⊔ XJ).add_mem
        (Ideal.mem_sup_left hcoef) (Ideal.mem_sup_right htail)
    change f ∈ I.map (MvPowerSeries.C : R →+* S) ⊔ XJ
    simpa [add_sub_cancel_left] using hsum
  have hmaxJ : IsLocalRing.maximalIdeal S = J := by
    ext f
    constructor
    · intro hf
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hf
      have hc : MvPowerSeries.constantCoeff f ∈ I := by
        change MvPowerSeries.constantCoeff f ∈ IsLocalRing.maximalIdeal R
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply hf
        rw [MvPowerSeries.isUnit_iff_constantCoeff]
        exact hu
      exact hdecomp f hc
    · intro hf
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hnonunit : MvPowerSeries.constantCoeff f ∈ nonunits R := by
        rw [← IsLocalRing.mem_maximalIdeal]
        exact hJ_le_comap hf
      exact (mem_nonunits_iff.mp hnonunit)
        (IsUnit.map (MvPowerSeries.constantCoeff : S →+* R) hu)
  let φ : S →+* Chapter13ResidueRing R :=
    (Chapter13ResidueMap R).comp (MvPowerSeries.constantCoeff : S →+* R)
  have hkerφ : RingHom.ker φ = J := by
    ext f
    constructor
    · intro hf
      change φ f = 0 at hf
      change Chapter13ResidueMap R (MvPowerSeries.constantCoeff f) = 0 at hf
      have hc : MvPowerSeries.constantCoeff f ∈ I := by
        change MvPowerSeries.constantCoeff f ∈ IsLocalRing.maximalIdeal R
        exact Ideal.Quotient.eq_zero_iff_mem.mp hf
      exact hdecomp f hc
    · intro hf
      change φ f = 0
      change Chapter13ResidueMap R (MvPowerSeries.constantCoeff f) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact hJ_le_comap hf
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPowerSeries.C r, ?_⟩
    change Chapter13ResidueMap R
      (MvPowerSeries.constantCoeff (MvPowerSeries.C r)) = y
    rw [MvPowerSeries.constantCoeff_C]
    exact hr
  have hresJ : Nonempty (S ⧸ J ≃+* Chapter13ResidueRing R) := by
    rw [← hkerφ]
    exact ⟨RingHom.quotientKerEquivOfSurjective hsurj⟩
  have hcomplete : Chapter13CompleteNoetherianLocalRing S := by
    refine ⟨inferInstance, ?_⟩
    rw [hmaxJ]
    exact hcompleteJ
  have hJdef : J = Chapter13PowerSeriesMaximalIdeal R n := by
    rfl
  have hmax : IsLocalRing.maximalIdeal S =
      Chapter13PowerSeriesMaximalIdeal R n := by
    rw [← hJdef]
    exact hmaxJ
  have hres : Nonempty
      ((S ⧸ Chapter13PowerSeriesMaximalIdeal R n) ≃+* Chapter13ResidueRing R) := by
    rw [← hJdef]
    exact hresJ
  simpa [S] using And.intro hcomplete (And.intro hmax hres)

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
  classical
  let S := MvPowerSeries (Fin n) R
  let K : Ideal S := Chapter13PowerSeriesMaximalIdeal R n
  let I : Ideal A :=
    Ideal.map σ (IsLocalRing.maximalIdeal R) ⊔
      Ideal.span (Set.range x)
  rcases hF with ⟨hcoeff, hX, hcont⟩
  have hKmap : Ideal.map F K ≤ I := by
    have hconst : Ideal.map F
        (Ideal.map (MvPowerSeries.C : R →+* S)
          (IsLocalRing.maximalIdeal R)) ≤ I := by
      rw [Ideal.map_map, hcoeff]
      exact le_sup_left
    have hvars : Ideal.map F
        (Ideal.span (Set.range (MvPowerSeries.X : Fin n → S))) ≤ I := by
      rw [Ideal.map_span]
      apply Ideal.span_le.2
      rintro _ ⟨a, ⟨i, rfl⟩, rfl⟩
      change F (MvPowerSeries.X i) ∈ I
      rw [hX i]
      exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))
    change Ideal.map F
        (Ideal.map (MvPowerSeries.C : R →+* S)
          (IsLocalRing.maximalIdeal R) ⊔
          Ideal.span (Set.range (MvPowerSeries.X : Fin n → S))) ≤ I
    rw [Ideal.map_sup]
    exact sup_le hconst hvars
  constructor
  · intro hsurj a
    obtain ⟨z, rfl⟩ := hsurj a
    let c := MvPowerSeries.constantCoeff z
    let t : S := z - MvPowerSeries.C c
    have ht : t ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin n → S)) := by
      rw [← chapter13_power_series_constantCoeff_ker]
      change MvPowerSeries.constantCoeff t = 0
      simp [t, c, MvPowerSeries.constantCoeff_C]
    have hFt : F t ∈ I := by
      apply hKmap
      exact Ideal.mem_map_of_mem F (Ideal.mem_sup_right ht)
    refine ⟨c, F t, hFt, ?_⟩
    have hCc : F (MvPowerSeries.C c) = σ c := by
      simpa using DFunLike.congr_fun hcoeff c
    calc
      F z = F (MvPowerSeries.C c + t) := by simp [t]
      _ = σ c + F t := by rw [map_add, hCc]
  · intro hplus
    have hplus' : ∀ a : A, ∃ r : R, ∃ j : A,
        j ∈ I ∧ a = σ r + j := by
      change ∀ a : A, ∃ r : R, ∃ j : A, j ∈ I ∧ a = σ r + j
      exact hplus
    intro a
    have hKmax : K ≤ Ideal.comap F (IsLocalRing.maximalIdeal A) := by
      intro k hk
      obtain ⟨d, hd⟩ := hcont 1
      change F k ∈ IsLocalRing.maximalIdeal A
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hpow : k ^ d ∈ K ^ d := Ideal.pow_mem_pow hk d
      have hFpow := hd (k ^ d) hpow
      have hnon : F k ^ d ∈ nonunits A := by
        rw [← IsLocalRing.mem_maximalIdeal]
        simpa [map_pow, pow_one] using hFpow
      exact (mem_nonunits_iff.mp hnon) (hu.pow d)
    have hImax : I ≤ IsLocalRing.maximalIdeal A := by
      apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        change σ r ∈ IsLocalRing.maximalIdeal A
        have hcr : MvPowerSeries.C r ∈ K := by
          exact Ideal.mem_sup_left (Ideal.mem_map_of_mem
            (MvPowerSeries.C : R →+* S) hr)
        have := hKmax hcr
        change F (MvPowerSeries.C r) ∈ IsLocalRing.maximalIdeal A at this
        have hcr' : F (MvPowerSeries.C r) = σ r := by
          simpa using DFunLike.congr_fun hcoeff r
        simpa only [hcr'] using this
      · apply Ideal.span_le.2
        rintro _ ⟨i, rfl⟩
        have hxi : MvPowerSeries.X i ∈ K :=
          Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))
        have := hKmax hxi
        simpa [hX i] using this
    have hS : Chapter13CompleteNoetherianLocalRing S := by
      let instNoetherian : IsNoetherianRing R := hR.1
      simpa [S] using
        (chapter13_power_series_complete_local R hR.2 n).1
    have hmax : IsLocalRing.maximalIdeal S = K := by
      let instNoetherian : IsNoetherianRing R := hR.1
      simpa [S, K] using
        (chapter13_power_series_complete_local R hR.2 n).2.1
    let ι := (IsLocalRing.maximalIdeal R) ⊕ Fin n
    let v : ι → A := Sum.elim (fun r => σ r.1) x
    let w : ι → S :=
      Sum.elim (fun r => MvPowerSeries.C r.1)
        (MvPowerSeries.X : Fin n → S)
    have hvw : ∀ i : ι, F (w i) = v i := by
      intro i
      cases i with
      | inl r =>
          simpa [w, v] using DFunLike.congr_fun hcoeff r.1
      | inr i => simpa [w, v] using hX i
    have hspanv : Ideal.span (Set.range v) = I := by
      apply le_antisymm
      · apply Ideal.span_le.2
        rintro _ ⟨i, rfl⟩
        cases i with
        | inl r =>
            exact Ideal.mem_sup_left (Ideal.mem_map_of_mem σ r.2)
        | inr i =>
            exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))
      · change I ≤ Ideal.span (Set.range v)
        apply sup_le
        · rw [Ideal.map_le_iff_le_comap]
          intro r hr
          change σ r ∈ Ideal.span (Set.range v)
          exact Ideal.subset_span ⟨Sum.inl ⟨r, hr⟩, rfl⟩
        · apply Ideal.span_le.2
          rintro _ ⟨i, rfl⟩
          exact Ideal.subset_span ⟨Sum.inr i, rfl⟩
    have hspanw : Ideal.span (Set.range w) = K := by
      apply le_antisymm
      · apply Ideal.span_le.2
        rintro _ ⟨i, rfl⟩
        cases i with
        | inl r =>
            exact Ideal.mem_sup_left (Ideal.mem_map_of_mem
              (MvPowerSeries.C : R →+* S) r.2)
        | inr i =>
            exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))
      · change K ≤ Ideal.span (Set.range w)
        apply sup_le
        · rw [Ideal.map_le_iff_le_comap]
          intro r hr
          change MvPowerSeries.C r ∈ Ideal.span (Set.range w)
          exact Ideal.subset_span ⟨Sum.inl ⟨r, hr⟩, rfl⟩
        · apply Ideal.span_le.2
          rintro _ ⟨i, rfl⟩
          exact Ideal.subset_span ⟨Sum.inr i, rfl⟩
    have happrox : ∀ m : ℕ, ∀ y : A, y ∈ I ^ m →
        ∃ z : S, z ∈ K ^ m ∧ y - F z ∈ I ^ (m + 1) := by
      intro m
      induction m with
      | zero =>
          intro y _
          obtain ⟨r, j, hj, hy⟩ := hplus' y
          refine ⟨MvPowerSeries.C r, by simp, ?_⟩
          have hcr : F (MvPowerSeries.C r) = σ r := by
            simpa using DFunLike.congr_fun hcoeff r
          rw [hy, hcr]
          simpa using hj
      | succ m ih =>
          intro y hy
          have hy' : y ∈ I ^ m • Ideal.span (Set.range v) := by
            simpa [hspanv, Ideal.smul_eq_mul, pow_succ] using hy
          obtain ⟨a, ha, hsum⟩ :=
            (Submodule.mem_ideal_smul_span_iff_exists_sum (I := I ^ m) v y).mp hy'
          choose z hzK hzE using fun i => ih (a i) (ha i)
          let zsum : S := a.support.sum (fun i => z i * w i)
          have hzsum : zsum ∈ K ^ (m + 1) := by
            apply Submodule.sum_mem
            intro i hi
            have hwi : w i ∈ K := by
              rw [← hspanw]
              exact Ideal.subset_span (Set.mem_range_self i)
            rw [pow_succ]
            exact Ideal.mul_mem_mul (hzK i) hwi
          have hres : y - F zsum ∈ I ^ (m + 2) := by
            have hterm : ∀ i ∈ a.support,
                (a i - F (z i)) * v i ∈ I ^ (m + 2) := by
              intro i hi
              have hvi : v i ∈ I := by
                rw [← hspanv]
                exact Ideal.subset_span (Set.mem_range_self i)
              rw [pow_succ]
              exact Ideal.mul_mem_mul (hzE i) hvi
            have hident : y - F zsum =
                a.support.sum (fun i => (a i - F (z i)) * v i) := by
              rw [← hsum]
              simp [zsum, Finsupp.sum, smul_eq_mul, map_sum, map_mul,
                hvw]
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            rw [hident]
            exact Submodule.sum_mem _ hterm
          exact ⟨zsum, hzsum, hres⟩
    obtain ⟨r₀, j₀, hj₀, ha₀⟩ := hplus' a
    have hbase : a - F (MvPowerSeries.C r₀) ∈ I ^ 1 := by
      have hcr : F (MvPowerSeries.C r₀) = σ r₀ := by
        simpa using DFunLike.congr_fun hcoeff r₀
      rw [ha₀, hcr]
      simpa using hj₀
    let State := fun m : ℕ =>
      {p : S × S //
        a - F p.1 ∈ I ^ (m + 1) ∧
        p.2 ∈ K ^ (m + 1) ∧
        a - F (p.1 + p.2) ∈ I ^ (m + 2)}
    let state : ∀ m : ℕ, State m :=
      Nat.rec (motive := fun m => State m)
        (let hq := happrox 1 (a - F (MvPowerSeries.C r₀)) hbase
         let q := Classical.choose hq
         ⟨(MvPowerSeries.C r₀, q), hbase,
           (Classical.choose_spec hq).1, by
             have heq : a - F (MvPowerSeries.C r₀ + q) =
                 a - F (MvPowerSeries.C r₀) - F q := by
               rw [map_add]
               ring
             rw [heq]
             simpa [q] using (Classical.choose_spec hq).2⟩)
        (fun m ih =>
          let hq := happrox (m + 2)
            (a - F (ih.1.1 + ih.1.2)) ih.2.2.2
          let q := Classical.choose hq
          ⟨(ih.1.1 + ih.1.2, q), ih.2.2.2,
            (Classical.choose_spec hq).1, by
              have heq : a - F (ih.1.1 + ih.1.2 + q) =
                  a - F (ih.1.1 + ih.1.2) - F q := by
                rw [map_add]
                ring
              rw [heq]
              simpa [q] using (Classical.choose_spec hq).2⟩)
    let z : ℕ → S := fun m =>
      match m with
      | 0 => MvPowerSeries.C r₀
      | m + 1 => (state m).1.2
    have hz : Chapter13AdicTermsVanish
        (IsLocalRing.maximalIdeal S) z := by
      intro m
      cases m with
      | zero => simp [z]
      | succ m =>
          simpa [z, hmax] using (state m).2.2.1
    obtain ⟨q, hqconv, _⟩ := chapter13_finite_module_adic_series hS z hz
    have hstate : ∀ m : ℕ,
        (state (Nat.succ m)).1.1 = (state m).1.1 + (state m).1.2 := by
      intro m
      rfl
    have hpartial : ∀ m : ℕ,
        (Finset.range (m + 1)).sum z = (state m).1.1 := by
      intro m
      induction m with
      | zero => simp [z, state]
      | succ m ih =>
          calc
            (Finset.range (m.succ + 1)).sum z =
                (Finset.range (m + 1)).sum z + z (m + 1) := by
              simpa [Nat.succ_eq_add_one] using
                (Finset.sum_range_succ z (m + 1))
            _ = (state m).1.1 + z (m + 1) := by rw [ih]
            _ = (state m).1.1 + (state m).1.2 := by rfl
            _ = (state (Nat.succ m)).1.1 := (hstate m).symm
    have hpartial_next : ∀ m : ℕ,
        (Finset.range (m + 2)).sum z =
          (state m).1.1 + (state m).1.2 := by
      intro m
      calc
        (Finset.range (m + 2)).sum z =
            (Finset.range (m + 1)).sum z + z (m + 1) := by
          simpa [show m + 2 = (m + 1) + 1 by omega] using
            (Finset.sum_range_succ z (m + 1))
        _ = (state m).1.1 + z (m + 1) := by rw [hpartial]
        _ = (state m).1.1 + (state m).1.2 := by rfl
    refine ⟨q, ?_⟩
    let _ : IsHausdorff (IsLocalRing.maximalIdeal A) A :=
      hA.2.toIsHausdorff
    apply (IsHausdorff.eq_iff_smodEq
      (I := IsLocalRing.maximalIdeal A)).2
    intro q'
    rw [SModEq.sub_mem]
    obtain ⟨d, hd⟩ := hcont q'
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (hqconv d))
    let k := max N (max d (q' + 2))
    have hk := hN k (le_max_left _ _)
    have hlarge : max d (q' + 2) ≤ k := le_max_right _ _
    have hkpos : 2 ≤ k := by omega
    let m := k - 2
    have hmplus : m + 2 = k := Nat.sub_add_cancel hkpos
    have hsumK :
        (Finset.range k).sum z - q ∈
          (IsLocalRing.maximalIdeal S) ^ d := by
      simpa [smul_eq_mul, Ideal.mul_top] using hk
    have hqK : q - (Finset.range k).sum z ∈ K ^ d := by
      rw [← hmax]
      simpa only [neg_sub] using
        (Submodule.neg_mem _ hsumK)
    have hcontq := hd _ hqK
    have hres := (state m).2.2.2
    have hres' : a - F ((Finset.range k).sum z) ∈ I ^ k := by
      have hsum_eq : (Finset.range k).sum z =
          (state m).1.1 + (state m).1.2 := by
        calc
          (Finset.range k).sum z =
              (Finset.range (m + 2)).sum z := by rw [hmplus]
          _ = (state m).1.1 + (state m).1.2 := hpartial_next m
      rw [hsum_eq]
      simpa [hmplus] using hres
    have hresA : a - F ((Finset.range k).sum z) ∈
        (IsLocalRing.maximalIdeal A) ^ k :=
      (Ideal.pow_right_mono hImax k) hres'
    have hqle : q' ≤ k := by omega
    have hres'' : a - F ((Finset.range k).sum z) ∈
        (IsLocalRing.maximalIdeal A) ^ q' :=
      (Ideal.pow_le_pow_right hqle) hresA
    have hdiff : F q - a ∈ (IsLocalRing.maximalIdeal A) ^ q' := by
      have h₁ : F q - F ((Finset.range k).sum z) ∈
          (IsLocalRing.maximalIdeal A) ^ q' := by
        simpa [map_sub] using hcontq
      have hresneg : F ((Finset.range k).sum z) - a ∈
          (IsLocalRing.maximalIdeal A) ^ q' := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (Submodule.neg_mem _ hres'')
      have hadd := (IsLocalRing.maximalIdeal A ^ q').add_mem h₁ hresneg
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd
    simpa [smul_eq_mul, Ideal.mul_top] using hdiff

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
