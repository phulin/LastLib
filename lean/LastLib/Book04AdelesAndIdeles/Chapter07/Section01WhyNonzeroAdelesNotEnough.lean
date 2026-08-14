import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct WithZero

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! # 7.1 Why nonzero adeles are not enough -/

/-- A book-facing criterion for a unit of the adele ring.  The finite condition is the
restricted-product integrality condition, while the first conjunct records nonvanishing at the
infinite places. -/
theorem chapter07_adele_unit_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (x : chapter07AdeleRing R K) :
    IsUnit x ↔
      (∀ v : NumberField.InfinitePlace K, x.1 v ≠ 0) ∧
        (∀ v : chapter07FinitePlace R, x.2 v ≠ 0) ∧
        ∀ᶠ v : chapter07FinitePlace R in cofinite, Valued.v (x.2 v) = 1 := by
  change IsUnit (x.1, x.2) ↔ _
  rw [Prod.isUnit_iff]
  constructor
  · intro hx
    have hxi := hx.1
    have hxf := hx.2
    change IsUnit (fun v : NumberField.InfinitePlace K => x.1 v) at hxi
    rw [Pi.isUnit_iff] at hxi
    rw [IsDedekindDomain.FiniteAdeleRing.isUnit_iff] at hxf
    exact ⟨by simpa only [isUnit_iff_ne_zero] using hxi,
      by simpa only [isUnit_iff_ne_zero] using hxf.1, hxf.2⟩
  · rintro ⟨hxi, hxf, htail⟩
    refine ⟨?_, ?_⟩
    · change IsUnit (fun v : NumberField.InfinitePlace K => x.1 v)
      rw [Pi.isUnit_iff]
      simpa only [isUnit_iff_ne_zero] using hxi
    · rw [IsDedekindDomain.FiniteAdeleRing.isUnit_iff]
      exact ⟨by simpa only [isUnit_iff_ne_zero] using hxf, htail⟩

theorem chapter07_adele_unit_iff_local_units_at_almost_all_finite_places
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (x : chapter07AdeleRing R K) :
    IsUnit x ↔
      (∀ v : NumberField.InfinitePlace K, x.1 v ≠ 0) ∧
        (∀ v : chapter07FinitePlace R, x.2 v ≠ 0) ∧
        ∀ᶠ v : chapter07FinitePlace R in cofinite,
          Valued.v (x.2 v) = 1 := by
  exact chapter07_adele_unit_iff R K x

theorem chapter07_nonzero_adele_need_not_be_an_idele
    [NumberField ℚ] :
    ∃ x : chapter07AdeleRing ℤ ℚ,
      (∀ v : NumberField.InfinitePlace ℚ, x.1 v ≠ 0) ∧
      (∀ v : chapter07FinitePlace ℤ, x.2 v ≠ 0) ∧ ¬ IsUnit x := by
  classical
  let f : ∀ v : chapter07FinitePlace ℤ, chapter07LocalField ℤ ℚ v :=
    fun v => algebraMap ℤ (chapter07LocalField ℤ ℚ v)
      (Rat.HeightOneSpectrum.natGenerator v : ℤ)
  have hf_mem : ∀ᶠ v : chapter07FinitePlace ℤ in cofinite,
      f v ∈ chapter07LocalIntegerRing ℤ ℚ v := by
    filter_upwards [] with v
    exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem
      (R := ℤ) (K := ℚ) v (Rat.HeightOneSpectrum.natGenerator v)
  let x : chapter07AdeleRing ℤ ℚ :=
    ⟨(1 : NumberField.InfiniteAdeleRing ℚ), RestrictedProduct.mk f hf_mem⟩
  refine ⟨x, ?_, ?_, ?_⟩
  · intro v
    change (1 : v.Completion) ≠ 0
    exact one_ne_zero
  · intro v
    have hvp : Nat.Prime (Rat.HeightOneSpectrum.natGenerator v) :=
      Rat.HeightOneSpectrum.prime_natGenerator v
    have hne : (Rat.HeightOneSpectrum.natGenerator v : ℤ) ≠ 0 := by
      exact_mod_cast hvp.ne_zero
    change algebraMap ℚ (chapter07LocalField ℤ ℚ v)
        (algebraMap ℤ ℚ (Rat.HeightOneSpectrum.natGenerator v : ℤ)) ≠ 0
    exact (map_ne_zero_iff (algebraMap ℚ (chapter07LocalField ℤ ℚ v))
      (FaithfulSMul.algebraMap_injective ℚ (chapter07LocalField ℤ ℚ v))).2
      ((Int.cast_ne_zero (α := ℚ) (n :=
        (Rat.HeightOneSpectrum.natGenerator v : ℤ))).2 hne)
  · intro hx
    have htail := (IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp
      (Prod.isUnit_iff.mp hx).2).2
    have hlt : ∀ v : chapter07FinitePlace ℤ, Valued.v (f v) ≠ 1 := by
      intro v
      have hval : Valued.v (f v) = v.valuation ℚ
          (Rat.HeightOneSpectrum.natGenerator v : ℚ) := by
        dsimp [f]
        rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
        simp only [Function.comp_apply]
        exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
          (Rat.HeightOneSpectrum.natGenerator v : ℚ)
      rw [hval]
      intro h
      have h' : v.valuation ℚ (algebraMap ℤ ℚ
          (Rat.HeightOneSpectrum.natGenerator v : ℤ)) = 1 := by simpa using h
      exact ((IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
        (K := ℚ) (v := v)).mp h')
        (by
          have hmap : (Rat.IsIntegralClosure.intEquiv ℤ)
              (Rat.HeightOneSpectrum.natGenerator v : ℤ) ∈
              v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) := by
            simpa using
              (Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mp (dvd_refl _)
          exact (Ideal.apply_mem_of_equiv_iff
            (I := v.asIdeal) (f := Rat.IsIntegralClosure.intEquiv ℤ)
            (x := (Rat.HeightOneSpectrum.natGenerator v : ℤ))).mp hmap)
    have hfin : {v : chapter07FinitePlace ℤ | Valued.v (f v) ≠ 1}.Finite :=
      eventually_cofinite.mp htail
    let _ : Infinite (chapter07FinitePlace ℤ) :=
      Infinite.of_injective
        (fun p : Nat.Primes => (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p)
        (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective
    exact (Set.infinite_univ (α := chapter07FinitePlace ℤ))
      (by simpa [hlt] using hfin)

/-- The finite adele which is equal to a chosen rational prime at one finite place and to one
everywhere else.  This is the moving-prime family used to test the inherited topology. -/
noncomputable def chapter07MovingPrimeAdele (p : Nat.Primes) :
    chapter07AdeleRing ℤ ℚ :=
  by
    classical
    exact
      ⟨(1 : NumberField.InfiniteAdeleRing ℚ),
        RestrictedProduct.mk
          (fun v : chapter07FinitePlace ℤ =>
            if h : v = (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p then
              h.symm ▸
                Padic.adicCompletionEquiv ℤ p
                  (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ))
            else 1)
          (by
            filter_upwards [eventually_cofinite_ne
              ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p)] with v hv
            simp [hv])⟩

theorem chapter07_moving_prime_adele_component_at_prime (p : Nat.Primes) :
      (chapter07MovingPrimeAdele p).2
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) =
      Padic.adicCompletionEquiv ℤ p
        (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ)) := by
  classical
  change (if h : (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p =
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p then
      h.symm ▸ Padic.adicCompletionEquiv ℤ p
        (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ)) else 1) = _
  simp

theorem chapter07_moving_prime_adele_component_away_from_prime
    (p : Nat.Primes) (v : chapter07FinitePlace ℤ)
    (hv : v ≠ (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) :
    (chapter07MovingPrimeAdele p).2 v = 1 := by
  classical
  change (if h : v = (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p then
      h.symm ▸ Padic.adicCompletionEquiv ℤ p
        (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ)) else 1) = 1
  simp [hv]

theorem chapter07_moving_prime_adele_is_unit (p : Nat.Primes) :
    IsUnit (chapter07MovingPrimeAdele p) := by
  classical
  rw [chapter07_adele_unit_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro v
    change (1 : v.Completion) ≠ 0
    exact one_ne_zero
  · intro v
    by_cases hv : v = (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p
    · subst hv
      rw [chapter07_moving_prime_adele_component_at_prime]
      intro h
      have h' : algebraMap ℚ (ℚ_[p]) (p.1 : ℚ) = 0 := by
        simpa using congrArg (Padic.adicCompletionEquiv ℤ p).symm h
      have hp0 : (p.1 : ℚ) = 0 :=
        (FaithfulSMul.algebraMap_injective ℚ (ℚ_[p])) h'
      have hp_pos : (0 : ℚ) < p.1 := by exact_mod_cast p.2.pos
      exact (ne_of_gt hp_pos) hp0
    · rw [chapter07_moving_prime_adele_component_away_from_prime p v hv]
      exact one_ne_zero
  · filter_upwards [eventually_cofinite_ne
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p)] with v hv
    rw [chapter07_moving_prime_adele_component_away_from_prime p v hv]
    simp

/-- The moving-prime family viewed as ideles, using the canonical unit constructor. -/
noncomputable def chapter07MovingPrimeIdele (p : Nat.Primes) :
    chapter07IdeleGroup ℤ ℚ :=
  (chapter07_moving_prime_adele_is_unit p).unit

@[simp]
theorem chapter07MovingPrimeIdele_val (p : Nat.Primes) :
    (chapter07MovingPrimeIdele p : chapter07AdeleRing ℤ ℚ) =
      chapter07MovingPrimeAdele p := by
  exact (chapter07_moving_prime_adele_is_unit p).unit_spec

theorem chapter07_moving_prime_adele_tendsto_one :
    Tendsto chapter07MovingPrimeAdele cofinite
      (𝓝 (1 : chapter07AdeleRing ℤ ℚ)) := by
  apply (Prod.tendsto_iff chapter07MovingPrimeAdele (1 : chapter07AdeleRing ℤ ℚ)).mpr
  constructor
  · exact tendsto_const_nhds
  · rw [tendsto_nhds]
    intro U hUopen hUone
    have hA : ∀ v : chapter07FinitePlace ℤ,
        IsOpen (chapter07LocalIntegerRing ℤ ℚ v :
          Set (chapter07LocalField ℤ ℚ v)) := by
      intro v
      exact Valued.isOpen_valuationSubring _
    rcases chapter07_restrictedProduct_basicOpen_basis_shared
      (fun v : chapter07FinitePlace ℤ => chapter07LocalField ℤ ℚ v)
      (fun v : chapter07FinitePlace ℤ => chapter07LocalIntegerRing ℤ ℚ v)
      hA (1 : chapter07FiniteAdeleRing ℤ ℚ) U (hUopen.mem_nhds hUone) with
      ⟨S, hS, V, hV, h1B, hBU⟩
    have hbad : {p : Nat.Primes |
        (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p ∈ S}.Finite :=
      hS.preimage (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective.injOn
    filter_upwards [hbad.compl_mem_cofinite] with p hp
    apply hBU
    constructor
    · intro v hv
      by_cases hvp : v =
          (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p
      · exact (hp (by simpa [hvp] using hv)).elim
      · change (chapter07MovingPrimeAdele p).2 v ∈ V v
        rw [chapter07_moving_prime_adele_component_away_from_prime p v hvp]
        simpa only [Pi.one_apply] using! h1B.1 v hv
    · intro v hv
      by_cases hvp : v =
          (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p
      · subst v
        change (chapter07MovingPrimeAdele p).2
          ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) ∈
          chapter07LocalIntegerRing ℤ ℚ
            ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p)
        rw [chapter07_moving_prime_adele_component_at_prime]
        have hmem := (PadicInt.adicCompletionIntegersEquiv ℤ p
          (p.1 : ℤ_[p])).property
        convert hmem using 1
        rw [PadicInt.coe_adicCompletionIntegersEquiv_apply]
        simp
      · change (chapter07MovingPrimeAdele p).2 v ∈
          chapter07LocalIntegerRing ℤ ℚ v
        rw [chapter07_moving_prime_adele_component_away_from_prime p v hvp]
        exact (chapter07LocalIntegerRing ℤ ℚ v).one_mem

/-- The moving-prime family converges to one for the additive topology pulled back to the units. -/
def chapter07NaiveIdeleTendsto
    {ι : Type*} (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (f : ι → chapter07IdeleGroup R K)
    (l : Filter ι) (x : chapter07IdeleGroup R K) : Prop :=
  Tendsto f l (@nhds (chapter07IdeleGroup R K)
    (chapter07NaiveIdeleTopology R K) x)

theorem chapter07_moving_prime_naive_tendsto_one :
    chapter07NaiveIdeleTendsto ℤ ℚ chapter07MovingPrimeIdele cofinite 1 := by
  change Tendsto chapter07MovingPrimeIdele cofinite
    (@nhds (chapter07IdeleGroup ℤ ℚ)
      (chapter07NaiveIdeleTopology ℤ ℚ) 1)
  rw [nhds_induced, tendsto_comap_iff]
  simpa [Function.comp_def, chapter07MovingPrimeIdele_val] using
    chapter07_moving_prime_adele_tendsto_one

theorem chapter07_moving_prime_inverse_component_at_prime (p : Nat.Primes) :
    ((chapter07MovingPrimeIdele p)⁻¹ : chapter07IdeleGroup ℤ ℚ).1.2
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) =
      Padic.adicCompletionEquiv ℤ p
        (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ))⁻¹ := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p
  have hcoord : (chapter07MovingPrimeIdele p).1.2 v =
      Padic.adicCompletionEquiv ℤ p
        (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ)) := by
    rw [show (chapter07MovingPrimeIdele p).1.2 v =
        (chapter07MovingPrimeAdele p).2 v by
      rw [chapter07MovingPrimeIdele_val]]
    exact chapter07_moving_prime_adele_component_at_prime p
  have h := congrArg (fun a : chapter07AdeleRing ℤ ℚ => a.2 v)
    (chapter07MovingPrimeIdele p).val_inv
  change (chapter07MovingPrimeIdele p).1.2 v *
      ((chapter07MovingPrimeIdele p)⁻¹ : chapter07IdeleGroup ℤ ℚ).1.2 v = 1 at h
  rw [hcoord] at h
  have hmul :
      Padic.adicCompletionEquiv ℤ p
          (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ)) *
        ((chapter07MovingPrimeIdele p)⁻¹ : chapter07IdeleGroup ℤ ℚ).1.2 v = 1 := by
    simpa [v] using h
  simpa [v] using eq_inv_of_mul_eq_one_right hmul

/-- Inversion is not continuous for the naive subspace topology. -/
theorem chapter07_naive_idele_inversion_not_continuous :
    ¬ @Continuous (chapter07IdeleGroup ℤ ℚ) (chapter07IdeleGroup ℤ ℚ)
      (chapter07NaiveIdeleTopology ℤ ℚ) (chapter07NaiveIdeleTopology ℤ ℚ)
      (fun x => x⁻¹) := by
  intro hcont
  have hinv : Tendsto (fun p : Nat.Primes =>
      (chapter07MovingPrimeIdele p)⁻¹) cofinite
      (@nhds (chapter07IdeleGroup ℤ ℚ)
        (chapter07NaiveIdeleTopology ℤ ℚ) 1) := by
    have h_at : Tendsto (fun x : chapter07IdeleGroup ℤ ℚ => x⁻¹)
        (@nhds (chapter07IdeleGroup ℤ ℚ)
          (chapter07NaiveIdeleTopology ℤ ℚ) 1)
        (@nhds (chapter07IdeleGroup ℤ ℚ)
          (chapter07NaiveIdeleTopology ℤ ℚ) 1) := by
      exact @Continuous.tendsto _ _
        (chapter07NaiveIdeleTopology ℤ ℚ)
        (chapter07NaiveIdeleTopology ℤ ℚ)
        (fun x : chapter07IdeleGroup ℤ ℚ => x⁻¹) hcont 1
    have h := h_at.comp
      chapter07_moving_prime_naive_tendsto_one
    simpa [Function.comp_def] using h
  have hval : @Continuous (chapter07IdeleGroup ℤ ℚ)
      (chapter07AdeleRing ℤ ℚ)
      (chapter07NaiveIdeleTopology ℤ ℚ) inferInstance
      (fun x => (x : chapter07AdeleRing ℤ ℚ)) :=
    continuous_induced_dom
  have hadele : Tendsto (fun p : Nat.Primes =>
      (((chapter07MovingPrimeIdele p)⁻¹ : chapter07IdeleGroup ℤ ℚ) :
        chapter07AdeleRing ℤ ℚ)) cofinite
      (𝓝 (1 : chapter07AdeleRing ℤ ℚ)) := by
    have hval_at : Tendsto (fun x : chapter07IdeleGroup ℤ ℚ =>
        (x : chapter07AdeleRing ℤ ℚ))
        (@nhds (chapter07IdeleGroup ℤ ℚ)
          (chapter07NaiveIdeleTopology ℤ ℚ) 1)
        (𝓝 (1 : chapter07AdeleRing ℤ ℚ)) := by
      exact @Continuous.tendsto _ _
        (chapter07NaiveIdeleTopology ℤ ℚ) inferInstance
        (fun x : chapter07IdeleGroup ℤ ℚ =>
          (x : chapter07AdeleRing ℤ ℚ)) hval 1
    exact hval_at.comp hinv
  have hfinite :=
    (Prod.tendsto_iff
      (fun p : Nat.Primes =>
        (((chapter07MovingPrimeIdele p)⁻¹ : chapter07IdeleGroup ℤ ℚ) :
          chapter07AdeleRing ℤ ℚ))
      (1 : chapter07AdeleRing ℤ ℚ)).mp hadele |>.2
  have hA : ∀ v : chapter07FinitePlace ℤ,
      IsOpen (chapter07LocalIntegerRing ℤ ℚ v :
        Set (chapter07LocalField ℤ ℚ v)) := by
    intro v
    exact Valued.isOpen_valuationSubring _
  have hBopen := chapter07_restrictedProduct_basicOpen_isOpen_shared
    (fun v : chapter07FinitePlace ℤ => chapter07LocalField ℤ ℚ v)
    (fun v : chapter07FinitePlace ℤ => chapter07LocalIntegerRing ℤ ℚ v)
    ∅ (Set.finite_empty : (∅ : Set (chapter07FinitePlace ℤ)).Finite)
    (fun _ => Set.univ) (fun _ => isOpen_univ) hA
  have hBone : (1 : chapter07FiniteAdeleRing ℤ ℚ) ∈
      chapter07RestrictedProductBasicOpenShared
        (fun v : chapter07FinitePlace ℤ => chapter07LocalField ℤ ℚ v)
        (fun v : chapter07FinitePlace ℤ => chapter07LocalIntegerRing ℤ ℚ v)
        ∅ (fun _ => Set.univ) := by
    constructor
    · intro v hv
      exact (hv.elim)
    · intro v hv
      exact (chapter07LocalIntegerRing ℤ ℚ v).one_mem
  have hev := (tendsto_nhds.mp hfinite) _ hBopen hBone
  have hfalse : ∀ᶠ p : Nat.Primes in cofinite, False := by
    filter_upwards [hev] with p hp
    have hmem := hp.2
      ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) (by simp)
    change ((chapter07MovingPrimeIdele p)⁻¹ : chapter07IdeleGroup ℤ ℚ).1.2
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) ∈
      chapter07LocalIntegerRing ℤ ℚ
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) at hmem
    rw [chapter07_moving_prime_inverse_component_at_prime p] at hmem
    have hnot : Padic.adicCompletionEquiv ℤ p
        (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ))⁻¹ ∉
        chapter07LocalIntegerRing ℤ ℚ
          ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) := by
      let v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p
      change Padic.adicCompletionEquiv ℤ p
          (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ))⁻¹ ∉
        chapter07LocalIntegerRing ℤ ℚ v
      have hlt : v.valuation ℚ (p.1 : ℚ) < 1 := by
        have hmap : (Rat.IsIntegralClosure.intEquiv ℤ)
            (p.1 : ℤ) ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) := by
          have hgen : Rat.HeightOneSpectrum.natGenerator v = p.1 := by
            exact congrArg Subtype.val
              ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply p)
          simpa [hgen] using
            (Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mp (dvd_refl _)
        have hmemR : (p.1 : ℤ) ∈ v.asIdeal :=
          (Ideal.apply_mem_of_equiv_iff
          (I := v.asIdeal) (f := Rat.IsIntegralClosure.intEquiv ℤ)
          (x := (p.1 : ℤ))).mp hmap
        exact (v.valuation_lt_one_iff_mem (K := ℚ) (p.1 : ℤ)).2 hmemR
      have hcoord :
          Padic.adicCompletionEquiv ℤ p
              (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ)) =
            algebraMap ℚ (chapter07LocalField ℤ ℚ v) (p.1 : ℚ) := by
        exact (Padic.adicCompletionEquiv ℤ p).commutes (p.1 : ℚ)
      have hcoord_inv :
          Padic.adicCompletionEquiv ℤ p
              ((algebraMap ℚ (ℚ_[p]) (p.1 : ℚ))⁻¹) =
            (algebraMap ℚ (chapter07LocalField ℤ ℚ v) (p.1 : ℚ))⁻¹ := by
        rw [map_inv₀, hcoord]
      have hpq : (p.1 : ℚ) ≠ 0 := by
        exact_mod_cast p.2.ne_zero
      have ha0 : algebraMap ℚ (chapter07LocalField ℤ ℚ v)
          (p.1 : ℚ) ≠ 0 :=
        (map_ne_zero_iff (algebraMap ℚ (chapter07LocalField ℤ ℚ v))
          (FaithfulSMul.algebraMap_injective ℚ (chapter07LocalField ℤ ℚ v))).2 hpq
      have hval : Valued.v (algebraMap ℚ (chapter07LocalField ℤ ℚ v)
          (p.1 : ℚ)) = v.valuation ℚ (p.1 : ℚ) := by
        rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
        simp only [Function.comp_apply]
        exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
          v (p.1 : ℚ)
      rw [IsDedekindDomain.HeightOneSpectrum.notMem_adicCompletionIntegers]
      rw [hcoord_inv]
      rw [(Valued.v : Valuation (chapter07LocalField ℤ ℚ v) ℤᵐ⁰).map_inv]
      rw [hval]
      have hpos : 0 < v.valuation ℚ (p.1 : ℚ) := by
        rw [← hval]
        exact (Valued.v : Valuation (chapter07LocalField ℤ ℚ v) ℤᵐ⁰).pos_iff.2 ha0
      exact (one_lt_inv₀ hpos).2 hlt
    exact hnot hmem
  rcases hfalse.exists with ⟨p, hp⟩
  exact hp

theorem chapter07_naive_idele_topology_is_not_a_topological_group :
    ¬ @IsTopologicalGroup (chapter07IdeleGroup ℤ ℚ)
      (chapter07NaiveIdeleTopology ℤ ℚ)
      (inferInstance : Group (chapter07IdeleGroup ℤ ℚ)) := by
  intro h
  exact chapter07_naive_idele_inversion_not_continuous h.continuous_inv

end

end LastLib.Book04AdelesAndIdeles.Chapter07
