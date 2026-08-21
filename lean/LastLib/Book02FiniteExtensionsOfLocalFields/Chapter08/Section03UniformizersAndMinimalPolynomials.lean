import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section01TheMeaningOfTotalRamification
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section02EisensteinCoefficientsAndValueBalance
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section06TheValuationRingInAFiniteCompleteExtension
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial
open scoped WithTop

/-! # 8.3. Every totally ramified extension comes from a uniformizer -/

theorem chapter08_valuation_subring_eq_range_of_integral_test
    {A K : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (v : AddValuation K (WithTop ℤ))
    (hintegral : ∀ x : K, IsIntegral A x ↔ 0 ≤ v x) :
    (v.toValuation.valuationSubring : Set K) = Set.range (algebraMap A K) := by
  let : IsIntegrallyClosed A := by infer_instance
  ext x
  constructor
  · intro hx
    have hv : 0 ≤ v x := by
      exact hx
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A)).mp
      ((hintegral x).2 hv)
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    have hv : 0 ≤ v (algebraMap A K a) :=
      (hintegral _).1 isIntegral_algebraMap
    change 0 ≤ v (algebraMap A K a)
    exact hv

theorem chapter08_valuation_subring_is_complete_of_integral_test
    {A K : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (v : AddValuation K (WithTop ℤ))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hintegral : ∀ x : K, IsIntegral A x ↔ 0 ≤ v x) :
    IsAdicComplete
      (IsLocalRing.maximalIdeal v.toValuation.valuationSubring)
      v.toValuation.valuationSubring := by
  let φ : A →+* v.toValuation.valuationSubring :=
    RingHom.codRestrict (algebraMap A K) _ (by
      intro a
      change 0 ≤ v (algebraMap A K a)
      exact (hintegral _).1 isIntegral_algebraMap)
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply IsFractionRing.injective A K
    simpa [φ] using congrArg (fun z : v.toValuation.valuationSubring => (z : K)) hab
  have hφsurj : Function.Surjective φ := by
    intro x
    have hxrange := chapter08_valuation_subring_eq_range_of_integral_test
      v hintegral
    have hxK : (x : K) ∈ (v.toValuation.valuationSubring : Set K) := x.property
    rw [hxrange] at hxK
    obtain ⟨a, ha⟩ := hxK
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha
  let e : A ≃+* v.toValuation.valuationSubring :=
    RingEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hcomp :=
    (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal A) e).mpr hcomplete
  rw [IsLocalRing.map_ringEquiv_maximalIdeal] at hcomp
  exact hcomp

/-! The Chapter 10 normalized-discreteness predicate determines the cyclic
value group required by Mathlib's rank-one discrete valuation interface. -/
theorem chapter08_rank_one_discrete_of_add_valuation
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hdiscrete :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation v) :
    Valuation.IsRankOneDiscrete v.toValuation := by
  let vk : Valuation K (Multiplicative (WithTop ℤ)ᵒᵈ) := v
  obtain ⟨π, hπ0, hπ, hv⟩ := hdiscrete
  have hone : ∀ z : ℕ, z • (1 : WithTop ℤ) = (z : WithTop ℤ) := by
    intro z
    induction z with
    | zero => simp
    | succ z ih =>
        rw [succ_nsmul, Nat.cast_succ, ih]
  have hnegcast : ∀ z : ℕ,
      (Int.negSucc z : WithTop ℤ) = -((z + 1 : ℕ) : WithTop ℤ) := by
    intro z
    simp [Int.negSucc_eq]
  have hpow : ∀ z : ℤ, v (π ^ z) = (z : WithTop ℤ) := by
    intro z
    cases z with
    | ofNat z =>
        change v (π ^ (z : ℤ)) = (z : WithTop ℤ)
        rw [zpow_natCast, v.map_pow, hπ, hone]
    | negSucc z =>
        rw [zpow_negSucc, v.map_inv, v.map_pow, hπ]
        rw [hnegcast z, hone]
  have hvg : MonoidWithZeroHom.valueGroup (.ofClass vk) = ⊤ := by
    apply top_unique
    intro u _hu
    have hu0 :
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)) : WithTop ℤ) ≠ ⊤ := by
      intro htop
      apply Units.ne_zero u
      change Multiplicative.ofAdd (OrderDual.toDual
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)))) =
        Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
      congr 1
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hu0
    apply MonoidWithZeroHom.mem_valueGroup
    refine ⟨π ^ n, ?_⟩
    change Multiplicative.ofAdd (OrderDual.toDual (v (π ^ n))) =
      (u : Multiplicative (WithTop ℤ)ᵒᵈ)
    rw [hpow n]
    exact congrArg (fun z : WithTop ℤ =>
      Multiplicative.ofAdd (OrderDual.toDual z)) hn
  let γ : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ :=
    Units.mk0 (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)))
      (by
        intro h
        have htop : (1 : WithTop ℤ) = ⊤ := congrArg (fun z =>
          OrderDual.ofDual (Multiplicative.toAdd z)) h
        exact (WithTop.coe_lt_top 1).ne htop)
  have honeD : ∀ z : ℕ,
      z • (OrderDual.toDual (1 : WithTop ℤ)) =
        OrderDual.toDual (z : WithTop ℤ) := by
    intro z
    exact congrArg OrderDual.toDual (hone z)
  have hγpow : ∀ n : ℤ,
      (γ ^ n : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ).val =
        Multiplicative.ofAdd (OrderDual.toDual (n : WithTop ℤ)) := by
    intro n
    cases n with
    | ofNat n =>
        simp [γ, zpow_natCast]
        change Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^ n =
          Multiplicative.ofAdd (OrderDual.toDual (n : WithTop ℤ))
        rw [← ofAdd_nsmul n (OrderDual.toDual (1 : WithTop ℤ))]
        congr 1
        exact honeD n
    | negSucc n =>
        simp [γ, zpow_negSucc]
        change (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^
            (n + 1))⁻¹ =
          Multiplicative.ofAdd (OrderDual.toDual
            (Int.negSucc n : WithTop ℤ))
        rw [hnegcast n]
        change (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^
            (n + 1))⁻¹ =
          Multiplicative.ofAdd
            (-(OrderDual.toDual ((n + 1 : ℕ) : WithTop ℤ)))
        rw [ofAdd_neg]
        rw [← ofAdd_nsmul (n + 1) (OrderDual.toDual (1 : WithTop ℤ))]
        congr 1
        exact honeD (n + 1)
  have hcyc : IsCyclic ((Multiplicative (WithTop ℤ)ᵒᵈ)ˣ) := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    refine ⟨γ, ?_⟩
    apply top_unique
    intro u _hu
    have hu0 :
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)) : WithTop ℤ) ≠ ⊤ := by
      intro htop
      apply Units.ne_zero u
      change Multiplicative.ofAdd (OrderDual.toDual
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)))) =
        Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
      congr 1
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hu0
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    apply Units.ext
    rw [hγpow]
    exact congrArg (fun z : WithTop ℤ =>
      Multiplicative.ofAdd (OrderDual.toDual z)) hn
  let : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass vk)) := by
    rw [hvg]
    exact (Subgroup.topEquiv.isCyclic :
      IsCyclic (⊤ : Subgroup ((Multiplicative (WithTop ℤ)ᵒᵈ)ˣ)) ↔
        IsCyclic ((Multiplicative (WithTop ℤ)ᵒᵈ)ˣ)).mpr hcyc
  let : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass vk)) := by
    rw [hvg]
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    refine ⟨γ, Subgroup.mem_top γ, ?_⟩
    intro hγ
    have hval := congrArg Units.val hγ
    simp [γ] at hval
  exact Valuation.IsRankOneDiscrete.mk' vk

theorem chapter08_value_one_generates_maximal_ideal
    {A K : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (v : AddValuation K (WithTop ℤ))
    (hdiscrete :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation v)
    (hintegral : ∀ x : K, IsIntegral A x ↔ 0 ≤ v x)
    (π : A) (hπ : v (algebraMap A K π) = 1) :
    IsLocalRing.maximalIdeal A = Ideal.span {π} := by
  let hvint : v.toValuation.Integers A := by
    refine {
      hom_inj := IsFractionRing.injective A K
      map_le_one := ?_
      exists_of_le_one := ?_ }
    · intro a
      change 0 ≤ v (algebraMap A K a)
      exact (hintegral _).1 isIntegral_algebraMap
    · intro x hx
      change 0 ≤ v x at hx
      obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A)).mp
        ((hintegral x).2 hx)
      exact ⟨a, ha⟩
  obtain ⟨_, _, _, hvalues⟩ := hdiscrete
  apply le_antisymm
  · intro a ha
    by_cases ha0 : a = 0
    · simp [ha0]
    have hnotunit : ¬ IsUnit a := by
      rw [IsLocalRing.mem_maximalIdeal] at ha
      exact ha
    have hlt : v.toValuation (algebraMap A K a) < 1 := by
      apply lt_of_le_of_ne (hvint.map_le_one a)
      intro heq
      exact hnotunit (hvint.isUnit_iff_valuation_eq_one.mpr heq)
    change (0 : WithTop ℤ) < v (algebraMap A K a) at hlt
    obtain ⟨z, hz⟩ := hvalues (algebraMap A K a)
      ((map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).2 ha0)
    have hzpos : (0 : ℤ) < z := by
      rw [hz] at hlt
      exact_mod_cast hlt
    have hzone : (1 : WithTop ℤ) ≤ (z : WithTop ℤ) := by
      exact_mod_cast (show (1 : ℤ) ≤ z by omega)
    have hle : v.toValuation (algebraMap A K a) ≤
        v.toValuation (algebraMap A K π) := by
      change OrderDual.toDual (v (algebraMap A K a)) ≤
        OrderDual.toDual (v (algebraMap A K π))
      rw [hz, hπ]
      change (1 : WithTop ℤ) ≤ (z : WithTop ℤ)
      exact hzone
    obtain ⟨b, hb⟩ := hvint.dvd_of_le hle
    exact Ideal.mem_span_singleton.mpr ⟨b, hb⟩
  · apply Ideal.span_le.mpr
    intro x hx
    have hxπ : x = π := Set.mem_singleton_iff.mp hx
    rw [hxπ]
    have hnotunit : ¬ IsUnit π := by
      intro hunit
      have hvπ := hvint.one_of_isUnit hunit
      change v (algebraMap A K π) = 0 at hvπ
      rw [hπ] at hvπ
      exact one_ne_zero hvπ
    exact (IsLocalRing.mem_maximalIdeal π).2 hnotunit

theorem chapter08_powers_linearlyIndependent_of_value_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (e : ℕ) (he : 0 < e)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvalues : ∀ x : K, x ≠ 0 → ∃ z : ℤ, vK x = z)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = e • vK x)
    (πL : L) (hπL : vL πL = 1) :
    LinearIndependent K (fun i : Fin e => πL ^ (i : ℕ)) := by
  classical
  let : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let terms : Fin e → L := fun i =>
    algebraMap K L (c i) * πL ^ (i : ℕ)
  have hterm_value (i : Fin e) (hci : c i ≠ 0) :
    ∃ z : ℤ,
        vL (terms i) =
          ((e : ℤ) * z + (i : ℤ) : WithTop ℤ) := by
    obtain ⟨z, hz⟩ := hvalues (c i) hci
    refine ⟨z, ?_⟩
    dsimp [terms]
    rw [vL.map_mul, hscale (c i) hci, vL.map_pow, hπL, hz]
    rw [← WithTop.coe_nsmul]
    congr 1
    norm_num [nsmul_eq_mul]
  have hdistinct (i j : Fin e) (hij : i ≠ j)
      (hci : c i ≠ 0) (hcj : c j ≠ 0) :
      vL (terms i) ≠ vL (terms j) := by
    intro heq
    obtain ⟨zi, hzi⟩ := hterm_value i hci
    obtain ⟨zj, hzj⟩ := hterm_value j hcj
    rw [hzi, hzj] at heq
    have heq' :
        (e : ℤ) * zi + (i : ℤ) = (e : ℤ) * zj + (j : ℤ) := by
      exact_mod_cast heq
    have hji_nat : (j : ℕ) ≠ (i : ℕ) := by
      intro h
      apply hij
      exact Fin.ext h.symm
    have hmod :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_term_values_are_distinct_modulo_degree
        (ω := fun z : ℕ => if z = (i : ℕ) then zi else zj)
        (a := fun k : Fin e => (k : ℕ)) i j hij
    apply hmod
    simpa [hji_nat] using congrArg (fun z : ℤ => z % (e : ℤ)) heq'
  by_contra hnot
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by
    by_contra hnone
    apply hnot
    intro i
    by_contra hci
    exact hnone ⟨i, hci⟩
  let s : Finset (Fin e) := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := ⟨i₀, by simp [s, hi₀]⟩
  obtain ⟨i₁, hi₁, hmin⟩ :=
    Finset.exists_min_image s (fun i => vL (terms i)) hs
  have hci₁ : c i₁ ≠ 0 := by simpa [s] using hi₁
  have hπL0 : πL ≠ 0 := by
    intro hzero
    have hbad := hπL
    rw [hzero, AddValuation.map_zero] at hbad
    simp at hbad
  have hterm₁ : terms i₁ ≠ 0 := by
    dsimp [terms]
    refine mul_ne_zero ?_ (pow_ne_zero _ hπL0)
    exact (map_ne_zero_iff (algebraMap K L)
      (FaithfulSMul.algebraMap_injective K L)).2 hci₁
  have hleast : ∀ j, j ≠ i₁ → vL (terms i₁) < vL (terms j) := by
    intro j hji
    by_cases hcj : c j = 0
    · dsimp [terms]
      rw [hcj, map_zero, zero_mul, AddValuation.map_zero]
      exact (vL.ne_top_iff.mpr hterm₁).lt_top
    · have hj : j ∈ s := by simp [s, hcj]
      have hle := hmin j hj
      have hneval := hdistinct i₁ j (Ne.symm hji) hci₁ hcj
      exact lt_of_le_of_ne hle hneval
  have hcancel :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.least_valued_term_does_not_cancel
      vL terms i₁ hleast hterm₁
  have hsum : (∑ i, terms i) = 0 := by
    simpa [terms, Algebra.smul_def] using hc
  have hnotop : vL (terms i₁) ≠ (⊤ : WithTop ℤ) :=
    vL.ne_top_iff.mpr hterm₁
  exfalso
  apply hnotop
  calc
    vL (terms i₁) = vL (∑ i, terms i) := hcancel.symm
    _ = vL 0 := by rw [hsum]
    _ = ⊤ := AddValuation.map_zero vL

theorem chapter08_uniformizer_maximal_ideal_map
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (_hfinite : Module.Finite A (integralClosure A L))
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Algebra vK.toValuation.valuationSubring vL.toValuation.valuationSubring]
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hintegralK : ∀ x : K, IsIntegral A x ↔ 0 ≤ vK x)
    (_hintegralL : ∀ x : L, IsIntegral A x ↔ 0 ≤ vL x)
    (e : ℕ)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = e • vK x)
    (hcoe : ∀ a : vK.toValuation.valuationSubring,
      ((algebraMap vK.toValuation.valuationSubring
          vL.toValuation.valuationSubring a :
            vL.toValuation.valuationSubring) : L) =
        algebraMap K L (a : K))
    (πL : L) (hπL : vL πL = 1) :
    Ideal.map (algebraMap vK.toValuation.valuationSubring
        vL.toValuation.valuationSubring)
      (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring) =
      (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring) ^ e := by
  have hdiscreteK0 := hdiscreteK
  let vk : Valuation K (Multiplicative (WithTop ℤ)ᵒᵈ) := vK.toValuation
  let vl : Valuation L (Multiplicative (WithTop ℤ)ᵒᵈ) := vL.toValuation
  have hvk : Valuation.IsRankOneDiscrete vk :=
    chapter08_rank_one_discrete_of_add_valuation vK hdiscreteK
  have hvl : Valuation.IsRankOneDiscrete vl :=
    chapter08_rank_one_discrete_of_add_valuation vL hdiscreteL
  let : Valuation.HasExtension vk vl := ⟨hval⟩
  let : Algebra vk.valuationSubring vl.valuationSubring :=
    (inferInstance : Algebra vK.toValuation.valuationSubring
      vL.toValuation.valuationSubring)
  have hcompleteV :=
    chapter08_valuation_subring_is_complete_of_integral_test
      vK hcomplete hintegralK
  have hstructure :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring
      vk vl hcompleteV
  let : IsDiscreteValuationRing vl.valuationSubring := hstructure.2.2.2.1
  let hintegralVK : ∀ x : K, IsIntegral vk.valuationSubring x ↔ 0 ≤ vK x := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ :=
        (IsIntegrallyClosed.isIntegral_iff (R := vk.valuationSubring)).mp hx
      have ha0 : 0 ≤ vK (a : K) := a.property
      have ha' : (a : K) = x := ha
      rw [ha'] at ha0
      exact ha0
    · intro hx
      apply (IsIntegrallyClosed.isIntegral_iff (R := vk.valuationSubring)).mpr
      exact ⟨⟨x, hx⟩, rfl⟩
  let hintegralVL : ∀ x : L, IsIntegral vl.valuationSubring x ↔ 0 ≤ vL x := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ :=
        (IsIntegrallyClosed.isIntegral_iff (R := vl.valuationSubring)).mp hx
      have ha0 : 0 ≤ vL (a : L) := a.property
      have ha' : (a : L) = x := ha
      rw [ha'] at ha0
      exact ha0
    · intro hx
      apply (IsIntegrallyClosed.isIntegral_iff (R := vl.valuationSubring)).mpr
      exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨π, hπ0, hπ, hv⟩ := hdiscreteK0
  have hπmem : π ∈ (vk.valuationSubring : Set K) := by
    change 0 ≤ vK π
    rw [hπ]
    simp
  have hπrange := chapter08_valuation_subring_eq_range_of_integral_test
    vK hintegralK
  change π ∈ (vK.toValuation.valuationSubring : Set K) at hπmem
  rw [hπrange] at hπmem
  obtain ⟨πA, hπA⟩ := hπmem
  let aK : vk.valuationSubring :=
    ⟨algebraMap A K πA, by
      change 0 ≤ vK (algebraMap A K πA)
      rw [hπA, hπ]
      simp⟩
  let πB : vl.valuationSubring :=
    ⟨πL, by
      change 0 ≤ vL πL
      rw [hπL]
      simp⟩
  have hdiscreteK' :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK :=
    ⟨π, hπ0, hπ, hv⟩
  have hmaxK := chapter08_value_one_generates_maximal_ideal
    vK hdiscreteK' hintegralVK aK (by simpa [aK, hπA] using hπ)
  have hmaxL := chapter08_value_one_generates_maximal_ideal
    vL hdiscreteL hintegralVL πB (by simpa [πB] using hπL)
  have haK0 : (aK : K) ≠ 0 := by
    intro haKzero
    apply hπ0
    calc
      π = algebraMap A K πA := hπA.symm
      _ = (aK : K) := rfl
      _ = 0 := haKzero
  let bL : vl.valuationSubring :=
    algebraMap vk.valuationSubring vl.valuationSubring aK
  have hbLval : vL (bL : L) = (e : WithTop ℤ) := by
    dsimp [bL]
    rw [hcoe aK]
    rw [hscale (aK : K) haK0]
    have haKval : vK (aK : K) = 1 := by
      simpa [aK, hπA] using hπ
    rw [haKval]
    simp
  have hπBval : vL (πB : L) = 1 := by
    simpa [πB] using hπL
  have hπB0 : (πB : L) ≠ 0 := by
    intro hzero
    have hbad := hπBval
    rw [hzero, AddValuation.map_zero] at hbad
    simp at hbad
  have hbL0 : (bL : L) ≠ 0 := by
    intro hzero
    have hbad := hbLval
    rw [hzero, AddValuation.map_zero] at hbad
    simp at hbad
  let hvintL : vL.toValuation.Integers vl.valuationSubring :=
    Valuation.valuationSubring.integers vL.toValuation
  have huval (u : vl.valuationSubringˣ) : vL (u : L) = 0 := by
    have hu := hvintL.valuation_unit u
    change vL (u : L) = 0 at hu
    exact hu
  have hirrL : Irreducible πB :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).2 hmaxL
  obtain ⟨n, u, hub⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (show bL ≠ 0 by
        intro hzero
        apply hbL0
        exact congrArg (fun z : vl.valuationSubring => (z : L)) hzero) hirrL
  have hnval : (n : WithTop ℤ) = (e : WithTop ℤ) := by
    have hvalhub := congrArg (fun z : vl.valuationSubring => vL (z : L)) hub
    change vL (bL : L) = vL ((u : L) * (πB : L) ^ n) at hvalhub
    rw [vL.map_mul, vL.map_pow, huval, hπBval] at hvalhub
    simpa using hvalhub.symm.trans hbLval
  have hne : n = e := by
    exact_mod_cast hnval
  have hspanb : Ideal.span ({bL} : Set vl.valuationSubring) =
      (IsLocalRing.maximalIdeal vl.valuationSubring) ^ e := by
    calc
      Ideal.span ({bL} : Set vl.valuationSubring) =
          Ideal.span ({(u : vl.valuationSubring) * πB ^ n} : Set vl.valuationSubring) := by
            rw [hub]
      _ = Ideal.span ({πB} : Set vl.valuationSubring) ^ n := by
        rw [Ideal.span_singleton_mul_left_unit u.isUnit]
        rw [← Ideal.span_singleton_pow]
      _ = (IsLocalRing.maximalIdeal vl.valuationSubring) ^ e := by
        rw [hmaxL, hne]
  have hmapmax :
      Ideal.map (algebraMap vk.valuationSubring vl.valuationSubring)
          (IsLocalRing.maximalIdeal vk.valuationSubring) =
        (IsLocalRing.maximalIdeal vl.valuationSubring) ^ e := by
    calc
      Ideal.map (algebraMap vk.valuationSubring vl.valuationSubring)
          (IsLocalRing.maximalIdeal vk.valuationSubring) =
          Ideal.map (algebraMap vk.valuationSubring vl.valuationSubring)
            (Ideal.span {aK}) := by rw [hmaxK]
      _ = Ideal.span {bL} := by
        rw [Ideal.map_span]
        simp [bL]
      _ = (IsLocalRing.maximalIdeal vl.valuationSubring) ^ e := hspanb
  simpa [vk, vl] using hmapmax

set_option maxHeartbeats 1000000 in
theorem chapter08_uniformizer_extension_degree_data
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfinite : Module.Finite A (integralClosure A L))
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (htotal : chapter08TotallyRamified vK vL hval)
    (hintegralK : ∀ x : K, IsIntegral A x ↔ 0 ≤ vK x)
    (hintegralL : ∀ x : L, IsIntegral A x ↔ 0 ≤ vL x)
    (πL : L) (hπL : vL πL = 1) :
    ∃ e : ℕ, 0 < e ∧
      (∀ x : K, x ≠ 0 → vL (algebraMap K L x) = e • vK x) ∧
      Module.finrank K L = e := by
  classical
  obtain ⟨e, he, hscale⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_normalized_restriction_formula
      vK vL hdiscreteK hdiscreteL hval
  let vk : Valuation K (Multiplicative (WithTop ℤ)ᵒᵈ) := vK.toValuation
  let vl : Valuation L (Multiplicative (WithTop ℤ)ᵒᵈ) := vL.toValuation
  let : Valuation.HasExtension vk vl := ⟨hval⟩
  let : Algebra vk.valuationSubring vl.valuationSubring :=
    Valuation.HasExtension.instAlgebra_valuationSubring vk vl
  have hcoe : ∀ a : vk.valuationSubring,
      ((algebraMap vk.valuationSubring vl.valuationSubring a :
          vl.valuationSubring) : L) = algebraMap K L (a : K) := by
    intro a
    exact Valuation.HasExtension.coe_algebraMap_valuationSubring_eq vk vl a
  have hmap := chapter08_uniformizer_maximal_ideal_map
    hcomplete hfinite vK vL hdiscreteK hdiscreteL hval hintegralK hintegralL
      e hscale hcoe πL hπL
  have hcompleteV := chapter08_valuation_subring_is_complete_of_integral_test
    vK hcomplete hintegralK
  let : Valuation.IsRankOneDiscrete vk :=
    chapter08_rank_one_discrete_of_add_valuation vK hdiscreteK
  let : Valuation.IsRankOneDiscrete vl :=
    chapter08_rank_one_discrete_of_add_valuation vL hdiscreteL
  have hstructure :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring
      vk vl hcompleteV
  have hram :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          vk.valuationSubring vl.valuationSubring
          (IsLocalRing.maximalIdeal vl.valuationSubring) = e := by
    let A₀ := vk.valuationSubring
    let B₀ := vl.valuationSubring
    let mA := IsLocalRing.maximalIdeal A₀
    let mB := IsLocalRing.maximalIdeal B₀
    let : IsDiscreteValuationRing B₀ := by
      simpa [B₀] using hstructure.2.2.2.1
    let J : Ideal B₀ := mA.map (algebraMap A₀ B₀)
    have hJpow : J = mB ^ e := by
      simpa [J, A₀, B₀, mA, mB, vk, vl] using hmap
    have hmBpow : mB ^ e ≠ (⊥ : Ideal B₀) := by
      intro hzero
      apply IsDiscreteValuationRing.not_a_field B₀
      exact (Ideal.pow_eq_bot (Nat.ne_of_gt he)).mp hzero
    have hJ0 : J ≠ ⊥ := by
      rw [hJpow]
      exact hmBpow
    obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B₀
      (IsPrincipalIdealRing.principal mB) J hJ0
    have hlen :
        (Module.length (Localization.AtPrime mB)
          (Localization.AtPrime mB ⧸
            mA.map (algebraMap A₀ (Localization.AtPrime mB)))).toNat = n := by
      have hmaploc :
          mA.map (algebraMap A₀ (Localization.AtPrime mB)) =
            J.map (algebraMap B₀ (Localization.AtPrime mB)) := by
        rw [Ideal.map_map]
        congr 1
      let : IsDiscreteValuationRing (Localization.AtPrime mB) :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B₀
          (IsDiscreteValuationRing.not_a_field B₀) (Localization.AtPrime mB)
      rw [hmaploc, hn, Ideal.map_pow,
        Localization.AtPrime.map_eq_maximalIdeal,
        IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
      rfl
    have hramn :
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
            A₀ B₀ mB = n := by
      calc
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
            A₀ B₀ mB = (Module.length (Localization.AtPrime mB)
            (Localization.AtPrime mB ⧸
              mA.map (algebraMap A₀ (Localization.AtPrime mB)))).toNat := by
          unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          exact Ideal.ramificationIdx_eq mA mB
        _ = n := hlen
    have hpows : mB ^ n = mB ^ e := hn.symm.trans hJpow
    have hen : n = e := by
      have hpowval := congrArg (IsDiscreteValuationRing.idealOrderIsoENat B₀) hpows
      have hleft :
          (IsDiscreteValuationRing.idealOrderIsoENat B₀) (mB ^ n) =
            (n : ENatᵒᵈ) := by
        rw [← IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe B₀ n]
        exact (IsDiscreteValuationRing.idealOrderIsoENat B₀).apply_symm_apply _
      have hright :
          (IsDiscreteValuationRing.idealOrderIsoENat B₀) (mB ^ e) =
            (e : ENatᵒᵈ) := by
        rw [← IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe B₀ e]
        exact (IsDiscreteValuationRing.idealOrderIsoENat B₀).apply_symm_apply _
      have hpowval' : (n : ENatᵒᵈ) = (e : ENatᵒᵈ) := by
        calc
          (n : ENatᵒᵈ) =
              (IsDiscreteValuationRing.idealOrderIsoENat B₀) (mB ^ n) := hleft.symm
          _ = (IsDiscreteValuationRing.idealOrderIsoENat B₀) (mB ^ e) := hpowval
          _ = (e : ENatᵒᵈ) := hright
      change (n : WithTop ℕ) = (e : WithTop ℕ) at hpowval'
      exact WithTop.coe_injective hpowval'
    have hram0 := hramn.trans hen
    simpa [A₀, B₀, mB] using hram0
  have hres :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
          vk.valuationSubring vl.valuationSubring
          (IsLocalRing.maximalIdeal vl.valuationSubring) = 1 := by
    change (IsLocalRing.maximalIdeal vl.valuationSubring).inertiaDeg
      vk.valuationSubring = 1
    rw [Ideal.inertiaDeg_eq_of_isMaximal
      (IsLocalRing.maximalIdeal vk.valuationSubring)
      (IsLocalRing.maximalIdeal vl.valuationSubring)]
    let eA : (vk.valuationSubring ⧸ IsLocalRing.maximalIdeal vk.valuationSubring) ≃+*
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK :=
      RingEquiv.refl _
    let eB : (vl.valuationSubring ⧸ IsLocalRing.maximalIdeal vl.valuationSubring) ≃+*
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL :=
      RingEquiv.refl _
    have hfin :
        Module.finrank (vk.valuationSubring ⧸ IsLocalRing.maximalIdeal vk.valuationSubring)
            (vl.valuationSubring ⧸ IsLocalRing.maximalIdeal vl.valuationSubring) =
          Module.finrank
            (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK)
            (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL) := by
      apply Algebra.finrank_eq_of_equiv_equiv eA eB
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun _ => rfl)
    have htotal' :
        Module.finrank
            (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK)
            (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vL) = 1 := by
      simpa [chapter08TotallyRamified,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree] using htotal
    exact hfin.trans htotal'
  have hdegree :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_defectless_without_separability
      vk vl hcompleteV
  refine ⟨e, he, hscale, ?_⟩
  simpa [hram, hres] using hdegree

/-- Book §8.3: a normalized value-one element generates the field in a finite
totally ramified extension once the base is a complete DVR. -/
theorem chapter08_uniformizer_generates_the_field
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfinite : Module.Finite A (integralClosure A L))
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (htotal : chapter08TotallyRamified vK vL hval)
    (hintegralK : ∀ x : K, IsIntegral A x ↔ 0 ≤ vK x)
    (hintegralL : ∀ x : L, IsIntegral A x ↔ 0 ≤ vL x)
    (πL : L) (hπL : vL πL = 1) :
    Algebra.adjoin K ({πL} : Set L) = ⊤ := by
  obtain ⟨e, he, hscale, hdegree⟩ :=
    chapter08_uniformizer_extension_degree_data
      hcomplete hfinite vK vL hdiscreteK hdiscreteL hval htotal
        hintegralK hintegralL πL hπL
  obtain ⟨π, hπ0, hπ, hv⟩ := hdiscreteK
  have hli : LinearIndependent K (fun i : Fin e => πL ^ (i : ℕ)) :=
    chapter08_powers_linearlyIndependent_of_value_one e he vK vL hv hscale πL hπL
  have hcard : Fintype.card (Fin e) = Module.finrank K L := by
    simpa using hdegree.symm
  have hspan :
      Submodule.span K (Set.range (fun i : Fin e => πL ^ (i : ℕ))) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  apply top_unique
  have hle :
      Submodule.span K (Set.range (fun i : Fin e => πL ^ (i : ℕ))) ≤
        (Algebra.adjoin K ({πL} : Set L)).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change πL ^ (i : ℕ) ∈ Algebra.adjoin K ({πL} : Set L)
    exact (Algebra.adjoin K ({πL} : Set L)).pow_mem
      (Algebra.subset_adjoin (Set.mem_singleton πL)) _
  intro x hx
  apply hle
  rw [hspan]
  exact hx

/-- The coefficient-level form of the uniformizer theorem: the minimal
polynomial of a uniformizer is Eisenstein over the base DVR. -/
theorem chapter08_uniformizer_minpoly_is_eisenstein
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfinite : Module.Finite A (integralClosure A L))
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (htotal : chapter08TotallyRamified vK vL hval)
    (hintegralK : ∀ x : K, IsIntegral A x ↔ 0 ≤ vK x)
    (hintegralL : ∀ x : L, IsIntegral A x ↔ 0 ≤ vL x)
    (πK : A) (hπK : vK (algebraMap A K πK) = 1)
    (πL : L) (hπL : vL πL = 1)
    (g : A[X])
    (hminpoly : g.map (algebraMap A K) = minpoly K πL) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt πK g ∧
      g.natDegree = Module.finrank K L := by
  classical
  obtain ⟨e, he, hscale, hdegree⟩ :=
    chapter08_uniformizer_extension_degree_data
      hcomplete hfinite vK vL hdiscreteK hdiscreteL hval htotal
        hintegralK hintegralL πL hπL
  have hπL0 : πL ≠ 0 := by
    intro hzero
    have hbad := hπL
    rw [hzero, AddValuation.map_zero] at hbad
    simp at hbad
  have hgen : Algebra.adjoin K ({πL} : Set L) = ⊤ :=
    chapter08_uniformizer_generates_the_field
      hcomplete hfinite vK vL hdiscreteK hdiscreteL hval htotal
        hintegralK hintegralL πL hπL
  have hPiIntegralK : IsIntegral K πL := Algebra.IsIntegral.isIntegral πL
  let B : PowerBasis K L := PowerBasis.ofAdjoinEqTop hPiIntegralK hgen
  have hBdim : B.dim = (minpoly K πL).natDegree := by
    exact PowerBasis.ofAdjoinEqTop_dim hPiIntegralK hgen
  have hminpoly_degree : (minpoly K πL).natDegree = Module.finrank K L := by
    calc
      (minpoly K πL).natDegree = B.dim := hBdim.symm
      _ = Module.finrank K L := B.finrank.symm
  have hmap_monic : (g.map (algebraMap A K)).Monic := by
    rw [hminpoly]
    exact minpoly.monic hPiIntegralK
  have hgmonic : g.Monic :=
    (Function.Injective.monic_map_iff (p := g)
      (IsFractionRing.injective A K)).mpr hmap_monic
  have hnatdegree : g.natDegree = Module.finrank K L := by
    calc
      g.natDegree = (g.map (algebraMap A K)).natDegree := by
        symm
        exact natDegree_map_eq_of_injective (IsFractionRing.injective A K) g
      _ = (minpoly K πL).natDegree := by rw [hminpoly]
      _ = Module.finrank K L := hminpoly_degree
  have hn : g.natDegree = e := hnatdegree.trans hdegree
  have hroot : aeval πL g = 0 := by
    have hroot' := minpoly.aeval K πL
    rw [← hminpoly] at hroot'
    simpa only [aeval_map_algebraMap, IsScalarTower.algebraMap_eq A K L] using hroot'
  have hAinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hvalues : ∀ x : K, x ≠ 0 → ∃ z : ℤ, vK x = z := by
    obtain ⟨_, _, _, hvalues⟩ := hdiscreteK
    exact hvalues
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span ({πK} : Set A) :=
    chapter08_value_one_generates_maximal_ideal
      vK hdiscreteK hintegralK πK hπK
  let hvint : vK.toValuation.Integers A := by
    refine {
      hom_inj := IsFractionRing.injective A K
      map_le_one := ?_
      exists_of_le_one := ?_ }
    · intro a
      change 0 ≤ vK (algebraMap A K a)
      exact (hintegralK _).1 isIntegral_algebraMap
    · intro x hx
      change 0 ≤ vK x at hx
      obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A)).mp
        ((hintegralK x).2 hx)
      exact ⟨a, ha⟩
  have hvalue_ideal : ∀ a : A,
      a ∈ IsLocalRing.maximalIdeal A ↔ 0 < vK (algebraMap A K a) := by
    intro a
    constructor
    · intro ha
      have hnotunit : ¬ IsUnit a := by
        rw [IsLocalRing.mem_maximalIdeal] at ha
        exact ha
      have hlt : vK.toValuation (algebraMap A K a) < 1 := by
        apply lt_of_le_of_ne (hvint.map_le_one a)
        intro heq
        exact hnotunit (hvint.isUnit_iff_valuation_eq_one.mpr heq)
      change (0 : WithTop ℤ) < vK (algebraMap A K a) at hlt
      exact hlt
    · intro ha
      rw [hmax]
      apply Ideal.mem_span_singleton.mpr
      by_cases ha0 : a = 0
      · simp [ha0]
      have hmapne : algebraMap A K a ≠ 0 := by
        exact (map_ne_zero_iff (algebraMap A K)
          (IsFractionRing.injective A K)).2 ha0
      obtain ⟨z, hz⟩ := hvalues (algebraMap A K a) hmapne
      have hzpos : (0 : ℤ) < z := by
        rw [hz] at ha
        exact_mod_cast ha
      have hzone : (1 : WithTop ℤ) ≤ (z : WithTop ℤ) := by
        exact_mod_cast (show (1 : ℤ) ≤ z by omega)
      have hle : vK.toValuation (algebraMap A K a) ≤
          vK.toValuation (algebraMap A K πK) := by
        change OrderDual.toDual (vK (algebraMap A K a)) ≤
          OrderDual.toDual (vK (algebraMap A K πK))
        rw [hz, hπK]
        change (1 : WithTop ℤ) ≤ (z : WithTop ℤ)
        exact hzone
      obtain ⟨b, hb⟩ := hvint.dvd_of_le hle
      exact ⟨b, hb⟩
  have hvalue_square : ∀ a : A,
      a ∈ IsLocalRing.maximalIdeal A ∧
        a ∉ (IsLocalRing.maximalIdeal A) ^ 2 ↔
        vK (algebraMap A K a) = 1 := by
    intro a
    constructor
    · rintro ⟨ha, hnot⟩
      have ha0 : a ≠ 0 := by
        intro ha0
        apply hnot
        simp [ha0]
      have hmapne : algebraMap A K a ≠ 0 := by
        exact (map_ne_zero_iff (algebraMap A K)
          (IsFractionRing.injective A K)).2 ha0
      obtain ⟨z, hz⟩ := hvalues (algebraMap A K a) hmapne
      have hzpos : (0 : ℤ) < z := by
        have hpos := (hvalue_ideal a).mp ha
        rw [hz] at hpos
        exact_mod_cast hpos
      have hnottwo : ¬ (2 : ℤ) ≤ z := by
        intro hz2
        apply hnot
        rw [hmax, Ideal.span_singleton_pow]
        apply Ideal.mem_span_singleton.mpr
        have hle : vK.toValuation (algebraMap A K a) ≤
            vK.toValuation (algebraMap A K (πK ^ 2)) := by
          change OrderDual.toDual (vK (algebraMap A K a)) ≤
            OrderDual.toDual (vK (algebraMap A K (πK ^ 2)))
          rw [hz, map_pow, AddValuation.map_pow, hπK]
          change (2 : WithTop ℤ) ≤ (z : WithTop ℤ)
          exact WithTop.coe_le_coe.mpr hz2
        obtain ⟨b, hb⟩ := hvint.dvd_of_le hle
        exact ⟨b, hb⟩
      have hzone : z = 1 := by omega
      rw [hz, hzone]
      norm_num
    · intro ha
      refine ⟨(hvalue_ideal a).mpr ?_, ?_⟩
      · rw [ha]
        norm_num
      · intro ha2
        rw [hmax, Ideal.span_singleton_pow] at ha2
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha2
        have hle : vK.toValuation (algebraMap A K a) ≤
            vK.toValuation (algebraMap A K (πK ^ 2)) := by
          apply hvint.le_of_dvd
          exact ⟨b, hb⟩
        change OrderDual.toDual (vK (algebraMap A K a)) ≤
          OrderDual.toDual (vK (algebraMap A K (πK ^ 2))) at hle
        rw [ha, map_pow, AddValuation.map_pow, hπK] at hle
        change (2 : WithTop ℤ) ≤ (1 : WithTop ℤ) at hle
        norm_num at hle
  have hEform := chapter08_eisenstein_coefficient_valuation_form
    vK πK g hmax.symm hvalue_ideal hvalue_square
  have hEdata : g.Monic ∧ 0 < g.natDegree ∧
      (∀ i < g.natDegree, 0 < vK (algebraMap A K (g.coeff i))) ∧
      vK (algebraMap A K g.constantCoeff) = 1 := by
    have hnpos : 0 < g.natDegree := by
      rw [hnatdegree]
      exact Module.finrank_pos
    have hcoeff0 : g.coeff 0 ≠ 0 := by
      have hmincoeff := minpoly.coeff_zero_ne_zero hPiIntegralK hπL0
      intro hz
      apply hmincoeff
      have hc := congrArg (fun p : K[X] => p.coeff 0) hminpoly
      rw [coeff_map, hz, map_zero] at hc
      exact hc.symm
    let terms : Fin (g.natDegree + 1) → L := fun i =>
      algebraMap A L (g.coeff (i : ℕ)) * πL ^ (i : ℕ)
    have hsum : (∑ i, terms i) = 0 := by
      simpa [terms, Polynomial.aeval_eq_sum_range, Algebra.smul_def,
        ← Fin.sum_univ_eq_sum_range] using hroot
    have hcoeff_map_ne (i : Fin (g.natDegree + 1))
        (hi : g.coeff (i : ℕ) ≠ 0) :
        algebraMap A K (g.coeff (i : ℕ)) ≠ 0 := by
      exact (map_ne_zero_iff (algebraMap A K)
        (IsFractionRing.injective A K)).2 hi
    have hterm_value (i : Fin (g.natDegree + 1))
        (hi : g.coeff (i : ℕ) ≠ 0) :
        ∃ z : ℤ,
          vK (algebraMap A K (g.coeff (i : ℕ))) = (z : WithTop ℤ) ∧
            vL (terms i) =
              ((e : ℤ) * z + (i : ℤ) : WithTop ℤ) := by
      have hmapne := hcoeff_map_ne i hi
      obtain ⟨z, hz⟩ := hvalues (algebraMap A K (g.coeff (i : ℕ))) hmapne
      refine ⟨z, hz, ?_⟩
      dsimp [terms]
      rw [AddValuation.map_mul, IsScalarTower.algebraMap_apply A K L,
        hscale _ hmapne, AddValuation.map_pow, hπL, hz]
      rw [← WithTop.coe_nsmul]
      congr 1
      norm_num [nsmul_eq_mul]
    have hleading_coeff : g.coeff g.natDegree = 1 := by
      simpa using hgmonic.coeff_natDegree
    let iN : Fin (g.natDegree + 1) :=
      ⟨g.natDegree, Nat.lt_succ_self _⟩
    have hterm0 : terms (0 : Fin (g.natDegree + 1)) ≠ 0 := by
      dsimp [terms]
      have hmapne : algebraMap A L (g.coeff 0) ≠ 0 := by
        intro hzero
        apply hcoeff0
        apply hAinj
        simpa using hzero
      exact mul_ne_zero hmapne (pow_ne_zero _ hπL0)
    have htermN : terms iN ≠ 0 := by
      dsimp [terms, iN]
      simp [Polynomial.leadingCoeff, hleading_coeff, hπL0]
    have htermN_value : vL (terms iN) =
        (g.natDegree : WithTop ℤ) := by
      dsimp [terms, iN]
      simp only [Polynomial.leadingCoeff, hleading_coeff]
      rw [AddValuation.map_mul,
        IsScalarTower.algebraMap_apply A K L,
        AddValuation.map_pow, hπL]
      simp
    have hno_strict_least (i₀ : Fin (g.natDegree + 1))
        (hti : terms i₀ ≠ 0)
        (hleast : ∀ j, j ≠ i₀ → vL (terms i₀) < vL (terms j)) : False := by
      have hcancel :=
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_strictly_least_valued_term_does_not_cancel
          vL terms i₀ hti hleast
      have hfinite : vL (terms i₀) ≠ (⊤ : WithTop ℤ) :=
        vL.ne_top_iff.mpr hti
      apply hfinite
      calc
        vL (terms i₀) = vL (∑ i, terms i) := hcancel.symm
        _ = vL 0 := by rw [hsum]
        _ = ⊤ := AddValuation.map_zero vL
    have hcoeff_nonneg (i : Fin (g.natDegree + 1)) :
        0 ≤ vK (algebraMap A K (g.coeff (i : ℕ))) :=
      (hintegralK _).1 isIntegral_algebraMap
    have hcoeff_z_nonneg (i : Fin (g.natDegree + 1)) (z : ℤ)
        (hz : vK (algebraMap A K (g.coeff (i : ℕ))) = (z : WithTop ℤ)) :
        0 ≤ z := by
      have hnonneg := hcoeff_nonneg i
      rw [hz] at hnonneg
      exact_mod_cast hnonneg
    obtain ⟨z0, hz0coeff, hz0term⟩ := hterm_value
      (0 : Fin (g.natDegree + 1)) hcoeff0
    have hterm0_value : vL (terms (0 : Fin (g.natDegree + 1))) =
        ((e : ℤ) * z0 : WithTop ℤ) := by
      simpa using hz0term
    have hz0_lower : (1 : ℤ) ≤ z0 := by
      by_contra hnot
      have hz0lt : z0 < 1 := lt_of_not_ge hnot
      have hleast : ∀ j, j ≠ (0 : Fin (g.natDegree + 1)) →
          vL (terms (0 : Fin (g.natDegree + 1))) < vL (terms j) := by
        intro j hj
        by_cases ht : terms j = 0
        · rw [ht, AddValuation.map_zero]
          exact (vL.ne_top_iff.mpr hterm0).lt_top
        · have hcj : g.coeff (j : ℕ) ≠ 0 := by
            intro hc
            apply ht
            simp [terms, hc]
          obtain ⟨zj, hzjcoeff, hzjterm⟩ := hterm_value j hcj
          have hzjnonneg := hcoeff_z_nonneg j zj hzjcoeff
          have hj0 : (j : ℕ) ≠ 0 := by
            intro hj0
            apply hj
            exact Fin.ext hj0
          have hjpos : (0 : ℤ) < (j : ℤ) := by
            exact_mod_cast (Nat.pos_of_ne_zero hj0)
          have hz0le : z0 ≤ 0 := by omega
          have hlt : (e : ℤ) * z0 <
              (e : ℤ) * zj + (j : ℤ) := by
            have heZ : (0 : ℤ) < (e : ℤ) := by
              exact_mod_cast he
            have hleft : (e : ℤ) * z0 ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (le_of_lt heZ) hz0le
            have hmul : 0 ≤ (e : ℤ) * zj :=
              mul_nonneg (le_of_lt heZ) hzjnonneg
            have hright : 0 < (e : ℤ) * zj + (j : ℤ) := by omega
            exact hleft.trans_lt hright
          rw [hterm0_value, hzjterm]
          exact WithTop.coe_lt_coe.mpr hlt
      exact hno_strict_least (0 : Fin (g.natDegree + 1)) hterm0 hleast
    have hcoeff_pos : ∀ i < g.natDegree,
        0 < vK (algebraMap A K (g.coeff i)) := by
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        have hz0pos : (0 : WithTop ℤ) < (z0 : WithTop ℤ) := by
          exact WithTop.coe_pos.mpr (by omega)
        change 0 < vK (algebraMap A K (g.coeff (0 : ℕ)))
        have hz0coeff' :
            vK (algebraMap A K (g.coeff (0 : ℕ))) = (z0 : WithTop ℤ) := by
          simpa using hz0coeff
        rw [hz0coeff']
        exact hz0pos
      · have hi' : i < g.natDegree + 1 := by omega
        let j : Fin (g.natDegree + 1) := ⟨i, hi'⟩
        by_contra hnot
        have hnonneg : 0 ≤ vK (algebraMap A K (g.coeff i)) := by
          exact (hintegralK _).1 isIntegral_algebraMap
        have hzero : vK (algebraMap A K (g.coeff i)) = 0 := by
          apply le_antisymm
          · exact le_of_not_gt hnot
          · exact hnonneg
        let s : Finset (Fin (g.natDegree + 1)) := Finset.univ.filter
          (fun k => 0 < (k : ℕ) ∧ (k : ℕ) < g.natDegree ∧
            vK (algebraMap A K (g.coeff (k : ℕ))) = 0)
        have hs : s.Nonempty := by
          refine ⟨j, ?_⟩
          have hjpos : 0 < (j : ℕ) := by
            exact Nat.pos_of_ne_zero hi0
          simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hjpos, hi, hzero⟩
        obtain ⟨j₀, hj₀, hmin⟩ :=
          Finset.exists_min_image s (fun k => (k : ℕ)) hs
        have hj₀data : 0 < (j₀ : ℕ) ∧ (j₀ : ℕ) < g.natDegree ∧
            vK (algebraMap A K (g.coeff (j₀ : ℕ))) = 0 := by
          simpa [s] using hj₀
        have hj₀bounds : 0 < (j₀ : ℕ) ∧ (j₀ : ℕ) < g.natDegree :=
          ⟨hj₀data.1, hj₀data.2.1⟩
        have hj₀zero :
            vK (algebraMap A K (g.coeff (j₀ : ℕ))) = 0 := hj₀data.2.2
        have hj₀coeff : g.coeff (j₀ : ℕ) ≠ 0 := by
          intro hc
          rw [hc, map_zero, AddValuation.map_zero] at hj₀zero
          simp at hj₀zero
        obtain ⟨zj₀, hzj₀coeff, hzj₀term⟩ :=
          hterm_value j₀ hj₀coeff
        have hzj₀ : zj₀ = 0 := by
          have hzj₀' : (zj₀ : WithTop ℤ) = 0 :=
            hzj₀coeff.symm.trans hj₀zero
          exact_mod_cast hzj₀'
        have hj₀term : terms j₀ ≠ 0 := by
          dsimp [terms]
          have hmapne : algebraMap A L (g.coeff (j₀ : ℕ)) ≠ 0 := by
            intro hzero'
            apply hj₀coeff
            apply hAinj
            simpa using hzero'
          exact mul_ne_zero hmapne (pow_ne_zero _ hπL0)
        have hj₀term_value : vL (terms j₀) =
            (j₀ : WithTop ℤ) := by
          rw [hzj₀] at hzj₀term
          simpa using hzj₀term
        have hleast : ∀ k, k ≠ j₀ →
            vL (terms j₀) < vL (terms k) := by
          intro k hkj₀
          by_cases htk : terms k = 0
          · rw [htk, AddValuation.map_zero]
            exact (vL.ne_top_iff.mpr hj₀term).lt_top
          · by_cases hk0 : (k : ℕ) = 0
            · have hjeNat : (j₀ : ℕ) < e := by omega
              have hje : (j₀ : ℤ) < (e : ℤ) := by
                exact_mod_cast hjeNat
              have heZ : (0 : ℤ) < (e : ℤ) := by
                exact_mod_cast he
              have hprod : (e : ℤ) ≤ (e : ℤ) * z0 := by
                calc
                  (e : ℤ) = (e : ℤ) * 1 := by ring
                  _ ≤ (e : ℤ) * z0 :=
                    mul_le_mul_of_nonneg_left hz0_lower (le_of_lt heZ)
              have hlt : (j₀ : ℤ) < (e : ℤ) * z0 := hje.trans_le hprod
              have hkzero : k = (0 : Fin (g.natDegree + 1)) := by
                apply Fin.ext
                exact hk0
              rw [hkzero, hj₀term_value, hterm0_value]
              exact WithTop.coe_lt_coe.mpr hlt
            · have hck : g.coeff (k : ℕ) ≠ 0 := by
                intro hc
                apply htk
                simp [terms, hc]
              obtain ⟨zk, hzkcoeff, hzkt⟩ := hterm_value k hck
              have hzk_nonneg := hcoeff_z_nonneg k zk hzkcoeff
              have hkne : (k : ℕ) ≠ (j₀ : ℕ) := by
                intro hk
                apply hkj₀
                exact Fin.ext hk
              have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk0
              have hkn : (k : ℕ) < g.natDegree ∨
                  (k : ℕ) = g.natDegree := by
                have := k.isLt
                omega
              rcases hkn with hkn | hkn
              · have hjk : (k : ℕ) < (j₀ : ℕ) ∨
                    (j₀ : ℕ) < (k : ℕ) := lt_or_gt_of_ne hkne
                rcases hjk with hjk | hjk
                · have hzk_ne : zk ≠ 0 := by
                    intro hzk0
                    have hkzero' :
                        vK (algebraMap A K (g.coeff (k : ℕ))) = 0 := by
                      rw [hzkcoeff, hzk0]
                      norm_num
                    have hkmem : k ∈ s := by
                      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
                      exact ⟨hkpos, hkn, hkzero'⟩
                    have hmin' := hmin k hkmem
                    omega
                  have hzk_one : (1 : ℤ) ≤ zk := by
                    have hzk_pos : (0 : ℤ) < zk :=
                      lt_of_le_of_ne hzk_nonneg (Ne.symm hzk_ne)
                    omega
                  have hlt : (j₀ : ℤ) <
                      (e : ℤ) * zk + (k : ℤ) := by
                    have hjeNat : (j₀ : ℕ) < e := by omega
                    have hje : (j₀ : ℤ) < (e : ℤ) := by
                      exact_mod_cast hjeNat
                    have heZ : (0 : ℤ) < (e : ℤ) := by
                      exact_mod_cast he
                    have he_le : (e : ℤ) ≤ (e : ℤ) * zk := by
                      calc
                        (e : ℤ) = (e : ℤ) * 1 := by ring
                        _ ≤ (e : ℤ) * zk :=
                          mul_le_mul_of_nonneg_left hzk_one (le_of_lt heZ)
                    exact hje.trans_le (he_le.trans (by omega))
                  rw [hj₀term_value, hzkt]
                  exact WithTop.coe_lt_coe.mpr hlt
                · have hlt : (j₀ : ℤ) <
                      (e : ℤ) * zk + (k : ℤ) := by
                    have hjeNat : (j₀ : ℕ) < e := by omega
                    have hje : (j₀ : ℤ) < (e : ℤ) := by
                      exact_mod_cast hjeNat
                    have heZ : (0 : ℤ) < (e : ℤ) := by
                      exact_mod_cast he
                    have hmul : 0 ≤ (e : ℤ) * zk :=
                      mul_nonneg (le_of_lt heZ) hzk_nonneg
                    have hjkZ : (j₀ : ℤ) < (k : ℤ) := by
                      exact_mod_cast hjk
                    have hk_le : (k : ℤ) ≤ (e : ℤ) * zk + (k : ℤ) := by
                      omega
                    exact lt_of_lt_of_le hjkZ hk_le
                  rw [hj₀term_value, hzkt]
                  exact WithTop.coe_lt_coe.mpr hlt
              · have hlt : (j₀ : ℤ) < (g.natDegree : ℤ) := by
                  exact_mod_cast hj₀bounds.2
                have hkN : k = iN := by
                  apply Fin.ext
                  exact hkn
                rw [hkN, hj₀term_value, htermN_value]
                exact WithTop.coe_lt_coe.mpr hlt
        exact hno_strict_least j₀ hj₀term hleast
    have hz0_le : z0 ≤ 1 := by
      by_contra hnot
      have hz0gt : 1 < z0 := lt_of_not_ge hnot
      have hleast : ∀ j, j ≠ iN →
          vL (terms iN) < vL (terms j) := by
        intro j hjiN
        by_cases ht : terms j = 0
        · rw [ht, AddValuation.map_zero]
          exact (vL.ne_top_iff.mpr htermN).lt_top
        · have hcj : g.coeff (j : ℕ) ≠ 0 := by
            intro hc
            apply ht
            simp [terms, hc]
          by_cases hj0 : (j : ℕ) = 0
          · have hjzero : j = (0 : Fin (g.natDegree + 1)) := by
              apply Fin.ext
              exact hj0
            have hlt : (g.natDegree : ℤ) < (e : ℤ) * z0 := by
              have hne : (g.natDegree : ℤ) = (e : ℤ) := by
                exact_mod_cast hn
              have heZ : (0 : ℤ) < (e : ℤ) := by
                exact_mod_cast he
              have hprod : (e : ℤ) ≤ (e : ℤ) * z0 := by
                calc
                  (e : ℤ) = (e : ℤ) * 1 := by ring
                  _ ≤ (e : ℤ) * z0 :=
                    mul_le_mul_of_nonneg_left (by omega) (le_of_lt heZ)
              have hprod_strict : (e : ℤ) < (e : ℤ) * z0 := by
                calc
                  (e : ℤ) = (e : ℤ) * 1 := by ring
                  _ < (e : ℤ) * z0 := mul_lt_mul_of_pos_left hz0gt heZ
              exact hne ▸ hprod_strict
            rw [hjzero, htermN_value, hterm0_value]
            exact WithTop.coe_lt_coe.mpr hlt
          · have hjn : (j : ℕ) ≠ g.natDegree := by
              intro hjn
              apply hjiN
              exact Fin.ext hjn
            have hjlt : (j : ℕ) < g.natDegree := by
              have := j.isLt
              omega
            have hpos := hcoeff_pos (j : ℕ) hjlt
            obtain ⟨zj, hzjcoeff, hzjterm⟩ := hterm_value j hcj
            have hzjpos : (0 : ℤ) < zj := by
              rw [hzjcoeff] at hpos
              exact_mod_cast hpos
            have hzjone : (1 : ℤ) ≤ zj := by omega
            have hlt : (g.natDegree : ℤ) <
                (e : ℤ) * zj + (j : ℤ) := by
              have hne : (g.natDegree : ℤ) = (e : ℤ) := by
                exact_mod_cast hn
              have heZ : (0 : ℤ) < (e : ℤ) := by
                exact_mod_cast he
              have he_le : (e : ℤ) ≤ (e : ℤ) * zj := by
                calc
                  (e : ℤ) = (e : ℤ) * 1 := by ring
                  _ ≤ (e : ℤ) * zj :=
                    mul_le_mul_of_nonneg_left hzjone (le_of_lt heZ)
              have hjpos : (0 : ℤ) < (j : ℤ) := by
                exact_mod_cast (Nat.pos_of_ne_zero hj0)
              have hstrict : (e : ℤ) * zj <
                  (e : ℤ) * zj + (j : ℤ) := by omega
              calc
                (g.natDegree : ℤ) = (e : ℤ) := hne
                _ ≤ (e : ℤ) * zj := he_le
                _ < (e : ℤ) * zj + (j : ℤ) := hstrict
            rw [htermN_value, hzjterm]
            exact WithTop.coe_lt_coe.mpr hlt
      exact hno_strict_least iN htermN hleast
    have hz0 : z0 = 1 := by omega
    have hconstant : vK (algebraMap A K g.constantCoeff) = 1 := by
      simpa [Polynomial.constantCoeff, hz0] using hz0coeff
    exact ⟨hgmonic, hnpos, hcoeff_pos, hconstant⟩
  refine ⟨hEform.mpr hEdata, hnatdegree⟩

/-- Book §8.3, Theorem 8.2: every uniformizer of a finite totally ramified
local extension generates both the field and its integral closure, and its
minimal polynomial is Eisenstein of the field degree. -/
theorem chapter08_uniformizer_theorem
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfinite : Module.Finite A (integralClosure A L))
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (htotal : chapter08TotallyRamified vK vL hval)
    (hintegralK : ∀ x : K, IsIntegral A x ↔ 0 ≤ vK x)
    (hintegralL : ∀ x : L, IsIntegral A x ↔ 0 ≤ vL x)
    (πK : A) (hπK : vK (algebraMap A K πK) = 1)
    (πL : L) (hπL : vL πL = 1) :
    ∃ g : A[X],
      g.Monic ∧
      g.map (algebraMap A K) = minpoly K πL ∧
      g.natDegree = Module.finrank K L ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt πK g ∧
      Algebra.adjoin K ({πL} : Set L) = ⊤ ∧
      (integralClosure A L : Set L) =
        (Algebra.adjoin A ({πL} : Set L) : Set L) ∧
      vL πL = 1 := by
  have hπLint : IsIntegral A πL := by
    apply (hintegralL πL).2
    rw [hπL]
    norm_num
  have hmap : (minpoly A πL).map (algebraMap A K) = minpoly K πL := by
    exact (minpoly.isIntegrallyClosed_eq_field_fractions' K hπLint).symm
  have hgen : Algebra.adjoin K ({πL} : Set L) = ⊤ :=
    chapter08_uniformizer_generates_the_field
      hcomplete hfinite vK vL hdiscreteK hdiscreteL hval htotal
        hintegralK hintegralL πL hπL
  obtain ⟨hE, hdegree⟩ :=
    chapter08_uniformizer_minpoly_is_eisenstein
      hcomplete hfinite vK vL hdiscreteK hdiscreteL hval htotal
        hintegralK hintegralL πK hπK πL hπL (minpoly A πL) hmap
  have hroot : aeval πL (minpoly A πL) = 0 := minpoly.aeval A πL
  have hclosure :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_integral_closure_is_root_order
    πK (minpoly A πL) πL hE hroot hdegree hgen
  refine ⟨minpoly A πL, minpoly.monic hπLint, hmap, hdegree, hE, hgen,
    hclosure, hπL⟩

/-- The norm of a uniformizer in a finite totally ramified extension has
valuation one in the base field (Book 2, Section 8.3). -/
theorem chapter08_uniformizer_norm_has_value_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (e : ℕ) (he : 0 < e)
    (hedegree : e = Module.finrank K L)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = e • vK x)
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) →
        vL.IsEquiv w)
    (htotal : chapter08TotallyRamified vK vL hval)
    (varpi : L) (hvarpi : vL varpi = 1) :
    vK (Algebra.norm K varpi) = 1 := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
