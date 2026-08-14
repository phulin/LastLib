import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section01TheMeaningOfTotalRamification
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
      Module.finrank K L = e := by sorry

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
  sorry

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
  sorry

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
  sorry

/-- The norm of a uniformizer in a finite totally ramified extension has
valuation one in the base field (Book 2, Section 8.3). -/
theorem chapter08_uniformizer_norm_has_value_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (e : ℕ) (he : 0 < e)
    (hedegree : e = Module.finrank K L)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = e • vK x)
    (htotal : chapter08TotallyRamified vK vL hval)
    (varpi : L) (hvarpi : vL varpi = 1) :
    vK (Algebra.norm K varpi) = 1 := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
