import LastLib.Book03RamificationTheory.Chapter07.Section04KaehlerDifferentials
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Section02EquivalentCharacterizations

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 7.5. Exact trace ideals -/

/-- The trace image of a fractional `B`-ideal. -/
def chapter07TraceImage
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (I : FractionalIdeal B⁰ L) : Set K :=
  Algebra.trace K L '' (I : Set L)

theorem chapter07_mem_trace_image_iff
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (I : FractionalIdeal B⁰ L) (x : K) :
    x ∈ chapter07TraceImage A B K L I ↔
      ∃ y : L, y ∈ (I : Set L) ∧ Algebra.trace K L y = x := Iff.rfl

/-- The integer exponent on the base side of the exact trace formula. -/
def chapter07TraceImageExponent (n : ℤ) (d e : ℕ) : ℤ :=
  chapter07FloorDiv n (d : ℤ) e

theorem chapter07TraceImageExponent_eq_displayed_floor
    (n : ℤ) (d e : ℕ) (he : 0 < e) :
    chapter07TraceImageExponent n d e =
      ⌊(n + d : ℚ) / e⌋ := by
  exact chapter07FloorDiv_eq_floor n (d : ℤ) e he

private theorem chapter07_trace_image_as_fractional_ideal
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (I : FractionalIdeal B⁰ L) (hI : I ≠ 0)
    (J : FractionalIdeal A⁰ K)
    (hsubset : chapter07TraceImage A B K L I ⊆ (J : Set K)) :
    ∃ T : FractionalIdeal A⁰ K,
      (T : Set K) = chapter07TraceImage A B K L I ∧ T ≠ 0 := by
  let htrace : L →ₗ[A] K := (Algebra.trace K L).restrictScalars A
  let U : Submodule A L := (I : Submodule B L).restrictScalars A
  let Tsub : Submodule A K := Submodule.map htrace U
  have hTle : Tsub ≤ (J : Submodule A K) := by
    intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    exact hsubset ⟨y, hy, hxy⟩
  let T : FractionalIdeal A⁰ K := ⟨Tsub, FractionalIdeal.isFractional_of_le hTle⟩
  have hTset : (T : Set K) = chapter07TraceImage A B K L I := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy⟩
  have hIelem : ∃ y : L, y ∈ I ∧ y ≠ 0 := by
    by_contra h'
    apply hI
    rw [FractionalIdeal.eq_zero_iff]
    intro x hx
    by_contra hxne
    exact h' ⟨x, hx, hxne⟩
  obtain ⟨y, hyI, hy⟩ := hIelem
  let hbasisA : Module.Basis (Module.Free.ChooseBasisIndex A B) A B :=
    Module.Free.chooseBasis A B
  let _ : Fintype (Module.Free.ChooseBasisIndex A B) := Fintype.ofFinite _
  let _ : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  let hbasisK : Module.Basis (Module.Free.ChooseBasisIndex A B) K L :=
    hbasisA.localizationLocalization K A⁰ L
  have hbasisA_span :
      (1 : Submodule B L).restrictScalars A =
        Submodule.span A (Set.range hbasisK) := by
    rw [Module.Basis.localizationLocalization_span K A⁰ L hbasisA]
    ext x
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      simpa [Algebra.linearMap_apply, IsScalarTower.toAlgHom_apply,
        LinearMap.toSpanSingleton_apply, Algebra.algebraMap_eq_smul_one] using hb
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      simpa [Algebra.linearMap_apply, IsScalarTower.toAlgHom_apply,
        LinearMap.toSpanSingleton_apply, Algebra.algebraMap_eq_smul_one] using hb
  have hBmem (i : Module.Free.ChooseBasisIndex A B) :
      ∃ b : B, algebraMap B L b = hbasisK i := by
    have hi : hbasisK i ∈
        (1 : Submodule B L).restrictScalars A := by
      rw [hbasisA_span]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hi' : hbasisK i ∈ (1 : Submodule B L) := hi
    rw [Submodule.one_eq_range] at hi'
    exact hi'
  have htrace_b_ne : ∃ b : B,
      Algebra.trace K L (y * algebraMap B L b) ≠ 0 := by
    by_contra hzero
    apply hy
    apply (traceForm_nondegenerate K L).1 y
    let φ : L →ₗ[K] K :=
      (Algebra.trace K L).comp (LinearMap.mulLeft K y)
    have hφ : φ = 0 := by
      apply hbasisK.ext
      intro i
      obtain ⟨b, hb⟩ := hBmem i
      apply Classical.byContradiction
      intro hne
      exact hzero ⟨b, by simpa [φ, hb, mul_comm] using hne⟩
    intro z
    have hz := congrArg (fun ψ : L →ₗ[K] K => ψ z) hφ
    simpa [φ, LinearMap.comp_apply] using hz
  obtain ⟨b, hb⟩ := htrace_b_ne
  have hybI : y * algebraMap B L b ∈ I := by
    rw [mul_comm]
    change algebraMap B L b * y ∈ (I : Submodule B L)
    rw [← Algebra.smul_def]
    exact (I : Submodule B L).smul_mem b hyI
  have hTne : T ≠ 0 := by
    intro hzero
    apply hb
    have hmemT : Algebra.trace K L (y * algebraMap B L b) ∈ (T : Set K) := by
      rw [hTset]
      exact ⟨y * algebraMap B L b, hybI, rfl⟩
    rw [hzero] at hmemT
    simpa using hmemT
  exact ⟨T, hTset, hTne⟩

private theorem chapter07_maximal_power_span
    (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (π : A) (hπ : Irreducible π) (q : ℤ) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K m q =
      FractionalIdeal.spanSingleton A⁰
        ((algebraMap A K π) ^ q) := by
  rw [hm, LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower]
  by_cases hq : 0 ≤ q
  · rw [dif_pos hq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      FractionalIdeal.coeIdeal_span_singleton]
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hq
    simp [hk]
  · rw [dif_neg hq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_inv]
    have hqneg : 0 ≤ -q := by omega
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hqneg
    have hq' : q = -(k : ℤ) := by omega
    have hk' : (-q).toNat = k := by simpa [hk]
    simp [hq']

private theorem chapter07_maximal_power_le_iff
    (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (n r : ℤ) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K m n ≤
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K m r ↔ r ≤ n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let hπu : LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Chapter04Uniformizer A π :=
    ⟨hπ.ne_zero, hπ.maximalIdeal_eq⟩
  have hpow (q : ℤ) :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          A K m q =
        FractionalIdeal.spanSingleton A⁰ ((algebraMap A K π) ^ q) := by
    rw [hm, LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower]
    by_cases hq : 0 ≤ q
    · rw [dif_pos hq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
        FractionalIdeal.coeIdeal_span_singleton]
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hq
      simp [hk]
    · rw [dif_neg hq, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
        FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.spanSingleton_inv]
      have hqneg : 0 ≤ -q := by omega
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hqneg
      have hq' : q = -(k : ℤ) := by omega
      simp [hq']
  have hπK : algebraMap A K π ≠ 0 := by simpa using hπ.ne_zero
  rw [hpow n, hpow r]
  constructor
  · intro hle
    have hmem : (algebraMap A K π) ^ n ∈
        FractionalIdeal.spanSingleton A⁰ ((algebraMap A K π) ^ r) :=
      (FractionalIdeal.spanSingleton_le_iff_mem).mp hle
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_spanSingleton A⁰).mp hmem
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_smul] at ha
      exact zpow_ne_zero n (by simpa using hπ.ne_zero) ha.symm
    obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
    have hxeq :
        algebraMap A K a * (algebraMap A K π) ^ r = (algebraMap A K π) ^ n := by
      simpa [Algebra.smul_def] using ha
    obtain ⟨n₀, u₀, hbase, hnormal⟩ :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.dvr_fraction_field_unique_normal_form
        A K hπu (zpow_ne_zero n hπK)
    have hpair := hnormal (r + k) u (by
      calc
        (algebraMap A K π) ^ n = algebraMap A K a * (algebraMap A K π) ^ r := hxeq.symm
        _ = algebraMap A K (u * π ^ k) * (algebraMap A K π) ^ r := by rw [hu]
        _ = algebraMap A K u * (algebraMap A K π) ^ k *
            (algebraMap A K π) ^ r := by rw [map_mul, map_pow]
        _ = u • (algebraMap A K π) ^ (r + k) := by
          simp only [Units.smul_def, Algebra.smul_def]
          rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hπK, add_comm]
      )
    have hn₀ : n₀ = n := (hnormal n 1 (by simp)).1.symm
    omega
  · intro hrn
    apply (FractionalIdeal.spanSingleton_le_iff_mem).mpr
    let k : ℕ := (n - r).toNat
    refine (FractionalIdeal.mem_spanSingleton A⁰).mpr ⟨π ^ k, ?_⟩
    have hk' : n = r + (k : ℤ) := by
      dsimp [k]
      rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hrn)]
      omega
    rw [hk']
    rw [Algebra.smul_def, map_pow, ← zpow_natCast, ← zpow_add₀ hπK,
      add_comm]

private theorem chapter07_maximal_power_mul
    (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (π : A) (hπ : Irreducible π) (q r : ℤ) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K m q *
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K m r =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K m (q + r) := by
  have hπK : algebraMap A K π ≠ 0 := by simpa using hπ.ne_zero
  rw [chapter07_maximal_power_span A K m hm π hπ q,
    chapter07_maximal_power_span A K m hm π hπ r,
    chapter07_maximal_power_span A K m hm π hπ (q + r),
    FractionalIdeal.spanSingleton_mul_spanSingleton, zpow_add₀ hπK]

private theorem chapter07_maximal_power_inv
    (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (π : A) (hπ : Irreducible π) (q : ℤ) :
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K m q)⁻¹ =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K m (-q) := by
  have hπK : algebraMap A K π ≠ 0 := by simpa using hπ.ne_zero
  rw [chapter07_maximal_power_span A K m hm π hπ q,
    chapter07_maximal_power_span A K m hm π hπ (-q),
    FractionalIdeal.spanSingleton_inv]
  congr 1
  rw [← zpow_neg]

private theorem chapter07_maximal_power_pow
    (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (π : A) (hπ : Irreducible π) (q : ℤ) (k : ℕ) :
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K m q) ^ k =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K m (q * (k : ℤ)) := by
  have hπK : algebraMap A K π ≠ 0 := by simpa using hπ.ne_zero
  rw [chapter07_maximal_power_span A K m hm π hπ q,
    chapter07_maximal_power_span A K m hm π hπ (q * (k : ℤ)),
    FractionalIdeal.spanSingleton_pow, ← zpow_natCast, ← zpow_mul]

private theorem chapter07_extended_inv
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L]
    [IsIntegralClosure B A L] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (I : FractionalIdeal A⁰ K) (hprod : I * I⁻¹ = 1) :
    FractionalIdeal.extendedHom L B I⁻¹ =
      (FractionalIdeal.extendedHom L B I)⁻¹ := by
  apply FractionalIdeal.right_inverse_eq
  calc
    FractionalIdeal.extendedHom L B I *
        FractionalIdeal.extendedHom L B I⁻¹ =
        FractionalIdeal.extendedHom L B (I * I⁻¹) := by
          rw [map_mul]
    _ = 1 := by
      rw [hprod]
      exact FractionalIdeal.extended_one L _

private theorem chapter07_extended_maximal_power
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B) (e : ℕ)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hmap :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (q : ℤ) :
    FractionalIdeal.extendedHom L B
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          A K mA q) =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        B L mB ((e : ℤ) * q) := by
  have hmA0 : mA ≠ (⊥ : Ideal A) := by
    rw [hmA]
    exact IsDiscreteValuationRing.not_a_field A
  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B
  by_cases hq : 0 ≤ q
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hq
    rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower,
      dif_pos hq, FractionalIdeal.extendedHom_coeIdeal_eq_map, Ideal.map_pow,
      FractionalIdeal.coeIdeal_pow]
    have hk' : q.toNat = k := by simpa [hk]
    rw [hk', hk, hmap, chapter07_maximal_power_pow B L mB hmB πB hπB e k]
  · have hqneg : 0 ≤ -q := by omega
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hqneg
    have hq' : q = -(k : ℤ) := by omega
    have hk' : (-q).toNat = k := by simpa [hk]
    obtain ⟨πA, hπA⟩ := IsDiscreteValuationRing.exists_irreducible A
    have hIeq :
        (↑(mA ^ k) : FractionalIdeal A⁰ K) =
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
            A K mA (k : ℤ) := by
      rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower,
        dif_pos (by exact_mod_cast Nat.zero_le k)]
      rfl
    have hprod : (↑(mA ^ k) : FractionalIdeal A⁰ K) *
        (↑(mA ^ k) : FractionalIdeal A⁰ K)⁻¹ = 1 := by
      rw [hIeq, chapter07_maximal_power_inv A K mA hmA πA hπA (k : ℤ),
        chapter07_maximal_power_mul A K mA hmA πA hπA (k : ℤ) (-(k : ℤ))]
      simp [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower]
    have hprod' : (↑(mA ^ (-q).toNat) : FractionalIdeal A⁰ K) *
        (↑(mA ^ (-q).toNat) : FractionalIdeal A⁰ K)⁻¹ = 1 := by
      simpa [hk'] using hprod
    rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower,
      dif_neg hq, chapter07_extended_inv A B K L
        (↑(mA ^ (-q).toNat) : FractionalIdeal A⁰ K)
        hprod',
      FractionalIdeal.extendedHom_coeIdeal_eq_map, Ideal.map_pow,
      FractionalIdeal.coeIdeal_pow]
    rw [hk', hq', hmap, chapter07_maximal_power_pow B L mB hmB πB hπB e k,
      chapter07_maximal_power_inv B L mB hmB πB hπB (e * (k : ℤ))]
    congr 1
    ring

private theorem chapter07_codifferent_maximal_power
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mB : Ideal B) (hmB : mB = IsLocalRing.maximalIdeal B) (d : ℕ)
    (hD : chapter07DifferentIdeal A B = mB ^ d) :
    FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        B L mB (-(d : ℤ)) := by
  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hDfrac :
      (chapter07DifferentIdeal A B : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (d : ℤ) := by
    rw [hD,
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower,
      dif_pos (by exact_mod_cast Nat.zero_le d)]
    rfl
  let C : FractionalIdeal B⁰ L := FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L)
  have hCne : C ≠ 0 := by
    dsimp [C]
    exact FractionalIdeal.dual_ne_zero A K (by simp)
  have hCinv : C * C⁻¹ = 1 := by
    exact FractionalIdeal.invertible_of_principal (R₁ := B) (K := L) C hCne
  have hDprod :
      (chapter07DifferentIdeal A B : FractionalIdeal B⁰ L) * C = 1 := by
    rw [chapter07_different_fractional_coe_eq A B K L,
      chapter07_different_fractional_is_inverse_codifferent A B K L]
    change C⁻¹ * C = 1
    simpa [mul_comm] using hCinv
  have hcodiff : C = (chapter07DifferentIdeal A B : FractionalIdeal B⁰ L)⁻¹ := by
    exact FractionalIdeal.right_inverse_eq (K := L)
      (chapter07DifferentIdeal A B : FractionalIdeal B⁰ L) C hDprod
  rw [hDfrac, chapter07_maximal_power_inv B L mB hmB πB hπB (d : ℤ)] at hcodiff
  exact hcodiff

private theorem chapter07_trace_image_subset_iff_dual
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (I : FractionalIdeal B⁰ L) (_hI : I ≠ 0)
    (J : FractionalIdeal A⁰ K) (hJ : J ≠ 0)
    (hinv : (J⁻¹)⁻¹ = J) :
    chapter07TraceImage A B K L I ⊆ (J : Set K) ↔
      I ≤ FractionalIdeal.dual A K
        (FractionalIdeal.extendedHom L B J⁻¹) := by
  have hJinv : J⁻¹ ≠ 0 := inv_ne_zero hJ
  have hE : FractionalIdeal.extendedHom L B J⁻¹ ≠ 0 := by
    intro hzero
    apply hJinv
    exact (FractionalIdeal.extendedHom_eq_zero_iff L B).mp hzero
  constructor
  · intro hsubset y hy
    rw [FractionalIdeal.mem_dual hE]
    intro a ha
    change a ∈ FractionalIdeal.extended L _ J⁻¹ at ha
    rw [FractionalIdeal.mem_extended_iff] at ha
    let P : L → Prop := fun z => ∀ y : L, y ∈ I →
      Algebra.trace K L (y * z) ∈ (algebraMap A K).range
    have hloc : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ :=
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <|
        FaithfulSMul.algebraMap_injective _ _
    have hspan : ∀ z : L,
        z ∈ Submodule.span B
          ((IsLocalization.map L (algebraMap A B) hloc) ''
            ((J⁻¹ : FractionalIdeal A⁰ K) : Set K)) → P z := by
      intro z hz
      exact Submodule.span_induction (R := B) (M := L)
        (s := (IsLocalization.map L (algebraMap A B) hloc) ''
          ((J⁻¹ : FractionalIdeal A⁰ K) : Set K))
        (p := fun z _ => P z)
        (mem := by
          intro z hz
          rcases hz with ⟨x, hx, hxz⟩
          intro y hy
          rw [← hxz]
          have hx' : x ∈ (J⁻¹ : FractionalIdeal A⁰ K) := by exact hx
          have hyJ : Algebra.trace K L y ∈ J := hsubset ⟨y, hy, rfl⟩
          have hxy := (FractionalIdeal.mem_inv_iff hJ).mp hx' _ hyJ
          obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff A⁰).mp hxy
          refine ⟨c, ?_⟩
          calc
            algebraMap A K c = x * Algebra.trace K L y := hc
            _ = Algebra.trace K L
                (y * IsLocalization.map L (algebraMap A B) hloc x) := by
              have hxmap : IsLocalization.map L (algebraMap A B) hloc x =
                  algebraMap K L x :=
                DFunLike.congr_fun
                  (IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L).symm x
              rw [hxmap, mul_comm y, ← Algebra.smul_def,
                LinearMap.map_smul_of_tower]
              simp)
        (zero := by
          intro y hy
          simp)
        (add := by
          intro y z _ _ hy hz w hw
          obtain ⟨c, hc⟩ := hy w hw
          obtain ⟨d, hd⟩ := hz w hw
          refine ⟨c + d, ?_⟩
          calc
            algebraMap A K (c + d) = algebraMap A K c + algebraMap A K d := map_add _ _ _
            _ = Algebra.trace K L (w * y) + Algebra.trace K L (w * z) := by rw [hc, hd]
            _ = Algebra.trace K L (w * (y + z)) := by rw [mul_add, map_add])
        (smul := by
          intro b z _ hz w hw
          have hbw : b • w ∈ I := (I : Submodule B L).smul_mem b hw
          obtain ⟨c, hc⟩ := hz (b • w) hbw
          refine ⟨c, ?_⟩
          simpa [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using hc)
        hz
    exact hspan a ha y hy
  · intro hle x hx
    change x ∈ J
    rw [← hinv]
    rw [FractionalIdeal.mem_inv_iff hJinv]
    rcases hx with ⟨y, hy, rfl⟩
    intro z hz
    have hydual := (FractionalIdeal.mem_dual hE).mp (hle hy)
    have hzE : algebraMap K L z ∈
        (FractionalIdeal.extendedHom L B J⁻¹ : FractionalIdeal B⁰ L) := by
      change algebraMap K L z ∈ FractionalIdeal.extended L _ J⁻¹
      rw [FractionalIdeal.mem_extended_iff]
      exact Submodule.subset_span ⟨z, hz, by
        exact DFunLike.congr_fun
          (IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L).symm z⟩
    obtain ⟨c, hc⟩ := hydual _ hzE
    exact (FractionalIdeal.mem_one_iff A⁰).mpr ⟨c, by
      calc
        algebraMap A K c = Algebra.trace K L (y * algebraMap K L z) := hc
        _ = Algebra.trace K L y * z := by
          calc
            Algebra.trace K L (y * algebraMap K L z) =
                Algebra.trace K L (algebraMap K L z * y) := by rw [mul_comm]
            _ = Algebra.trace K L (z • y) := by rw [Algebra.smul_def]
            _ = z • Algebra.trace K L y := by
              rw [LinearMap.map_smul_of_tower]
            _ = Algebra.trace K L y * z := by simp [mul_comm]
      ⟩

private theorem chapter07_trace_floor_le_iff
    (n : ℤ) (d e : ℕ) (he : 0 < e) (r : ℤ) :
    r ≤ chapter07TraceImageExponent n d e ↔
      (e : ℤ) * r ≤ n + (d : ℤ) := by
  rw [chapter07TraceImageExponent, chapter07FloorDiv,
    Int.le_ediv_iff_mul_le (by exact_mod_cast he)]
  simp [mul_comm]

private theorem chapter07_trace_fractional_power_contained_iff_aux
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B) (e d : ℕ)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (he : 0 < e)
    (hmap :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (hD : chapter07DifferentIdeal A B = mB ^ d) (n r : ℤ) :
    chapter07TraceImage A B K L
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB n) ⊆
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K mA r : Set K) ↔
        r ≤ chapter07TraceImageExponent n d e := by
  obtain ⟨πA, hπA⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hI :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        B L mB n ≠ 0 := by
    rw [chapter07_maximal_power_span B L mB hmB πB hπB n]
    exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (zpow_ne_zero n (by simpa using hπB.ne_zero))
  have hJ :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K mA r ≠ 0 := by
    rw [chapter07_maximal_power_span A K mA hmA πA hπA r]
    exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (zpow_ne_zero r (by simpa using hπA.ne_zero))
  have hinv :
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K mA r)⁻¹⁻¹ =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          A K mA r := by
    rw [chapter07_maximal_power_inv A K mA hmA πA hπA r,
      chapter07_maximal_power_inv A K mA hmA πA hπA (-r)]
    congr 1
    ring
  rw [chapter07_trace_image_subset_iff_dual A B K L _ hI _ hJ hinv]
  rw [FractionalIdeal.dual_eq_mul_inv,
    chapter07_codifferent_maximal_power A B K L mB hmB d hD]
  rw [chapter07_maximal_power_inv A K mA hmA πA hπA r,
    chapter07_extended_maximal_power A B K L mA mB e hmA hmB hmap (-r)]
  rw [chapter07_maximal_power_inv B L mB hmB πB hπB ((e : ℤ) * (-r))]
  have hneg : -((e : ℤ) * (-r)) = (e : ℤ) * r := by ring
  rw [hneg, chapter07_maximal_power_mul B L mB hmB πB hπB
    (-(d : ℤ)) ((e : ℤ) * r)]
  rw [chapter07_maximal_power_le_iff B L mB hmB n
    (-(d : ℤ) + (e : ℤ) * r)]
  constructor
  · intro h
    apply (chapter07_trace_floor_le_iff n d e he r).mpr
    omega
  · intro h
    have h' := (chapter07_trace_floor_le_iff n d e he r).mp h
    omega

/-- The exact trace-image formula for all integral and fractional powers. -/
theorem chapter07_trace_fractional_power_formula
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B) (e d : ℕ)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (he : 0 < e)
    (hmap :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (hD : chapter07DifferentIdeal A B = mB ^ d) (n : ℤ) :
    chapter07TraceImage A B K L
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB n) =
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K mA
        (chapter07TraceImageExponent n d e) : Set K) := by
  let I :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
      B L mB n
  let J :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
      A K mA (chapter07TraceImageExponent n d e)
  have hsubset : chapter07TraceImage A B K L I ⊆ (J : Set K) :=
    (chapter07_trace_fractional_power_contained_iff_aux A B K L mA mB e d
      hmA hmB he hmap hD n (chapter07TraceImageExponent n d e)).mpr le_rfl
  have hI : I ≠ 0 := by
    dsimp [I]
    obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B
    rw [chapter07_maximal_power_span B L mB hmB πB hπB n]
    exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (zpow_ne_zero n (by simpa using hπB.ne_zero))
  obtain ⟨T, hTset, hTne⟩ :=
    chapter07_trace_image_as_fractional_ideal A B K L I hI J hsubset
  obtain ⟨s, hs, _⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04_nonzero_fractional_ideal_is_maximal_power
      A K T hTne
  have hs' : T =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K mA s := by
    simpa [hmA] using hs
  have hTleq : T ≤ J := by
    intro x hx
    apply hsubset
    rw [← hTset]
    exact hx
  have hqle : chapter07TraceImageExponent n d e ≤ s := by
    rw [hs'] at hTleq
    exact (chapter07_maximal_power_le_iff A K mA hmA s
      (chapter07TraceImageExponent n d e)).mp hTleq
  have hsub_s : chapter07TraceImage A B K L I ⊆
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K mA s : Set K) := by
    rw [← hs', ← hTset]
  have hsle : s ≤ chapter07TraceImageExponent n d e :=
    (chapter07_trace_fractional_power_contained_iff_aux A B K L mA mB e d
      hmA hmB he hmap hD n s).mp hsub_s
  have hqT :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K mA (chapter07TraceImageExponent n d e) ≤ T := by
    rw [hs']
    exact (chapter07_maximal_power_le_iff A K mA hmA
      (chapter07TraceImageExponent n d e) s).mpr hsle
  have hTeq : T = J := le_antisymm hTleq hqT
  calc
    chapter07TraceImage A B K L I = (T : Set K) := hTset.symm
    _ = (J : Set K) := by rw [hTeq]

theorem chapter07_trace_fractional_power_contained_iff
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B) (e d : ℕ)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (he : 0 < e)
    (hmap :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (hD : chapter07DifferentIdeal A B = mB ^ d) (n r : ℤ) :
    chapter07TraceImage A B K L
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB n) ⊆
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
        A K mA r : Set K) ↔
        r ≤ chapter07TraceImageExponent n d e := by
  exact chapter07_trace_fractional_power_contained_iff_aux A B K L mA mB e d
    hmA hmB he hmap hD n r

def chapter07IntegralRingSet
    (B L : Type*) [CommRing B] [Field L] [Algebra B L] : Set L :=
  Set.range (algebraMap B L)

def chapter07MaximalIdealSet
    (B L : Type*) [CommRing B] [Field L] [Algebra B L]
    (mB : Ideal B) : Set L :=
  {x | ∃ b : B, b ∈ mB ∧ x = algebraMap B L b}

private theorem chapter07_fractional_power_zero_set
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (m : Ideal A) :
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
      A K m (0 : ℤ) : Set K) = chapter07IntegralRingSet A K := by
  ext x
  simp [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower,
    chapter07IntegralRingSet]

private theorem chapter07_fractional_power_one_set
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (m : Ideal A) :
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
      A K m (1 : ℤ) : Set K) = chapter07MaximalIdealSet A K m := by
  ext x
  simp [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower,
    chapter07MaximalIdealSet]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, hx⟩
    exact ⟨b, hb, hx.symm⟩

theorem chapter07_unramified_exact_integral_trace
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hmap :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (1 : ℤ))
    (hD : chapter07DifferentIdeal A B = mB ^ 0) :
    Algebra.trace K L '' chapter07IntegralRingSet B L =
        Set.range (algebraMap A K) ∧
      Algebra.trace K L '' chapter07MaximalIdealSet B L mB =
        chapter07MaximalIdealSet A K mA := by
  constructor
  · have hzero := chapter07_trace_fractional_power_formula A B K L mA mB 1 0
      hmA hmB (by omega) hmap hD 0
    simpa [chapter07TraceImage, chapter07TraceImageExponent, chapter07FloorDiv,
      chapter07IntegralRingSet,
      chapter07_fractional_power_zero_set] using hzero
  · have hone := chapter07_trace_fractional_power_formula A B K L mA mB 1 0
      hmA hmB (by omega) hmap hD 1
    simpa [chapter07TraceImage, chapter07TraceImageExponent, chapter07FloorDiv,
      chapter07_fractional_power_one_set] using hone

theorem chapter07_tame_exact_integral_and_maximal_trace
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A]
    [Module.Finite A B] [Module.Free A B] [Module.IsTorsionFree A B]
    [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B) (e : ℕ)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (he : 0 < e)
    (hmap :
      (Ideal.map (algebraMap A B) mA : FractionalIdeal B⁰ L) =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04FractionalIdealPower
          B L mB (e : ℤ))
    (hD : chapter07DifferentIdeal A B = mB ^ (e - 1)) :
    Algebra.trace K L '' chapter07IntegralRingSet B L =
        Set.range (algebraMap A K) ∧
      Algebra.trace K L '' chapter07MaximalIdealSet B L mB =
        chapter07MaximalIdealSet A K mA := by
  have hecast' : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by
    omega
  have hq0 : chapter07TraceImageExponent 0 (e - 1) e = 0 := by
    have hnon : 0 ≤ chapter07TraceImageExponent 0 (e - 1) e := by
      apply (chapter07_trace_floor_le_iff 0 (e - 1) e he 0).mpr
      rw [hecast']
      omega
    have hnot : ¬(1 : ℤ) ≤ chapter07TraceImageExponent 0 (e - 1) e := by
      intro h
      have h' := (chapter07_trace_floor_le_iff 0 (e - 1) e he 1).mp h
      rw [hecast'] at h'
      omega
    omega
  have hq1 : chapter07TraceImageExponent 1 (e - 1) e = 1 := by
    have hge : (1 : ℤ) ≤ chapter07TraceImageExponent 1 (e - 1) e := by
      apply (chapter07_trace_floor_le_iff 1 (e - 1) e he 1).mpr
      rw [hecast']
      omega
    have hnot : ¬(2 : ℤ) ≤ chapter07TraceImageExponent 1 (e - 1) e := by
      intro h
      have h' := (chapter07_trace_floor_le_iff 1 (e - 1) e he 2).mp h
      rw [hecast'] at h'
      omega
    omega
  constructor
  · have hzero := chapter07_trace_fractional_power_formula A B K L mA mB e (e - 1)
      hmA hmB he hmap hD 0
    simpa [chapter07TraceImage, chapter07IntegralRingSet, hq0,
      chapter07_fractional_power_zero_set] using hzero
  · have hone := chapter07_trace_fractional_power_formula A B K L mA mB e (e - 1)
      hmA hmB he hmap hD 1
    simpa [chapter07TraceImage, hq1, chapter07_fractional_power_one_set] using hone

/- The quadratic trace computation used for `Q_2(sqrt 2)`. -/
def chapter07QuadraticTraceModel
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (θ : L) : Prop :=
  Module.finrank K L = 2 ∧ Algebra.trace K L θ = 0

theorem chapter07_quadratic_trace_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (θ : L)
    (hmodel : chapter07QuadraticTraceModel K L θ) (a b : K) :
    Algebra.trace K L
        (algebraMap K L a + algebraMap K L b * θ) = 2 * a := by
  rcases hmodel with ⟨hfinrank, hθ⟩
  rw [map_add, Algebra.trace_algebraMap]
  rw [← Algebra.smul_def, LinearMap.map_smul, hθ, smul_zero, add_zero]
  rw [hfinrank]
  norm_num

theorem chapter07_sqrt_two_trace_formula
    (L : Type*) [Field L] [Algebra ℚ_[2] L]
    [FiniteDimensional ℚ_[2] L] (sqrtTwo : L)
    (hmodel : chapter07QuadraticTraceModel ℚ_[2] L sqrtTwo)
    (_hsquare : sqrtTwo ^ 2 = algebraMap ℚ_[2] L 2) (a b : ℚ_[2]) :
    Algebra.trace ℚ_[2] L
        (algebraMap ℚ_[2] L a + algebraMap ℚ_[2] L b * sqrtTwo) = 2 * a := by
  exact chapter07_quadratic_trace_formula ℚ_[2] L sqrtTwo hmodel a b

theorem chapter07_sqrt_two_integral_trace_is_two_adic
    (L : Type*) [Field L] [Algebra ℚ_[2] L]
    [FiniteDimensional ℚ_[2] L] (sqrtTwo : L)
    (hmodel : chapter07QuadraticTraceModel ℚ_[2] L sqrtTwo)
    (hsquare : sqrtTwo ^ 2 = algebraMap ℚ_[2] L 2) :
    ∀ a b : ℚ_[2],
      Algebra.trace ℚ_[2] L
        (algebraMap ℚ_[2] L a + algebraMap ℚ_[2] L b * sqrtTwo) =
        2 * a := by
  intro a b
  exact chapter07_sqrt_two_trace_formula L sqrtTwo hmodel hsquare a b

/- The exact linear term in the norm expansion, with the higher terms named. -/
theorem chapter07_norm_one_add_trace_remainder
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.norm K (1 + x) =
      1 + Algebra.trace K L x +
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormRemainder
          K L x := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_norm_one_add_linearizes_to_trace
    K L x

/-- A precise predicate for the norm-lifting obstruction mentioned after the
    first-order expansion. -/
def chapter07NormLiftingFailure
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    (unitLayerL : Set L) (unitLayerK : Set K) : Prop :=
  Function.Surjective (Algebra.norm k (S := l)) ∧
    ¬Set.SurjOn (Algebra.norm K (S := L)) unitLayerL unitLayerK

end

end LastLib.Book03RamificationTheory.Chapter07
