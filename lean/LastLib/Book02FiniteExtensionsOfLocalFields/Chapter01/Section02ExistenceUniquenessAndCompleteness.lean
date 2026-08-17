import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section01TheExtensionProblem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section02ExistenceByMaximalDomination
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section03IntegralElementsAreBounded
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section04RamificationIndexAndResidueDegree
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section05SplittingPatterns
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section05UniqueExtensionAndHenselianity

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01

noncomputable section

universe u

open scoped Polynomial TensorProduct WithZero

/-! # Book 2, Chapter 1, Section 1.2

This file records the henselian-versus-complete distinction and the concrete
Gaussian example at the prime `5`; the uniqueness bridge is exported by the
leaf interface in Section 1.1 so later chapter modules can import it without
creating an import cycle through this section.
-/

/-! ### Existence, uniqueness, and branches

The statements in this section keep the algebraic extension interface separate
from the later finite-dimensional local-field interface.
-/

/-- The valuation-theoretic extension theorem, in valuation-subring form. -/
theorem chapter01_algebraic_extension_exists
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) :
    ∃ W : ValuationSubring L,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ContractsTo
        vK.valuationSubring.toSubring W.toSubring := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_algebraic_valuation_extension_exists vK

/-! ### The prime/valuation branch interface -/

/-- In a finite field extension, valuation branches are parametrized by primes
of an integral model above the base maximal ideal. -/
theorem chapter01_finite_extension_prime_valuation_correspondence
    {A B K L Γ : Type*} [CommRing A] [IsDomain A]
    [ValuationRing A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ExtensionPrimeCorrespondence
      (A := A) (B := B) (L := L) vK hA := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_finite_extension_prime_valuation_correspondence
    vK hA

/-- The prime/valuation correspondence turns uniqueness of a branch into
uniqueness of the corresponding maximal ideal, and conversely. -/
theorem chapter01_unique_prime_iff_unique_valuation_extension
    {A B K L Γ : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [IsIntegrallyClosed A]
    [Field K] [Field L] [CommRing B] [Algebra A B] [Algebra B L]
    [Algebra A L] [IsScalarTower A B L] [IsIntegralClosure B A L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L]
    [IsScalarTower A K L]
    [LinearOrderedCommGroupWithZero Γ] (vK : Valuation K Γ)
    (hA : vK.Integers A)
    (hcor :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ExtensionPrimeCorrespondence
        (A := A) (B := B) (L := L) vK hA) :
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HasUniquePrimeAbove
        (A := A) (B := B) ↔
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HasUniqueValuationExtension
        (L := L) vK) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_unique_prime_iff_unique_valuation_extension
    vK hA hcor

/-- A heterogeneous extension is discrete when its canonical value group is
discrete. A branch may use an ambient ordered codomain larger than the image
of its valuation, so discreteness must not be imposed on that arbitrary
codomain. -/
def chapter01DiscreteHeterogeneousExtension
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    (W : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension vK L) : Prop :=
  let _ : LinearOrderedCommGroupWithZero W.valueGroup := W.orderedValueGroup
  Nonempty
    (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass W.valuation) ≃*o ℤᵐ⁰)

private theorem chapter01_finite_index_cyclic_ordered_group_is_cyclic
    {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    (H : Subgroup G) [H.FiniteIndex] [IsCyclic H] [Nontrivial H] :
    IsCyclic G := by
  classical
  obtain ⟨h, hh⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp
      (inferInstance : IsCyclic H)
  have hh1 : h ≠ 1 := by
    intro h1
    obtain ⟨x, hx⟩ := exists_ne (1 : H)
    have hxH : (x : G) ∈ H := x.property
    have hxzp : (x : G) ∈ Subgroup.zpowers h := hh.symm ▸ hxH
    rw [h1] at hxzp
    exact hx (Subtype.ext (by simpa using hxzp))
  let a : G := max h h⁻¹
  have ha : 1 < a := by
    dsimp [a]
    by_cases hpos : 1 < h
    · exact lt_of_lt_of_le hpos (le_max_left _ _)
    · have hneg : h < 1 := lt_of_le_of_ne (le_of_not_gt hpos) hh1
      exact lt_of_lt_of_le (one_lt_inv'.mpr hneg) (le_max_right _ _)
  have haH : Subgroup.zpowers a = H := by
    dsimp [a]
    rcases max_cases h h⁻¹ with hcase | hcase
    · rw [hcase.1, hh]
    · rw [hcase.1, Subgroup.zpowers_inv, hh]
  have hpow (x : G) : ∃ m : ℤ, x ^ H.index = a ^ m := by
    have hxH : x ^ H.index ∈ H := H.pow_index_mem x
    have hindex : (Subgroup.zpowers a).index = H.index := congrArg Subgroup.index haH
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (haH.symm ▸ hxH)
    rw [hindex] at hm
    exact ⟨m, hm.symm⟩
  have harch : MulArchimedean G := by
    constructor
    intro x y hy
    obtain ⟨r, hr⟩ := hpow y
    have hindex : 0 < H.index :=
      Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    have hyindex : 1 < y ^ H.index := by
      simpa using pow_lt_pow_right' hy (Nat.zero_lt_of_lt hindex)
    have har : 1 < a ^ r := hr ▸ hyindex
    have hrpos : (0 : ℤ) < r := by
      apply (zpow_right_strictMono ha).lt_iff_lt.mp
      simpa using har
    by_cases hx : x ≤ 1
    · exact ⟨0, by simpa using hx⟩
    · have hxpos : 1 < x := lt_of_not_ge hx
      obtain ⟨m, hm⟩ := hpow x
      have hxm : x ≤ a ^ m := by
        calc
          x ≤ x ^ H.index := by
            simpa using pow_le_pow_right' (le_of_lt hxpos)
              (Nat.one_le_iff_ne_zero.mpr hindex.ne')
          _ = a ^ m := hm
      have hmpos : (0 : ℤ) < m := by
        apply (zpow_right_strictMono ha).lt_iff_lt.mp
        exact (by simpa [hm] using hxpos.trans_le hxm)
      let mn : ℕ := m.toNat
      have hmcast : (mn : ℤ) = m := by
        exact Int.toNat_of_nonneg (le_of_lt hmpos)
      refine ⟨H.index * mn, ?_⟩
      calc
        x ≤ a ^ (mn : ℤ) := by simpa [hmcast] using hxm
        _ ≤ a ^ (r * (mn : ℤ)) := by
          apply zpow_le_zpow_right ha.le
          have hmn : (0 : ℤ) ≤ mn := by positivity
          nlinarith [hrpos]
        _ = (a ^ r) ^ mn := by
          rw [zpow_mul, zpow_natCast]
        _ = (y ^ H.index) ^ mn := by rw [← hr]
        _ = y ^ (H.index * mn) := by rw [pow_mul]
  let _ : MulArchimedean G := harch
  have hgap : Disjoint (H : Set G) (Set.Ioo 1 a) := by
    rw [Set.disjoint_left]
    intro z hzH hzI
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (haH.symm ▸ hzH)
    have hkpos : (0 : ℤ) < k := by
      apply (zpow_right_strictMono ha).lt_iff_lt.mp
      simpa [hk] using hzI.1
    have hklt : k < 1 := by
      apply (zpow_right_strictMono ha).lt_iff_lt.mp
      simpa [hk] using hzI.2
    omega
  have hcontra {u v : G} (hu : u ∈ Set.Ioo 1 a) (hv : v ∈ Set.Ioo 1 a)
      (huv : u < v) (hquot : QuotientGroup.mk' H u = QuotientGroup.mk' H v) :
      False := by
    obtain ⟨z, hz, huvz⟩ := (QuotientGroup.mk'_eq_mk' H).mp hquot
    have hz_eq : z = u⁻¹ * v := by
      calc
        z = 1 * z := by rw [one_mul]
        _ = (u⁻¹ * u) * z := by simp
        _ = u⁻¹ * (u * z) := by rw [mul_assoc]
        _ = u⁻¹ * v := by rw [huvz]
    have hzI : z ∈ Set.Ioo 1 a := by
      constructor
      · rw [hz_eq]
        have hmul := mul_lt_mul_left huv u⁻¹
        simpa [mul_comm] using hmul
      · rw [hz_eq]
        calc
          u⁻¹ * v < v := by
            have hmul := mul_lt_mul_left (inv_lt_one_of_one_lt hu.1) v
            simpa using hmul
          _ < a := hv.2
    exact Set.disjoint_left.1 hgap hz hzI
  have hq_injective :
      Function.Injective (fun x : Set.Ioo (1 : G) a => QuotientGroup.mk' H x) := by
    intro x y hxy
    rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
    · exact (hcontra x.2 y.2 hlt hxy).elim
    · exact Subtype.ext heq
    · exact (hcontra y.2 x.2 hgt hxy.symm).elim
  let _ : Finite (G ⧸ H) :=
    (Subgroup.finiteIndex_iff_finite_quotient (H := H)).mp inferInstance
  have hIoo : Finite (Set.Ioo (1 : G) a) :=
    Finite.of_injective (fun x : Set.Ioo (1 : G) a => QuotientGroup.mk' H x) hq_injective
  have hnotdense : ¬ DenselyOrdered G := by
    intro hdense
    exact (not_finite_iff_infinite.mpr
      (@Set.Ioo.infinite G _ hdense 1 a ha)) hIoo
  let _ : Nontrivial G := ⟨⟨a, 1, ne_of_gt ha⟩⟩
  exact (LinearOrderedCommGroup.isCyclic_iff_not_denselyOrdered (G := G)).mpr hnotdense

/-- Finite algebraic extensions of a discrete field have discrete extension values. -/
theorem chapter01_finite_extension_value_group_is_discrete
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK] :
    ∀ W : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension vK L,
      chapter01DiscreteHeterogeneousExtension vK W := by
  intro W
  let _ : LinearOrderedCommGroupWithZero W.valueGroup := W.orderedValueGroup
  change Nonempty
    (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass W.valuation) ≃*o ℤᵐ⁰)
  obtain ⟨data⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_heterogeneous_extension_data_exists
      vK W.valuation W.isExtension
  have hhom :
      W.valuation.toMonoidWithZeroHom = MonoidWithZeroHom.ofClass W.valuation := by
    ext x
    rfl
  have hvalueGroup_eq :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup W.valuation =
        MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass W.valuation) := by
    simp only [LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup,
      hhom]
  let H := data.valueGroupMap.range
  have hfinite :
      Finite
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup W.valuation ⧸ H) := by
    simpa [H] using data.finite_quotient
  have hfiniteIndex : H.FiniteIndex :=
    (Subgroup.finiteIndex_iff_finite_quotient (H := H)).mpr hfinite
  let _ : H.FiniteIndex := hfiniteIndex
  have hsourceCyclic :
      IsCyclic
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK) := by
    change IsCyclic (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass vK))
    infer_instance
  let _ : IsCyclic
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK) :=
    hsourceCyclic
  have hrangeCyclic : IsCyclic H := by
    exact isCyclic_of_surjective _ data.valueGroupMap.rangeRestrict_surjective
  let _ : IsCyclic H := hrangeCyclic
  have hsourceNontrivial :
      Nontrivial
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK) := by
    change Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass vK))
    infer_instance
  let _ : Nontrivial
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK) :=
    hsourceNontrivial
  have hinjective : Function.Injective data.valueGroupMap.rangeRestrict := by
    intro x y hxy
    exact data.valueGroupMap_injective (congrArg Subtype.val hxy)
  let _ : Nontrivial H := hinjective.nontrivial
  have htargetCyclic :
      IsCyclic
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup W.valuation) :=
    chapter01_finite_index_cyclic_ordered_group_is_cyclic H
  let _ : IsCyclic
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup W.valuation) :=
    htargetCyclic
  have htargetCyclic' :
      IsCyclic (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass W.valuation)) := by
    rw [← hvalueGroup_eq]
    exact htargetCyclic
  have hincl :
      Function.Injective
        (fun x : H =>
          (x : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup
            W.valuation)) := by
    intro x y hxy
    exact Subtype.ext hxy
  have htargetNontrivial :
      Nontrivial
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup W.valuation) := by
    exact hincl.nontrivial
  have htargetNontrivial' :
      Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass W.valuation)) := by
    rw [← hvalueGroup_eq]
    exact htargetNontrivial
  let _ : IsCyclic
      (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass W.valuation)) := htargetCyclic'
  let _ : Nontrivial
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup W.valuation) :=
    htargetNontrivial
  let _ : Nontrivial
      (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass W.valuation)) :=
    htargetNontrivial'
  let _ : Valuation.IsRankOneDiscrete W.valuation :=
    Valuation.IsRankOneDiscrete.mk' W.valuation
  exact ⟨Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt W.valuation⟩

/-- The finite part of Theorem 1.1 packages uniqueness and discreteness of
the extension branches in one interface. -/
theorem chapter01_theorem_1_1_finite
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L ∧
      ∀ W :
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension
          vK L,
        chapter01DiscreteHeterogeneousExtension vK W := by
  exact ⟨chapter01_theorem_1_1 vK hcomplete,
    chapter01_finite_extension_value_group_is_discrete vK⟩

/-! ### The canonical finite value-group quotient -/

/-- A finite branch carries a canonical finite quotient of value groups. -/
theorem chapter01_heterogeneous_value_group_quotient_is_finite
    {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL] [FiniteDimensional K L]
    (vK : Valuation K ΓK) (vL : Valuation L ΓL)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L))) :
    ∃ data :
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
          vK vL hext,
      Finite
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL ⧸
          data.valueGroupMap.range) := by
  obtain ⟨data⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_heterogeneous_extension_data_exists
      vK vL hext
  exact ⟨data, data.finite_quotient⟩

/-- The value-group quotient in a finite extension is finite. -/
theorem chapter01_finite_value_group_quotient_is_finite
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hext : chapter01SamePlace vK vL)
    (hΓ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK ≤
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL) :
    Finite
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL ⧸
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK).subgroupOf
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL)) := by
  classical
  have _ := hext
  let G :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL
  let H : Subgroup G :=
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK).subgroupOf
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL)
  change Finite (G ⧸ H)
  have hGcyc : IsCyclic G := by
    change IsCyclic
      (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass vL))
    infer_instance
  have hGnontrivial : Nontrivial G := by
    change Nontrivial
      (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass vL))
    infer_instance
  let e : Multiplicative ℤ ≃*o G :=
    ((LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int (G := G)).mp hGcyc).some.symm
  let H' : Subgroup (Multiplicative ℤ) := H.comap e.toMonoidHom
  have hH : H ≠ ⊥ := by
    intro hbot
    have hgen :
        Valuation.IsRankOneDiscrete.generator vK ∈
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK :=
      Valuation.IsRankOneDiscrete.generator_mem_valueGroup vK
    have hgen' :
        (Valuation.IsRankOneDiscrete.generator vK : Γˣ) ∈
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL :=
      hΓ hgen
    have hgenH :
        (⟨(Valuation.IsRankOneDiscrete.generator vK : Γˣ), hgen'⟩ : G) ∈ H := by
      change (⟨(Valuation.IsRankOneDiscrete.generator vK : Γˣ), hgen'⟩ : G).val ∈
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK
      exact hgen
    have hgenHbot :
        (⟨(Valuation.IsRankOneDiscrete.generator vK : Γˣ), hgen'⟩ : G) ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hgenH
    have hgen_eq_one :
        (⟨(Valuation.IsRankOneDiscrete.generator vK : Γˣ), hgen'⟩ : G) = 1 :=
      (Subgroup.mem_bot.mp hgenHbot)
    have hgen_ne_one :
        (⟨(Valuation.IsRankOneDiscrete.generator vK : Γˣ), hgen'⟩ : G) ≠ 1 := by
      intro h
      have : (Valuation.IsRankOneDiscrete.generator vK : Γˣ) = 1 := by
        exact congrArg Subtype.val h
      exact (ne_of_lt (Valuation.IsRankOneDiscrete.generator_lt_one vK)) this
    exact hgen_ne_one hgen_eq_one
  have hH' : H' ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hxH, hx1⟩ := (Subgroup.bot_or_exists_ne_one H).resolve_left hH
    let y : Multiplicative ℤ := e.symm x
    have hyH : y ∈ H' := by
      change e y ∈ H
      change e (e.symm x) ∈ H
      rw [e.apply_symm_apply]
      exact hxH
    have hy1 : y ≠ 1 := by
      intro hy
      apply hx1
      have : e y = e 1 := by rw [hy]
      simpa [y] using e.injective this
    have hybot : y ∈ (⊥ : Subgroup (Multiplicative ℤ)) := by
      rw [← hbot]
      exact hyH
    exact hy1 (Subgroup.mem_bot.mp hybot)
  have hH'add : H'.toAddSubgroup' ≠ ⊥ := by
    intro hbot
    apply hH'
    apply Subgroup.toAddSubgroup'.injective
    exact hbot
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic H'.toAddSubgroup'
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hH'add
    rw [ha, ha0]
    exact AddSubgroup.closure_singleton_zero
  have hfinite_add : H'.toAddSubgroup'.FiniteIndex := by
    rw [ha, ← AddSubgroup.zmultiples_eq_closure, AddSubgroup.finiteIndex_iff,
      Int.index_zmultiples]
    exact Int.natAbs_ne_zero.mpr ha0
  have hfinite' : H'.FiniteIndex := by
    have hfinite'' : (H'.toAddSubgroup').toSubgroup.FiniteIndex :=
      (AddSubgroup.finiteIndex_toSubgroup_iff H'.toAddSubgroup').mpr hfinite_add
    simpa using hfinite''
  have hfinite : H.FiniteIndex := by
    refine ⟨?_⟩
    have hindex : H'.index = H.index := by
      apply Subgroup.index_comap_of_surjective (H := H) (f := e.toMonoidHom)
      intro x
      refine ⟨e.symm x, ?_⟩
      simp
    rw [← hindex]
    exact hfinite'.index_ne_zero
  exact (Subgroup.finiteIndex_iff_finite_quotient (H := H)).mp hfinite

/-- A discrete value group has a canonical ordered integer model. -/
theorem chapter01_discrete_value_group_can_be_normalized
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Valuation.IsRankOneDiscrete v] :
    Nonempty
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v) ≃*o ℤᵐ⁰) := by
  exact ⟨Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v⟩

/-- The finite normalization is local over a henselian valuation ring. -/
theorem chapter01_henselian_integral_closure_is_local
    {A K L : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [HenselianLocalRing A]
    (hfinite : Module.Finite A (integralClosure A L)) :
    IsLocalRing (integralClosure A L) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.henselian_local_ring_integral_closure_is_local
    (A := A) (K := K) (L := L) hfinite

/-- Maximal ideals above the base maximal ideal are the finite-extension branches. -/
theorem chapter01_henselian_branch_is_unique
    {A K L : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [HenselianLocalRing A]
    (hfinite : Module.Finite A (integralClosure A L)) :
    ∃! P : Ideal (integralClosure A L),
      P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal A) := by
  let _ : IsLocalRing (integralClosure A L) :=
    chapter01_henselian_integral_closure_is_local (A := A) (K := K) (L := L) hfinite
  have halg_injective : Function.Injective (algebraMap A (integralClosure A L)) := by
    intro a b hab
    apply (FaithfulSMul.algebraMap_injective A K)
    apply (FaithfulSMul.algebraMap_injective K L)
    rw [← IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply A K L]
    have habL := congrArg (fun x : integralClosure A L => (x : L)) hab
    change algebraMap (integralClosure A L) L
        (algebraMap A (integralClosure A L) a) =
      algebraMap (integralClosure A L) L
        (algebraMap A (integralClosure A L) b) at habL
    rw [← IsScalarTower.algebraMap_apply A (integralClosure A L) L,
      ← IsScalarTower.algebraMap_apply A (integralClosure A L) L] at habL
    exact habL
  let _ : FaithfulSMul A (integralClosure A L) :=
    (faithfulSMul_iff_algebraMap_injective A (integralClosure A L)).mpr
      halg_injective
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := A) (S := integralClosure A L) (IsLocalRing.maximalIdeal A)
  refine ⟨P, ⟨hPmax, hPover⟩, ?_⟩
  intro Q hQ
  exact (IsLocalRing.eq_maximalIdeal hQ.1).trans
    (IsLocalRing.eq_maximalIdeal hPmax).symm

/-! ### The nonhenselian `5`-adic Gaussian example -/

/-- Irreducibility supplies the field instance for Book 1's Gaussian presentation. -/
theorem chapter01_gaussian_polynomial_irreducible :
    Irreducible
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hnat :
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ).natDegree = 2 := by
      simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial] using
        (Polynomial.natDegree_X_pow_add_C (R := ℚ) (n := 2) (r := (1 : ℚ)))
    rw [hnat]
    norm_num
  · intro x hx
    have hx' : x ^ 2 + 1 = 0 := by
      simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
        Polynomial.IsRoot] using hx
    nlinarith [sq_nonneg x]

noncomputable instance chapter01GaussianPolynomialIrreducible :
    Fact (Irreducible
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ)) :=
  ⟨chapter01_gaussian_polynomial_irreducible⟩

/-- The normalized `5`-adic valuation on the rational field. -/
abbrev chapter01FiveAdicValuation [Fact (Nat.Prime 5)] : Valuation ℚ ℤᵐ⁰ :=
  Rat.padicValuation 5

/-- Two inequivalent extension places, retaining Book 1's heterogeneous groups. -/
def chapter01TwoInequivalentValuationExtensions
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] (vK : Valuation K ΓK) : Prop :=
  ∃ w₁ w₂ :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousValuationExtension
        L vK,
    ¬ LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValuationExtensionsEquivalent
      vK w₁ w₂

/-- `X² + 1` has two distinct roots modulo `5`. -/
theorem chapter01_gaussian_mod_five_has_two_distinct_roots
    [Fact (Nat.Prime 5)] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11SimpleResidueRoots (ZMod 5)
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial (ZMod 5)) := by
  simpa using
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_gaussian_odd_prime_one_mod_four_has_two_roots
      5 (by decide) (by decide))

/-- The two residue roots lift to two distinct linear factors over `ℚ₅`. -/
theorem chapter01_gaussian_polynomial_splits_over_five_adics
    [Fact (Nat.Prime 5)] :
    ∃ a b : ℚ_[5], a ≠ b ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial (ℚ_[5]) =
        (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) := by
  have hderiv :
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).derivative.aeval
          (2 : ℤ_[5]) = (4 : ℤ_[5]) := by
    simp [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
      Polynomial.aeval_def]
  have hval :
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).aeval
          (2 : ℤ_[5]) = (5 : ℤ_[5]) := by
    norm_num [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
      Polynomial.aeval_def]
  have hnorm :
      ‖(LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).aeval
          (2 : ℤ_[5])‖ <
        ‖(LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).derivative.aeval
          (2 : ℤ_[5])‖ ^ 2 := by
    rw [hval, hderiv]
    have hfour : ‖(4 : ℤ_[5])‖ = 1 := by
      exact (PadicInt.norm_intCast_eq_one_iff).2 ⟨-1, 1, by norm_num⟩
    change ‖(5 : ℤ_[5])‖ < ‖(4 : ℤ_[5])‖ ^ 2
    rw [hfour]
    simpa using
      (PadicInt.norm_intCast_lt_one_iff (p := 5) (z := (5 : ℤ))).2 (by norm_num)
  obtain ⟨z, hz, _, _, _⟩ :=
    hensels_lemma (p := 5)
      (F := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ)
      (a := (2 : ℤ_[5])) hnorm
  let u : ℚ_[5] := z
  have hu : u ^ 2 = -1 := by
    have hz' := congrArg (fun x : ℤ_[5] => (x : ℚ_[5])) hz
    have hz'' : u ^ 2 + 1 = 0 := by
      simpa [u,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
        Polynomial.aeval_def] using hz'
    exact eq_neg_of_add_eq_zero_left hz''
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0] at hu
    norm_num at hu
  refine ⟨u, -u, ?_, ?_⟩
  · intro h
    have hzero : (2 : ℚ_[5]) * u = 0 := by
      calc
        (2 : ℚ_[5]) * u = u + u := by rw [two_mul]
        _ = u + (-u) := congrArg (fun z => u + z) h
        _ = 0 := add_neg_cancel u
    rcases mul_eq_zero.mp hzero with h2 | hu'
    · norm_num at h2
    · exact hu0 hu'
  · have hcalc :
        (Polynomial.X : Polynomial (ℚ_[5])) ^ 2 + 1 =
          (Polynomial.X - Polynomial.C u) *
            (Polynomial.X + Polynomial.C u) := by
      have hcu : (Polynomial.C u : Polynomial (ℚ_[5])) ^ 2 =
          -(1 : Polynomial (ℚ_[5])) := by
        rw [← Polynomial.C_pow, hu]
        simp
      calc
        Polynomial.X ^ 2 + 1 =
            Polynomial.X ^ 2 - (Polynomial.C u) ^ 2 := by rw [hcu]; ring
        _ = (Polynomial.X - Polynomial.C u) *
            (Polynomial.X + Polynomial.C u) := by
              rw [sq_sub_sq]
              ring
    simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
      sub_eq_add_neg, map_neg] using hcalc

/-- The rational `5`-adic field is nonhenselian. -/
theorem chapter01_rationals_five_adic_are_not_henselian
    [Fact (Nat.Prime 5)] :
    ¬ HenselianLocalRing
      (chapter01FiveAdicValuation.valuationSubring) := by
  intro hH
  have h5le : chapter01FiveAdicValuation (5 : ℚ) ≤ 1 := by
    exact (Rat.padicValuation_le_one_iff).2 (by norm_num)
  have h5lt : chapter01FiveAdicValuation (5 : ℚ) < 1 := by
    have hself : chapter01FiveAdicValuation (5 : ℚ) = WithZero.exp (-1) :=
      Rat.padicValuation_self 5
    rw [hself]
    exact (WithZero.exp_lt_exp).2 (by norm_num)
  have hv2 : chapter01FiveAdicValuation (2 : ℚ) = 1 := by
    change Rat.padicValuation 5 (2 : ℚ) = 1
    simp [Rat.padicValuation, padicValRat]
  have hv4 : chapter01FiveAdicValuation (4 : ℚ) = 1 := by
    change Rat.padicValuation 5 (4 : ℚ) = 1
    simp [Rat.padicValuation, padicValRat]
  let A := chapter01FiveAdicValuation.valuationSubring
  have h5A : (5 : ℚ) ∈ A := by
    change (5 : ℚ) ∈ chapter01FiveAdicValuation.valuationSubring
    rw [Valuation.mem_valuationSubring_iff]
    exact h5le
  have h2A : (2 : ℚ) ∈ A := by
    change (2 : ℚ) ∈ chapter01FiveAdicValuation.valuationSubring
    rw [Valuation.mem_valuationSubring_iff]
    exact hv2.le
  have h2nonunit : (⟨5, h5A⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    change chapter01FiveAdicValuation.valuationSubring.valuation (5 : ℚ) < 1
    exact (Valuation.isEquiv_valuation_valuationSubring chapter01FiveAdicValuation).lt_one_iff_lt_one.mp h5lt
  let a2 : A := ⟨2, h2A⟩
  let a4 : A := ⟨4, hv4.le⟩
  have h4unit : IsUnit a4 := by
    rw [ValuationSubring.valuation_eq_one_iff]
    change chapter01FiveAdicValuation.valuationSubring.valuation (4 : ℚ) = 1
    exact (Valuation.isEquiv_valuation_valuationSubring chapter01FiveAdicValuation).eq_one_iff_eq_one.mp hv4
  let f : Polynomial A := Polynomial.X ^ 2 + 1
  have hf : f.Monic := by
    simpa [f] using
      (Polynomial.monic_X_pow_add_C (R := A) (1 : A) (n := 2) (by norm_num))
  have heval : f.eval a2 = (⟨5, h5A⟩ : A) := by
    apply Subtype.ext
    norm_num [f, a2]
  have hfa : f.eval a2 ∈ IsLocalRing.maximalIdeal A := by
    rw [heval]
    exact h2nonunit
  have hderiv : f.derivative.eval a2 = a4 := by
    ext
    norm_num [f, a2, a4]
    change (2 : ℚ) * 2 = 4
    norm_num
  have hderivunit : IsUnit (f.derivative.eval a2) := by
    rw [hderiv]
    exact h4unit
  obtain ⟨a, ha, _⟩ := hH.is_henselian f hf a2 hfa hderivunit
  have haA : (a : A) ^ 2 + 1 = 0 := by
    simpa [f, Polynomial.IsRoot] using ha
  have ha0 : (a : ℚ) ^ 2 + 1 = 0 := by
    exact_mod_cast haA
  nlinarith [sq_nonneg (a : ℚ)]

/-- `ℚ(i)` has two inequivalent extensions of the rational `5`-adic place. -/
theorem chapter01_gaussian_has_two_five_adic_extensions
    [Fact (Nat.Prime 5)] :
    chapter01TwoInequivalentValuationExtensions
      (L := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField)
      (Rat.padicValuation 5) := by
  unfold chapter01TwoInequivalentValuationExtensions
  have hderiv :
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).derivative.aeval
          (2 : ℤ_[5]) = (4 : ℤ_[5]) := by
    simp [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
      Polynomial.aeval_def]
  have hval :
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).aeval
          (2 : ℤ_[5]) = (5 : ℤ_[5]) := by
    norm_num [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
      Polynomial.aeval_def]
  have hnorm :
      ‖(LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).aeval
          (2 : ℤ_[5])‖ <
        ‖(LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).derivative.aeval
          (2 : ℤ_[5])‖ ^ 2 := by
    rw [hval, hderiv]
    have hfour : ‖(4 : ℤ_[5])‖ = 1 := by
      exact (PadicInt.norm_intCast_eq_one_iff).2 ⟨-1, 1, by norm_num⟩
    change ‖(5 : ℤ_[5])‖ < ‖(4 : ℤ_[5])‖ ^ 2
    rw [hfour]
    simpa using
      (PadicInt.norm_intCast_lt_one_iff (p := 5) (z := (5 : ℤ))).2 (by norm_num)
  obtain ⟨z, hz, hzclose, _, _⟩ :=
    hensels_lemma (p := 5)
      (F := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ)
      (a := (2 : ℤ_[5])) hnorm
  let u : ℚ_[5] := z
  have hu : u ^ 2 = -1 := by
    have hz' := congrArg (fun x : ℤ_[5] => (x : ℚ_[5])) hz
    have hz'' : u ^ 2 + 1 = 0 := by
      simpa [u,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
        Polynomial.aeval_def] using hz'
    exact eq_neg_of_add_eq_zero_left hz''
  have hroot :
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ).eval₂
          (Algebra.ofId ℚ ℚ_[5]) u = 0 := by
    simp [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
      hu]
  have hroot_neg :
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ).eval₂
          (Algebra.ofId ℚ ℚ_[5]) (-u) = 0 := by
    simp [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
      hu]
  let φ₁ :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField →ₐ[ℚ] ℚ_[5] :=
    AdjoinRoot.liftAlgHom
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ)
      (Algebra.ofId ℚ ℚ_[5]) u hroot
  let φ₂ :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField →ₐ[ℚ] ℚ_[5] :=
    AdjoinRoot.liftAlgHom
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ)
      (Algebra.ofId ℚ ℚ_[5]) (-u) hroot_neg
  have hφ₁root : φ₁ (AdjoinRoot.root
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ)) = u := by
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hφ₂root : φ₂ (AdjoinRoot.root
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ)) = -u := by
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have huclose : ‖u - (2 : ℚ_[5])‖ < 1 := by
    rw [hderiv] at hzclose
    have hfour : ‖(4 : ℤ_[5])‖ = 1 := by
      exact (PadicInt.norm_intCast_eq_one_iff).2 ⟨-1, 1, by norm_num⟩
    rw [hfour] at hzclose
    change ‖(z - 2 : ℤ_[5])‖ < 1 at hzclose
    rw [PadicInt.norm_def, PadicInt.coe_sub] at hzclose
    change ‖(z : ℚ_[5]) - 2‖ < 1
    exact hzclose
  have hvaldiff : (Padic.mulValuation (p := 5)) (u - 2) < 1 := by
    by_cases hx : u - 2 = 0
    · simp [Padic.mulValuation, hx]
    · have hnonneg : 0 ≤ (u - 2).valuation :=
        (Padic.norm_le_one_iff_val_nonneg (p := 5) (u - 2)).1 huclose.le
      have hpos : 0 < (u - 2).valuation := by
        by_contra hnot
        have hzero : (u - 2).valuation = 0 := by omega
        have hnormone : ‖u - 2‖ = 1 := by
          rw [Padic.norm_eq_zpow_neg_valuation hx, hzero]
          norm_num
        linarith
      simpa [Padic.mulValuation, hx, ← WithZero.exp_zero] using
        (show WithZero.exp (-(u - 2).valuation) < 1 from
          (WithZero.exp_lt_exp).2 (by linarith))
  have hfourval : (Padic.mulValuation (p := 5)) (4 : ℚ_[5]) = 1 := by
    norm_num [Padic.mulValuation, Padic.valuation_intCast, padicValInt]
  have huplus : (Padic.mulValuation (p := 5)) (u + 2) = 1 := by
    calc
      (Padic.mulValuation (p := 5)) (u + 2) =
          (Padic.mulValuation (p := 5)) (4 + (u - 2)) := by
            congr 1
            ring
      _ = (Padic.mulValuation (p := 5)) 4 := by
        apply (Padic.mulValuation (p := 5)).map_add_eq_of_lt_left
        rw [hfourval]
        exact hvaldiff
      _ = 1 := hfourval
  have hcomp₁ :
      ((Padic.mulValuation (p := 5)).comap φ₁.toRingHom).comap
          (algebraMap ℚ
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField) =
        Rat.padicValuation 5 := by
    calc
      _ = (Padic.mulValuation (p := 5)).comap
          (φ₁.toRingHom.comp
            (algebraMap ℚ
              LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField)) := rfl
      _ = (Padic.mulValuation (p := 5)).comap (Rat.castHom ℚ_[5]) := by
        congr 1
        ext x
        change φ₁ (algebraMap ℚ
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField x) =
          (x : ℚ_[5])
        exact φ₁.commutes x
      _ = Rat.padicValuation 5 :=
        Padic.comap_mulValuation_eq_padicValuation
  have hcomp₂ :
      ((Padic.mulValuation (p := 5)).comap φ₂.toRingHom).comap
          (algebraMap ℚ
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField) =
        Rat.padicValuation 5 := by
    calc
      _ = (Padic.mulValuation (p := 5)).comap
          (φ₂.toRingHom.comp
            (algebraMap ℚ
              LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField)) := rfl
      _ = (Padic.mulValuation (p := 5)).comap (Rat.castHom ℚ_[5]) := by
        congr 1
        ext x
        change φ₂ (algebraMap ℚ
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField x) =
          (x : ℚ_[5])
        exact φ₂.commutes x
      _ = Rat.padicValuation 5 :=
        Padic.comap_mulValuation_eq_padicValuation
  let W₁ :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousValuationExtension
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField
          (Rat.padicValuation 5) :=
    { valueGroup := ℤᵐ⁰
      valuation := (Padic.mulValuation (p := 5)).comap φ₁.toRingHom
      isExtension := Valuation.IsEquiv.of_eq hcomp₁.symm }
  let W₂ :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousValuationExtension
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField
          (Rat.padicValuation 5) :=
    { valueGroup := ℤᵐ⁰
      valuation := (Padic.mulValuation (p := 5)).comap φ₂.toRingHom
      isExtension := Valuation.IsEquiv.of_eq hcomp₂.symm }
  let α :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField :=
    AdjoinRoot.root
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ)
  let r :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField :=
    α + algebraMap ℚ
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField 2
  have hφ₁r : φ₁ r = u + 2 := by
    dsimp [r, α]
    rw [map_add, hφ₁root, φ₁.commutes]
    norm_num
  have hφ₂r : φ₂ r = -u + 2 := by
    dsimp [r, α]
    rw [map_add, hφ₂root, φ₂.commutes]
    norm_num
  have hW₁r : W₁.valuation r = 1 := by
    change (Padic.mulValuation (p := 5)) (φ₁ r) = 1
    rw [hφ₁r]
    exact huplus
  have hW₂r : W₂.valuation r < 1 := by
    change (Padic.mulValuation (p := 5)) (φ₂ r) < 1
    rw [hφ₂r, show -u + 2 = -(u - 2) by ring,
      (Padic.mulValuation (p := 5)).map_neg]
    exact hvaldiff
  refine ⟨W₁, W₂, ?_⟩
  intro hEq
  have hiff : W₁.valuation r < 1 ↔ W₂.valuation r < 1 :=
    hEq.lt_one_iff_lt_one
  have hlt : W₁.valuation r < 1 := hiff.mpr hW₂r
  rw [hW₁r] at hlt
  exact (lt_irrefl (1 : ℤᵐ⁰)) hlt

/-- Completion at `5` separates the Gaussian tensor product into two local factors. -/
theorem chapter01_gaussian_completed_tensor_product_at_five
    [Fact (Nat.Prime 5)] :
    Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField ⊗[ℚ] ℚ_[5] ≃+*
        ℚ_[5] × ℚ_[5]) := by
  simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11TensorSplit] using
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_gaussian_completed_tensor_at_five

/-- Each factor in the completed split tensor product is a local field. -/
theorem chapter01_gaussian_completed_factors_are_fields
    [Fact (Nat.Prime 5)] :
    Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField ⊗[ℚ] ℚ_[5] ≃+*
        ℚ_[5] × ℚ_[5]) ∧
      IsField ℚ_[5] := by
  exact ⟨chapter01_gaussian_completed_tensor_product_at_five, Field.toIsField _⟩

/-- The split completed tensor product is not itself a field. -/
theorem chapter01_gaussian_completed_tensor_product_not_field
    [Fact (Nat.Prime 5)] :
    ¬ IsField
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField ⊗[ℚ] ℚ_[5]) := by
  intro hfield
  obtain ⟨e⟩ := chapter01_gaussian_completed_tensor_product_at_five
  have hprod : IsField (ℚ_[5] × ℚ_[5]) :=
    MulEquiv.isField hfield e.symm.toMulEquiv
  have hleft : ((1, 0) : ℚ_[5] × ℚ_[5]) ≠ 0 := by
    intro h
    have := congrArg Prod.fst h
    simp at this
  obtain ⟨b, hb⟩ := hprod.mul_inv_cancel hleft
  have hsecond := congrArg Prod.snd hb
  simp at hsecond

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
