import LastLib.Book04AdelesAndIdeles.Chapter08.Section81

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct WithZero
open IsDedekindDomain

/-! ## 8.4 Lattices and finite ideles -/

def chapter08LatticeSet {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Set K :=
  {a | ∀ v : HeightOneSpectrum (Chapter08Integers K),
    (a : v.adicCompletion K) * chapter08FiniteIdeleComponent x v ∈
      v.adicCompletionIntegers K}

def chapter08Lattice {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Submodule (Chapter08Integers K) K where
  carrier := chapter08LatticeSet x
  zero_mem' := by
    intro v
    change (0 : v.adicCompletion K) * chapter08FiniteIdeleComponent x v ∈
      v.adicCompletionIntegers K
    simp
  add_mem' := by
    intro a b ha hb v
    change ((a + b : K) : v.adicCompletion K) *
      chapter08FiniteIdeleComponent x v ∈ v.adicCompletionIntegers K
    simpa only [IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_add, add_mul] using
      (v.adicCompletionIntegers K).add_mem
        (((a : K) : v.adicCompletion K) * chapter08FiniteIdeleComponent x v)
        (((b : K) : v.adicCompletion K) * chapter08FiniteIdeleComponent x v)
        (ha v) (hb v)
  smul_mem' := by
    intro r a ha v
    change ((r • a : K) : v.adicCompletion K) *
      chapter08FiniteIdeleComponent x v ∈ v.adicCompletionIntegers K
    simpa only [Algebra.smul_def,
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.coe_mul,
      mul_assoc] using
      (v.adicCompletionIntegers K).mul_mem
        (((r : K) : v.adicCompletion K))
        (((a : K) : v.adicCompletion K) * chapter08FiniteIdeleComponent x v)
        (IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem
          (R := Chapter08Integers K) (K := K) v r) (ha v)

theorem chapter08_lattice_mem_iff
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) (a : K) :
    a ∈ chapter08Lattice x ↔
      ∀ v : HeightOneSpectrum (Chapter08Integers K),
        (a : v.adicCompletion K) * chapter08FiniteIdeleComponent x v ∈
          v.adicCompletionIntegers K :=
  Iff.rfl

theorem chapter08_lattice_eq_inverse_ideal_submodule
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08Lattice x =
      (↑((chapter08FiniteIdeleIdealMap K x : Chapter08FractionalIdeal K)⁻¹) :
        Submodule (Chapter08Integers K) K) := by
  let I : Chapter08FractionalIdeal K :=
    (chapter08FiniteIdeleIdealMap K x : Chapter08FractionalIdeal K)
  have hI : I ≠ 0 := by
    exact Units.ne_zero (chapter08FiniteIdeleIdealMap K x)
  have hvalx (v : HeightOneSpectrum (Chapter08Integers K)) :
      Valued.v (chapter08FiniteIdeleComponent x v) =
        WithZero.exp (-chapter08FiniteIdeleOrder x v) := by
    have hxv : (Valued.v (chapter08FiniteIdeleComponent x v) : ℤᵐ⁰) ≠ 0 := by
      exact (Valuation.ne_zero_iff _).2
        (chapter08_finite_idele_component_ne_zero x v)
    unfold chapter08FiniteIdeleOrder chapter08LocalOrder
    rw [dif_neg hxv, WithZero.toAdd_unzero_eq_log hxv]
    simpa only [neg_neg] using (WithZero.exp_log hxv).symm
  ext a
  constructor
  · intro ha
    by_cases ha0 : a = 0
    · simp [ha0]
    change a ∈ I⁻¹
    rw [FractionalIdeal.mem_inv_iff hI]
    intro y hy
    by_cases hy0 : y = 0
    · simp [hy0]
    have hyspan :
        FractionalIdeal.spanSingleton (Chapter08Integers K)⁰ y ≤ I :=
      (FractionalIdeal.spanSingleton_le_iff_mem).2 hy
    have hyspan0 :
        FractionalIdeal.spanSingleton (Chapter08Integers K)⁰ y ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy0
    obtain ⟨r, hr⟩ :=
      IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
        K (a * y) (by
          intro v
          have halocal := (chapter08_lattice_mem_iff x a).1 ha v
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at halocal
          have hcountv :=
            chapter08_finite_idele_ideal_count x v
          have hcounty :
              FractionalIdeal.count K v I ≤
                LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent v y := by
              simpa [I,
              LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using
              (FractionalIdeal.count_mono K v hyspan0 hyspan :
                FractionalIdeal.count K v I ≤
                  FractionalIdeal.count K v
                    (FractionalIdeal.spanSingleton (Chapter08Integers K)⁰ y))
          have halocal' := halocal
          rw [Valuation.map_mul,
            IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
              v ha0, hvalx v] at halocal'
          rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at halocal'
          rw [hcountv] at hcounty
          rw [LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
              v (mul_ne_zero ha0 hy0), ← WithZero.exp_zero, WithZero.exp_le_exp]
          rw [LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_mul
            v ha0 hy0]
          linarith)
    exact ⟨r, trivial, hr⟩
  · intro ha
    by_cases ha0 : a = 0
    · simp [ha0]
    apply (chapter08_lattice_mem_iff x a).2
    intro v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    have hspan :
        FractionalIdeal.spanSingleton (Chapter08Integers K)⁰ a ≤ I⁻¹ :=
      (FractionalIdeal.spanSingleton_le_iff_mem).2 ha
    have hspan0 :
        FractionalIdeal.spanSingleton (Chapter08Integers K)⁰ a ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha0
    have hcount := FractionalIdeal.count_mono K v hspan0 hspan
    rw [FractionalIdeal.count_inv K v I] at hcount
    have hcount' :
        -FractionalIdeal.count K v I ≤
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent v a := by
      simpa [I,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent] using hcount
    have hcountv := chapter08_finite_idele_ideal_count x v
    rw [Valuation.map_mul, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter01.dedekindExponent_valuation
        v ha0, hvalx v]
    rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
    rw [hcountv] at hcount'
    linarith

noncomputable def chapter08LatticeFractionalIdeal
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) : Chapter08FractionalIdeal K :=
  ⟨chapter08Lattice x, by
    rw [chapter08_lattice_eq_inverse_ideal_submodule x]
    exact (chapter08FiniteIdeleIdealMap K x : Chapter08FractionalIdeal K)⁻¹ |>.isFractional⟩

theorem chapter08_lattice_fractionalIdeal_ne_zero
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08LatticeFractionalIdeal x ≠ 0 := by
  intro h
  have h_eq : chapter08LatticeFractionalIdeal x =
      (chapter08FiniteIdeleIdealMap K x : Chapter08FractionalIdeal K)⁻¹ := by
    apply FractionalIdeal.coeToSubmodule_injective
    change chapter08Lattice x = _
    exact chapter08_lattice_eq_inverse_ideal_submodule x
  rw [h_eq] at h
  exact (inv_ne_zero (Units.ne_zero (chapter08FiniteIdeleIdealMap K x))) h

theorem chapter08_lattice_eq_inverse_ideal
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08LatticeFractionalIdeal x =
      (chapter08FiniteIdeleIdealMap K x : Chapter08FractionalIdeal K)⁻¹ := by
  apply FractionalIdeal.coeToSubmodule_injective
  change chapter08Lattice x = _
  exact chapter08_lattice_eq_inverse_ideal_submodule x

theorem chapter08_lattice_unchanged_by_finite_integral_unit
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (u : chapter08FiniteIntegralUnits (K := K)) :
    chapter08LatticeSet (x * u.1) = chapter08LatticeSet x := by
  ext a
  constructor <;> intro ha v
  · have hu := (chapter08_finite_integral_unit_iff_local_valued_eq_one u.1).1 u.2 v
    have ha' := ha v
    change ((a : v.adicCompletion K) *
      (chapter08FiniteIdeleComponent x v *
        chapter08FiniteIdeleComponent u.1 v)) ∈ v.adicCompletionIntegers K at ha'
    change ((a : v.adicCompletion K) *
      chapter08FiniteIdeleComponent x v) ∈ v.adicCompletionIntegers K
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      at ha' ⊢
    rw [Valuation.map_mul, Valuation.map_mul, hu] at ha'
    simpa [mul_assoc] using ha'
  · have hu := (chapter08_finite_integral_unit_iff_local_valued_eq_one u.1).1 u.2 v
    have ha' := ha v
    change ((a : v.adicCompletion K) *
      chapter08FiniteIdeleComponent x v) ∈ v.adicCompletionIntegers K at ha'
    change ((a : v.adicCompletion K) *
      (chapter08FiniteIdeleComponent x v *
        chapter08FiniteIdeleComponent u.1 v)) ∈ v.adicCompletionIntegers K
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      at ha' ⊢
    rw [Valuation.map_mul, Valuation.map_mul, hu]
    simpa [mul_assoc] using ha'

theorem chapter08_lattice_unchanged_by_finite_integral_unit_submodule
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K)
    (u : chapter08FiniteIntegralUnits (K := K)) :
    chapter08Lattice (x * u.1) = chapter08Lattice x := by
  ext a
  exact Set.ext_iff.mp (chapter08_lattice_unchanged_by_finite_integral_unit x u) a

noncomputable def chapter08FiniteIdeleQuotientEquivIdealGroup
    (K : Type*) [Field K] [NumberField K] :
    (Chapter08FiniteIdeles K ⧸ chapter08FiniteIntegralUnits (K := K)) ≃*
      Chapter08IdealGroup K :=
  QuotientGroup.liftEquiv (chapter08FiniteIntegralUnits (K := K))
    (chapter08_finite_idele_ideal_surjective K)
    (chapter08_finite_idele_ideal_kernel (K := K)).symm

def chapter08RankOneFractionalLattice
    {K : Type*} [Field K] [NumberField K]
    (L : Submodule (Chapter08Integers K) K) : Prop :=
  ∃ I : Chapter08FractionalIdeal K, I ≠ 0 ∧ (I : Submodule (Chapter08Integers K) K) = L

theorem chapter08_lattice_is_rank_one_fractional_lattice
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08FiniteIdeles K) :
    chapter08RankOneFractionalLattice (chapter08Lattice x) := by
  refine ⟨chapter08LatticeFractionalIdeal x, chapter08_lattice_fractionalIdeal_ne_zero x, ?_⟩
  rfl

theorem chapter08_ideal_group_classifies_rank_one_lattices
    (K : Type*) [Field K] [NumberField K] :
    ∀ L : Submodule (Chapter08Integers K) K,
      chapter08RankOneFractionalLattice L →
        ∃ x : Chapter08FiniteIdeles K, chapter08Lattice x = L := by
  intro L hL
  obtain ⟨I, hI, hIL⟩ := hL
  let J : Chapter08IdealGroup K :=
    Units.mk0 (I⁻¹) (inv_ne_zero hI)
  obtain ⟨x, hx⟩ := chapter08_finite_idele_ideal_surjective K J
  refine ⟨x, ?_⟩
  rw [chapter08_lattice_eq_inverse_ideal_submodule x, hx]
  rw [← hIL]
  have hJI : (↑J : Chapter08FractionalIdeal K)⁻¹ = I := by
    simp [J]
  exact congrArg (fun M : Chapter08FractionalIdeal K =>
    (M : Submodule (Chapter08Integers K) K)) hJI

def chapter08IdealToLattice {K : Type*} [Field K] [NumberField K]
    (I : Chapter08IdealGroup K) : Chapter08FractionalIdeal K :=
  (I : Chapter08FractionalIdeal K)⁻¹

def chapter08HomotheticFractionalIdeal
    {K : Type*} [Field K] [NumberField K]
    (I J : Chapter08IdealGroup K) : Prop :=
  ∃ a : Kˣ, I = J * toPrincipalIdeal (Chapter08Integers K) K a

abbrev Chapter08HomotheticLatticeClassGroup
    (K : Type*) [Field K] [NumberField K] :=
  Chapter08IdealGroup K ⧸ (toPrincipalIdeal (Chapter08Integers K) K).range

noncomputable def chapter08HomotheticLatticeClassEquiv
    (K : Type*) [Field K] [NumberField K] :
    Chapter08OrdinaryClassGroup K ≃*
      Chapter08HomotheticLatticeClassGroup K :=
  ClassGroup.equiv K

theorem chapter08_homothetic_lattices_are_class_group
    (K : Type*) [Field K] [NumberField K] :
    Nonempty
      (Chapter08OrdinaryClassGroup K ≃*
        Chapter08HomotheticLatticeClassGroup K) := by
  exact ⟨chapter08HomotheticLatticeClassEquiv K⟩

end

end LastLib.Book04AdelesAndIdeles.Chapter08
