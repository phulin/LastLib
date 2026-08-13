import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section06LocalizationAndResidues
import Mathlib.Data.ENat.BigOperators
import Mathlib.RingTheory.Ideal.Norm.RelNorm

universe u v

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter11

noncomputable section

open Ideal IsLocalRing
open Polynomial
open scoped BigOperators TensorProduct WithZero Polynomial nonZeroDivisors

/-! # Chapter 11: several places above one place

This file is a statement-only formalization of sections 11.1--11.9 of Book 1.
The declarations are intentionally local to this namespace because the chapters
are generated independently.
-/

/-! # Book 1, Chapter 11, Section 11.7: Norms and Ideals
-/

/-! ## 11.7. Norms and the sum over branches -/

/-- The field norm, defined by the determinant of multiplication. -/
def chapter11FieldNorm (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : L) : K :=
  Algebra.norm K x

/-- The field trace, defined by the trace of multiplication. -/
def chapter11FieldTrace (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (x : L) : K :=
  Algebra.trace K L x

/-- The residue field attached to an additive valuation. -/
abbrev chapter11AdditiveResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :=
  IsLocalRing.ResidueField v.toValuation.valuationSubring

/-- The actual residue degree of an additive valuation extension. -/
noncomputable def chapter11AdditiveResidueDegree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (h : v.IsEquiv (AddValuation.comap (algebraMap K L) w)) : ℕ := by
  letI : Valuation.HasExtension v.toValuation w.toValuation := ⟨h⟩
  exact Module.finrank (chapter11AdditiveResidueField v)
    (chapter11AdditiveResidueField w)

/-- A valuation with value group `ℤ` is normalized when it attains value one. -/
def chapter11AdditiveValuationNormalized
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) : Prop :=
  ∃ x : K, v x = (1 : WithTop ℤ)

/-- Finiteness of the residue-field extension attached to an equivalent branch. -/
def chapter11ResidueExtensionFinite
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AddValuation K (WithTop ℤ)) (w : AddValuation L (WithTop ℤ))
    (h : v.IsEquiv (AddValuation.comap (algebraMap K L) w)) : Prop := by
  letI : Valuation.HasExtension v.toValuation w.toValuation := ⟨h⟩
  exact FiniteDimensional (chapter11AdditiveResidueField v)
    (chapter11AdditiveResidueField w)

/-- A finite indexed family containing every normalized extension of `v`
exactly once, up to equivalence. -/
def chapter11CompleteNormalizedBranchFamily
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    {ι : Type*} [Fintype ι]
  (v : AddValuation K (WithTop ℤ))
  (w : ι → AddValuation L (WithTop ℤ)) : Prop :=
  (∀ i, v.IsEquiv (AddValuation.comap (algebraMap K L) (w i))) ∧
    (∀ i, ∃ e : ℕ, 0 < e ∧
      (∀ z : K, w i (algebraMap K L z) = (e : WithTop ℤ) * v z) ∧
      chapter11AdditiveValuationNormalized (w i)) ∧
    (∀ i, ∃ h : v.IsEquiv (AddValuation.comap (algebraMap K L) (w i)),
      chapter11ResidueExtensionFinite v (w i) h) ∧
    (∀ ⦃i j⦄, (w i).IsEquiv (w j) → i = j) ∧
    ∀ w' : AddValuation L (WithTop ℤ),
      v.IsEquiv (AddValuation.comap (algebraMap K L) w') →
        ∃ i, (w i).IsEquiv w'

/-- The displayed natural numbers are the ramification scalings of the
chosen normalized branch valuations. -/
def chapter11RamificationScaling
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {ι : Type*}
    (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e : ι → ℕ) : Prop :=
  ∀ i, 0 < e i ∧
    ∀ z : K, w i (algebraMap K L z) = (e i : WithTop ℤ) * v z

/-- Defectless normalized branch data for the norm formula.

The branch correspondences identify the displayed valuations with the
normalization branches.  The degree equality is not assumed as part of this
interface, since it is the fundamental equality supplied by finite
normalization.
The source formula is a statement about the finite normalization of a DVR:
the finiteness hypothesis and the correspondence of the displayed branches
with the primes/localizations of that normalization are therefore part of the
interface, rather than being left implicit in the valuation family.
-/
def chapter11DefectlessNormBranchData
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {ι : Type*} [Fintype ι]
    (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) : Prop :=
  chapter11AdditiveValuationNormalized v ∧
    IsDiscreteValuationRing v.valuationSubring ∧
    chapter11NormalizationFinite v.valuationSubring L ∧
    (∀ i, ∃ P : Ideal (chapter11IntegralClosure v.valuationSubring L),
      chapter11Branch v.valuationSubring (chapter11IntegralClosure v.valuationSubring L)
        (IsLocalRing.maximalIdeal v.valuationSubring) P ∧
        Nonempty (Chapter11ValuationBranchCorrespondence
          (chapter11IntegralClosure v.valuationSubring L) L P (w i).toValuation)) ∧
    (∀ P : Ideal (chapter11IntegralClosure v.valuationSubring L),
      chapter11Branch v.valuationSubring (chapter11IntegralClosure v.valuationSubring L)
        (IsLocalRing.maximalIdeal v.valuationSubring) P →
        ∃ i, Nonempty (Chapter11ValuationBranchCorrespondence
          (chapter11IntegralClosure v.valuationSubring L) L P (w i).toValuation))

/-! The next two lemmas make the normalization step in the norm proof explicit.
The first identifies an exactly normalized additive valuation with the DVR
order on nonzero elements.  The second transports that order through a branch
correspondence and its localization equivalence. -/

theorem chapter11_normalized_dvr_ord
    (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (v : AddValuation K (WithTop ℤ))
    (hsub : v.toValuation.valuationSubring.toSubring =
      Subring.map (algebraMap A K) (⊤ : Subring A))
    (hnorm : ∃ z : K, v z = (1 : WithTop ℤ))
    (a : A) (ha0 : a ≠ 0) :
    v (algebraMap A K a) = (Ring.ord A a).toNat := by
  classical
  have hmem (b : A) : algebraMap A K b ∈ v.toValuation.valuationSubring := by
    change algebraMap A K b ∈ v.toValuation.valuationSubring.toSubring
    rw [hsub, Subring.mem_map]
    exact ⟨b, Subring.mem_top _, rfl⟩
  have hzero_of_unit {y : K} (hy : y ≠ 0) (hy0 : 0 ≤ v y)
      (hyi : 0 ≤ v y⁻¹) : v y = 0 := by
    have hytop : v y ≠ ⊤ := (v.ne_top_iff).2 hy
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hytop
    rw [← hn] at hy0
    rw [AddValuation.map_inv, ← hn] at hyi
    have hyn : 0 ≤ n := by exact_mod_cast hy0
    have hyin : 0 ≤ -n := by exact_mod_cast hyi
    have hn0 : n = 0 := by linarith
    rw [hn0] at hn
    simpa using hn.symm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hunit (u : Aˣ) : v (algebraMap A K (u : A)) = 0 := by
    apply hzero_of_unit (by
      exact (map_ne_zero_iff (algebraMap A K)
        (FaithfulSMul.algebraMap_injective A K)).2 u.ne_zero)
    · exact hmem (u : A)
    · have huinv := hmem ((u⁻¹ : Aˣ) : A)
      change 0 ≤ v (algebraMap A K ((u⁻¹ : Aˣ) : A)) at huinv
      rw [show algebraMap A K ((u⁻¹ : Aˣ) : A) =
        (algebraMap A K (u : A))⁻¹ by simp] at huinv
      exact huinv
  have hpi_pos : 0 < v (algebraMap A K π) := by
    by_contra hnot
    have hpi0 : v (algebraMap A K π) = 0 :=
      le_antisymm (not_lt.mp hnot) (hmem π)
    have hinv : (algebraMap A K π)⁻¹ ∈ v.toValuation.valuationSubring := by
      change 0 ≤ v ((algebraMap A K π)⁻¹)
      rw [AddValuation.map_inv, hpi0]
      exact le_rfl
    change (algebraMap A K π)⁻¹ ∈ v.toValuation.valuationSubring.toSubring at hinv
    rw [hsub, Subring.mem_map] at hinv
    obtain ⟨b, -, hb⟩ := hinv
    have hprod : π * b = 1 := by
      apply (FaithfulSMul.algebraMap_injective A K)
      rw [map_mul, map_one, hb]
      exact mul_inv_cancel₀ (by
        exact (map_ne_zero_iff (algebraMap A K)
          (FaithfulSMul.algebraMap_injective A K)).2 hπ.ne_zero)
    exact hπ.not_isUnit (by
      rw [isUnit_iff_exists_inv]
      exact ⟨b, hprod⟩)
  obtain ⟨z, hz⟩ := hnorm
  have hzmem : z ∈ v.toValuation.valuationSubring := by
    change 0 ≤ v z
    rw [hz]
    exact zero_le_one
  change z ∈ v.toValuation.valuationSubring.toSubring at hzmem
  rw [hsub, Subring.mem_map] at hzmem
  obtain ⟨b, -, hb⟩ := hzmem
  have hb0 : b ≠ 0 := by
    intro hb0
    have hz0 : z = 0 := by simpa [hb0] using hb.symm
    have hzero : v 0 = 1 := hz0 ▸ hz
    simp at hzero
  obtain ⟨n, u, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  have hpi_top : v (algebraMap A K π) ≠ ⊤ :=
    (v.ne_top_iff).2 (by
      exact (map_ne_zero_iff (algebraMap A K)
        (FaithfulSMul.algebraMap_injective A K)).2 hπ.ne_zero)
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hpi_top
  have hmpos : 0 < m := by
    have hpi_pos' : (0 : WithTop ℤ) < (m : WithTop ℤ) := by simpa [hm] using hpi_pos
    exact_mod_cast hpi_pos'
  have hnm : n * m = 1 := by
    have hv := hz
    rw [← hb, ha] at hv
    rw [map_mul, AddValuation.map_mul, map_pow, AddValuation.map_pow] at hv
    rw [hunit, ← hm] at hv
    simp at hv
    exact_mod_cast hv
  have hn1z : (n : ℤ) = 1 :=
    Int.eq_one_of_mul_eq_one_right (by exact_mod_cast (Nat.zero_le n)) hnm
  have hm1 : m = 1 :=
    Int.eq_one_of_mul_eq_one_left (by linarith [hmpos]) hnm
  have hn1 : n = 1 := by exact_mod_cast hn1z
  have hpi1 : v (algebraMap A K π) = 1 := by
    rw [← hm, hm1]
    norm_num
  obtain ⟨n, u, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  calc
    v (algebraMap A K a) =
        v (algebraMap A K ((u : A) * π ^ n)) := by rw [ha]
    _ = (n : WithTop ℤ) := by
      simp only [map_mul, AddValuation.map_mul, map_pow, AddValuation.map_pow]
      rw [hunit, hpi1]
      simp
    _ = (Ring.ord A a).toNat := by
      have hord : Ring.ord A a = n := by
        rw [Ring.ord_eq_addVal]
        exact IsDiscreteValuationRing.addVal_def a u hπ n ha
      rw [hord]
      norm_num

theorem chapter11_correspondence_valuationSubring
    (B L : Type*) [CommRing B] [Field L] [Algebra B L]
    (P : Ideal B) [P.IsPrime]
    {vL : Valuation L (Multiplicative (WithTop ℤ)ᵒᵈ)}
    (c : Chapter11ValuationBranchCorrespondence B L P vL) :
    vL.valuationSubring.toSubring =
      Subring.map (vL.valuationSubring.subtype.comp c.localizationEquiv.toRingHom)
        (⊤ : Subring (Localization.AtPrime P)) := by
  apply Subring.ext
  intro z
  constructor
  · intro hz
    rcases c.localizationEquiv.surjective ⟨z, hz⟩ with ⟨s, hs⟩
    refine ⟨s, Subring.mem_top _, ?_⟩
    simpa using congrArg (fun t : vL.valuationSubring => (t : L)) hs
  · intro hz
    rcases hz with ⟨s, -, hs⟩
    change ((c.localizationEquiv s : vL.valuationSubring) : L) = z at hs
    change z ∈ vL.valuationSubring
    rw [← hs]
    exact (c.localizationEquiv s).property

theorem chapter11_local_length_eq_emultiplicity
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] (hP0 : P ≠ (⊥ : Ideal B))
    (b : B) (hb0 : b ≠ 0) :
    chapter11LocalLengthValue B P b =
      (emultiplicity P (Ideal.span ({b} : Set B))).toNat := by
  let S := Localization.AtPrime P
  let : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0 S
  have hbS : algebraMap B S b ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap B S)
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).2 hb0
  have hmax0 : IsLocalRing.maximalIdeal S ≠ (⊥ : Ideal S) := by
    rw [← (Localization.AtPrime.map_eq_maximalIdeal (I := P))]
    exact (Ideal.map_eq_bot_iff_of_injective
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).not.mpr hP0
  have hlen : (Module.length S
      (S ⧸ Ideal.span {algebraMap B S b})).toNat =
      (Ring.ord S (algebraMap B S b)).toNat := by
    rfl
  have hadd : Ring.ord S (algebraMap B S b) =
      emultiplicity (IsLocalRing.maximalIdeal S)
        (Ideal.span ({algebraMap B S b} : Set S)) := by
    rw [Ring.ord_eq_addVal]
    have hp : Prime (Classical.choose (IsDiscreteValuationRing.exists_prime S)) :=
      Classical.choose_spec (IsDiscreteValuationRing.exists_prime S)
    rw [IsDiscreteValuationRing.addVal, multiplicity_addValuation_apply]
    rw [← Ideal.emultiplicity_eq_emultiplicity_span]
    simp only [hp.irreducible.maximalIdeal_eq]
  have hram : Ideal.ramificationIdx' P (IsLocalRing.maximalIdeal S) = 1 := by
    apply Ideal.ramificationIdx'_eq_one_of_map_localization
      (p := P) (P := IsLocalRing.maximalIdeal S)
    · rw [← (Localization.AtPrime.map_eq_maximalIdeal (I := P))]
    · exact hmax0
    · exact (IsLocalRing.maximalIdeal S).primeCompl_le_nonZeroDivisors
    · rw [IsScalarTower.algebraMap_eq B S
          (Localization.AtPrime (IsLocalRing.maximalIdeal S)),
        ← Ideal.map_map, ← (Localization.AtPrime.map_eq_maximalIdeal
          (I := IsLocalRing.maximalIdeal S)), Localization.AtPrime.map_eq_maximalIdeal]
  have hmult := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
    (I := Ideal.span ({b} : Set B)) (h := by simp [hb0])
    (Ideal.prime_of_isPrime hP0 (inferInstance : P.IsPrime)).irreducible
    (Ideal.prime_of_isPrime hmax0 (IsLocalRing.maximalIdeal.isMaximal S).isPrime).irreducible
    hmax0
  rw [Ideal.map_span] at hmult
  have hmult' : emultiplicity (IsLocalRing.maximalIdeal S)
      (Ideal.span ({algebraMap B S b} : Set S)) =
      (emultiplicity P (Ideal.span ({b} : Set B))) := by
    simpa [hram] using hmult
  have hmultord : Ring.ord S (algebraMap B S b) =
      emultiplicity P (Ideal.span ({b} : Set B)) := hadd.trans hmult'
  change (Module.length S
      (S ⧸ Ideal.span {algebraMap B S b})).toNat = _
  rw [hlen]
  exact congrArg ENat.toNat hmultord

/-! The relative norm order is obtained by factoring a principal ideal and
grouping its normalized factors by the prime below them. -/
open UniqueFactorizationMonoid

theorem chapter11_norm_integral_emultiplicity
    (A B K : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B]
    [Field K] [Algebra A K] [IsFractionRing A K] [PerfectField K]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (m : Ideal A) [m.IsMaximal] (hm0 : m ≠ (⊥ : Ideal A))
    (y : B) (hy : y ≠ 0) :
    emultiplicity m
        (Ideal.span ({Algebra.intNorm A B y} : Set A)) =
      ∑ q : m.primesOver B,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 (Ideal.span ({y} : Set B)) := by
  classical
  let : PerfectField (FractionRing A) :=
    PerfectField.of_ringEquiv (FractionRing.algEquiv A K).symm.toRingEquiv
  let F := normalizedFactors (Ideal.span ({y} : Set B))
  have hI0 : Ideal.span ({y} : Set B) ≠ (⊥ : Ideal B) := by
    simp [hy]
  have hrel : Ideal.relNorm A (Ideal.span ({y} : Set B)) =
      Ideal.span ({Algebra.intNorm A B y} : Set A) := by
    exact Ideal.relNorm_singleton A y
  have hmprime : Prime m := Ideal.prime_of_isPrime hm0
    (inferInstance : m.IsMaximal).isPrime
  have hsum_map : ∀ (s : Multiset (Ideal B)),
        emultiplicity m (Multiset.map (Ideal.relNorm A) s).prod =
          (Multiset.map (fun Q => emultiplicity m (Ideal.relNorm A Q)) s).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      change emultiplicity m (1 : Ideal A) = 0
      apply emultiplicity_eq_zero.mpr
      intro hdiv
      apply (inferInstance : m.IsMaximal).ne_top
      exact top_unique (by simpa [Ideal.one_eq_top] using (Ideal.dvd_iff_le).mp hdiv)
    | @cons Q s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
      rw [emultiplicity_mul hmprime, ih]
  have hsum_rel :
      emultiplicity m (Ideal.relNorm A (Ideal.span ({y} : Set B))) =
        ∑ Q ∈ F.toFinset,
          F.count Q • emultiplicity m (Ideal.relNorm A Q) := by
    rw [← Ideal.prod_normalizedFactors_eq_self hI0, map_multiset_prod]
    rw [hsum_map F, Finset.sum_multiset_map_count]
  have hfactor : ∀ Q : Ideal B, Q ∈ F →
      emultiplicity m (Ideal.relNorm A Q) =
        if hQ : Q.LiesOver m then (Q.inertiaDeg A : ℕ∞) else 0 := by
    intro Q hQ
    have hQ0 : Q ≠ (⊥ : Ideal B) := ne_zero_of_mem_normalizedFactors hQ
    have hQprime : Q.IsPrime :=
      Ideal.isPrime_of_prime (prime_of_normalized_factor Q hQ)
    have hQmax : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ0 hQprime
    by_cases hQo : Q.LiesOver m
    · let : Q.LiesOver m := hQo
      simp only [dif_pos hQo]
      rw [Ideal.relNorm_eq_pow_of_isMaximal Q m]
      have hmp : Prime m := Ideal.prime_of_isPrime hm0
        (inferInstance : m.IsMaximal).isPrime
      exact emultiplicity_pow_self_of_prime hmp (Q.inertiaDeg A)
    · simp only [dif_neg hQo]
      have hundermax : (Ideal.comap (algebraMap A B) Q).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
      let : (Ideal.comap (algebraMap A B) Q).IsMaximal := hundermax
      let : Q.LiesOver (Ideal.comap (algebraMap A B) Q) :=
        Ideal.over_under (A := A) (P := Q)
      rw [Ideal.relNorm_eq_pow_of_isMaximal Q (Ideal.comap (algebraMap A B) Q)]
      apply emultiplicity_eq_zero.mpr
      intro hdiv
      have hne : (Ideal.comap (algebraMap A B) Q) ≠ m := by
        intro heq
        exact hQo ⟨heq.symm⟩
      have htop : m ⊔ (Ideal.comap (algebraMap A B) Q) = ⊤ :=
        (inferInstance : m.IsMaximal).coprime_of_ne
          (inferInstance : (Ideal.comap (algebraMap A B) Q).IsMaximal) hne.symm
      have htop_pow := Ideal.sup_pow_eq_top' (n := Q.inertiaDeg A) htop
      apply (inferInstance : m.IsMaximal).ne_top
      rw [← htop_pow]
      exact (sup_eq_left.mpr ((Ideal.dvd_iff_le).mp hdiv)).symm
  rw [hrel] at hsum_rel
  let T : Finset (Ideal B) := F.toFinset.filter (fun Q => Q.LiesOver m)
  have hsum_factor :
      emultiplicity m (Ideal.span ({Algebra.intNorm A B y} : Set A)) =
        ∑ Q ∈ T, F.count Q • (Q.inertiaDeg A : ℕ∞) := by
    calc
      emultiplicity m (Ideal.span ({Algebra.intNorm A B y} : Set A)) =
          ∑ Q ∈ F.toFinset,
            F.count Q • emultiplicity m (Ideal.relNorm A Q) := hsum_rel
      _ = ∑ Q ∈ F.toFinset,
            F.count Q • (if hQ : Q.LiesOver m then
              (Q.inertiaDeg A : ℕ∞) else 0) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [hfactor Q (Multiset.mem_toFinset.mp hQ)]
      _ = ∑ Q ∈ T, F.count Q • (Q.inertiaDeg A : ℕ∞) := by
        rw [show T = F.toFinset.filter (fun Q => Q.LiesOver m) by rfl,
          Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro Q hQ
        by_cases hQo : Q.LiesOver m <;> simp [hQo]
  have hcount_q (q : m.primesOver B) :
      emultiplicity q.1 (Ideal.span ({y} : Set B)) =
        (F.count q.1 : ℕ∞) := by
    have hq0 : q.1 ≠ (⊥ : Ideal B) :=
      Ideal.ne_bot_of_mem_primesOver hm0 q.2
    have hqprime : Prime q.1 :=
      Ideal.prime_of_isPrime hq0 (Ideal.primesOver.isPrime m q)
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      hqprime.irreducible hI0]
    simp [F, normalize_eq]
  let U : Finset (m.primesOver B) :=
    Finset.univ.filter (fun q => q.1 ∈ F.toFinset)
  have hsum_q_filter :
      (∑ q : m.primesOver B,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 (Ideal.span ({y} : Set B))) =
        ∑ q ∈ U,
          (q.1.inertiaDeg A : ℕ∞) *
            emultiplicity q.1 (Ideal.span ({y} : Set B)) := by
    rw [show U = Finset.univ.filter (fun q : m.primesOver B =>
      q.1 ∈ F.toFinset) by rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqF : q.1 ∈ F.toFinset
    · simp [hqF]
    · have hcount0 : F.count q.1 = 0 :=
        Multiset.count_eq_zero.mpr (by
          exact fun hmem => hqF (Multiset.mem_toFinset.mpr hmem))
      rw [hcount_q q, hcount0]
      simp
  have hsum_bij :
      (∑ q ∈ U,
        (q.1.inertiaDeg A : ℕ∞) *
          emultiplicity q.1 (Ideal.span ({y} : Set B))) =
        ∑ Q ∈ T, F.count Q • (Q.inertiaDeg A : ℕ∞) := by
    apply Finset.sum_bij (s := U) (t := T)
      (fun q _ => q.1)
    · intro q hq
      exact Finset.mem_filter.mpr ⟨
        (Finset.mem_filter.mp hq).2,
        Ideal.primesOver.liesOver m q⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      exact Subtype.ext heq
    · intro Q hQ
      have hQF : Q ∈ F :=
        Multiset.mem_toFinset.mp (Finset.mem_filter.mp hQ).1
      have hQo : Q.LiesOver m := Finset.mem_filter.mp hQ |>.2
      let : Q.IsPrime := Ideal.isPrime_of_prime
        (prime_of_normalized_factor Q hQF)
      let : Q.LiesOver m := hQo
      refine ⟨⟨Q, inferInstance, inferInstance⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Multiset.mem_toFinset.mpr hQF⟩
    · intro q hq
      rw [hcount_q q]
      simp [nsmul_eq_mul, mul_comm]
  exact hsum_factor.trans (hsum_q_filter.trans hsum_bij).symm

set_option maxHeartbeats 1000000 in
theorem chapter11_branch_value_eq_local_length
    (B L : Type*) [CommRing B] [IsDedekindDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal] (hP0 : P ≠ (⊥ : Ideal B))
    (vL : AddValuation L (WithTop ℤ))
    (c : Chapter11ValuationBranchCorrespondence B L P vL.toValuation)
    (hnorm : ∃ z : L, vL z = (1 : WithTop ℤ))
    (b : B) (hb0 : b ≠ 0) :
    vL (algebraMap B L b) =
      (chapter11LocalLengthValue B P b : WithTop ℤ) := by
  let S := Localization.AtPrime P
  let φ : S →+* L :=
    vL.toValuation.valuationSubring.subtype.comp c.localizationEquiv.toRingHom
  let : Algebra S L := φ.toAlgebra
  let : IsScalarTower B S L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro b
    change algebraMap B L b = φ (algebraMap B S b)
    dsimp [φ]
    rw [show algebraMap B S b =
      Localization.mk b ⟨1, P.primeCompl.one_mem⟩ by rfl,
      c.localizationEquiv_on_B b]
    exact (c.embedding_compatible b).symm
  let : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl S L
  let : IsDiscreteValuationRing S :=
    chapter11_branch_localization_is_dvr B P hP0
  have hφ : algebraMap S L = φ := RingHom.algebraMap_toAlgebra φ
  have hsub : vL.toValuation.valuationSubring.toSubring =
      Subring.map (algebraMap S L) (⊤ : Subring S) := by
    rw [hφ]
    exact chapter11_correspondence_valuationSubring B L P c
  have hbS : algebraMap B S b ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap B S)
      (IsLocalization.injective S P.primeCompl_le_nonZeroDivisors)).2 hb0
  have hv := chapter11_normalized_dvr_ord S L vL hsub hnorm
    (algebraMap B S b) hbS
  change vL (algebraMap B L b) =
      (Ring.ord S (algebraMap B S b)).toNat
  simpa only [IsScalarTower.algebraMap_apply B S L] using hv

set_option maxHeartbeats 5000000 in
/-- The norm valuation formula v(N(x)) = Σ f_i w_i(x).

The finite-normalization branch data identify the displayed valuations with all
normalization branches.  The degree equality is obtained from that finite
normalization rather than assumed in the norm interface.
-/
theorem chapter11_norm_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (f : ι → ℕ)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w)
    (x : L) (hx : x ≠ 0) :
    v (Algebra.norm K x) =
      ∑ i, (f i : WithTop ℤ) * w i x := by
  sorry


/-- If the branch values of an element are the specified `e_i`, the norm sees
`Σ e_i f_i`. -/
theorem chapter11_norm_from_branch_values
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e f : ι → ℕ) (π : K)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w)
    (hπ : ∀ i, w i (algebraMap K L π) = (e i : WithTop ℤ))
    (hπ_ne : π ≠ 0) :
    v (Algebra.norm K (algebraMap K L π)) =
      ∑ i, (f i : WithTop ℤ) * (e i : WithTop ℤ) := by
  have hnorm := chapter11_norm_valuation_formula K L v w f hbranches hf hdefectless
    (algebraMap K L π)
      ((map_ne_zero_iff (algebraMap K L)
        (FaithfulSMul.algebraMap_injective K L)).2 hπ_ne)
  simpa [hπ] using hnorm

/-- The same formula extends from integral elements to fractions by division. -/
theorem chapter11_norm_valuation_on_fractions
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (v : AddValuation K (WithTop ℤ)) (x y : L) (_hy : y ≠ 0) :
    v (Algebra.norm K (x / y)) =
      v (Algebra.norm K x) - v (Algebra.norm K y) := by
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
    AddValuation.map_mul, AddValuation.map_inv]
  simp only [sub_eq_add_neg]

/-- The uniformizer computation agrees with the degree formula. -/
theorem chapter11_norm_uniformizer_consistency
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e f : ι → ℕ) (π : K)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w)
    (hπbase : v π = (1 : WithTop ℤ))
    (hπ : ∀ i, w i (algebraMap K L π) = (e i : WithTop ℤ))
    (hdegree : Module.finrank K L = ∑ i, e i * f i) :
    v (Algebra.norm K (algebraMap K L π)) =
      (Module.finrank K L : WithTop ℤ) := by
  have hπ_ne : π ≠ 0 := by
    intro h
    subst π
    simp at hπbase
  have hnorm := chapter11_norm_valuation_formula K L v w f hbranches hf hdefectless
    (algebraMap K L π)
    ((map_ne_zero_iff (algebraMap K L)
      (FaithfulSMul.algebraMap_injective K L)).2 hπ_ne)
  rw [hnorm]
  simp_rw [hπ]
  have hpoint : ∀ i : ι,
      (f i : WithTop ℤ) * (e i : WithTop ℤ) =
        ((e i * f i : ℕ) : WithTop ℤ) := by
    intro i
    change ((f i : ℤ) : WithTop ℤ) * ((e i : ℤ) : WithTop ℤ) =
      ((e i * f i : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_mul]
    congr 1
    exact mul_comm (f i : ℤ) (e i : ℤ)
  calc
    ∑ i, (f i : WithTop ℤ) * (e i : WithTop ℤ) =
        ∑ i, ((e i * f i : ℕ) : WithTop ℤ) := by
          exact Finset.sum_congr rfl (fun i hi => hpoint i)
    _ = (∑ i, e i * f i : ℕ) := by
      symm
      exact Nat.cast_sum (R := WithTop ℤ) Finset.univ (fun i => e i * f i)
    _ = (Module.finrank K L : WithTop ℤ) := by
      exact congrArg (fun n : ℕ => (n : WithTop ℤ)) hdegree.symm

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
