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

The degree equality is the explicit defectless hypothesis.  The existential
scaling law records the ramification data; theorems displaying a separately
named `e` also take `chapter11RamificationScaling` so that their `e` cannot be
an unrelated numerical decomposition.
The source formula is a statement about the finite normalization of a DVR:
the finiteness hypothesis and the correspondence of the displayed branches
with the primes/localizations of that normalization are therefore part of the
interface, rather than being left implicit in the valuation family.
-/
def chapter11DefectlessNormBranchData
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {ι : Type*} [Fintype ι]
    (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (f : ι → ℕ) : Prop :=
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
          (chapter11IntegralClosure v.valuationSubring L) L P (w i).toValuation)) ∧
    ∃ e : ι → ℕ,
      (∀ i, 0 < e i ∧
        ∀ z : K, w i (algebraMap K L z) = (e i : WithTop ℤ) * v z) ∧
        Module.finrank K L = ∑ i, e i * f i

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

The accompanying branch data include the explicit degree equality, excluding
defect and tying the ramification indices to the displayed normalized values.
-/
-- The canonical relative-ideal-norm API currently requires
-- `PerfectField (FractionRing R)` for the base Dedekind domain `R`; here the
-- normalized valuation ring has fraction field identified with `K`, so the
-- formal interface includes `[PerfectField K]`. Separability of `K → L` is
-- retained as the finite-extension hypothesis used by the field-norm step.
-- The finite-normalization and defectless-degree data above remain part of
-- the statement and are not replaced by the conclusion.
theorem chapter11_norm_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [PerfectField K] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (f : ι → ℕ)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w f)
    (x : L) (hx : x ≠ 0) :
    v (Algebra.norm K x) =
      ∑ i, (f i : WithTop ℤ) * w i x := by
  classical
  let A := v.valuationSubring
  let B := chapter11IntegralClosure A L
  let : Algebra A K := by
    dsimp [A]
    infer_instance
  let : IsFractionRing A K := inferInstance
  let : IsDomain A := inferInstance
  let : IsDiscreteValuationRing A := hdefectless.2.1
  let : IsDedekindDomain A :=
    ((IsDiscreteValuationRing.TFAE A (IsDiscreteValuationRing.not_isField A)).out 0 2).mp
      hdefectless.2.1
  let : IsIntegralClosure B A L := by
    change IsIntegralClosure (integralClosure A L) A L
    infer_instance
  let : IsDomain B := (IsIntegralClosure.algebraMap_injective B A L).isDomain
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  let : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  let : IsScalarTower A B L := inferInstance
  let : Module.Finite A B := hdefectless.2.2.1
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  let : Module.Free A B :=
    chapter11_finite_torsion_free_over_pid_is_free A B
  have corr_subring_of {P : Ideal B} [P.IsPrime]
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
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let : m.IsMaximal := by
    dsimp [m]
    exact IsLocalRing.maximalIdeal.isMaximal A
  let : m.IsPrime := (inferInstance : m.IsMaximal).isPrime
  have hm0 : m ≠ (⊥ : Ideal A) := by
    dsimp [m]
    exact IsDiscreteValuationRing.not_a_field A
  have hiP : ∀ i, ∃ P : Ideal B,
      chapter11Branch A B m P ∧
        Nonempty (Chapter11ValuationBranchCorrespondence
          B L P (w i).toValuation) := by
    simpa [m] using hdefectless.2.2.2.1
  have hPall : ∀ P : Ideal B,
      chapter11Branch A B m P →
        ∃ i, Nonempty (Chapter11ValuationBranchCorrespondence
          B L P (w i).toValuation) := by
    simpa [m] using hdefectless.2.2.2.2.1
  let P : ι → Ideal B := fun i => Classical.choose (hiP i)
  have hPbranch (i : ι) : chapter11Branch A B m (P i) := by
    exact (Classical.choose_spec (hiP i)).1
  let (i : ι) : (P i).IsPrime := (hPbranch i).1
  let (i : ι) : (P i).IsMaximal := (hPbranch i).2.1
  let (i : ι) : (P i).LiesOver m := (hPbranch i).2.2
  let c : ∀ i : ι,
      Chapter11ValuationBranchCorrespondence B L (P i) (w i).toValuation :=
    fun i => Classical.choice (Classical.choose_spec (hiP i)).2
  let g : ι → m.primesOver B := fun i =>
    ⟨P i, (hPbranch i).1, (hPbranch i).2.2⟩
  have hlocal_on_base (i : ι) (b : B) :
      (c i).localizationEquiv (algebraMap B (Localization.AtPrime (P i)) b) =
        (c i).embedding b := by
    let : (P i).IsPrime := (hPbranch i).1
    rw [show algebraMap B (Localization.AtPrime (P i)) b =
      Localization.mk b ⟨1, (P i).primeCompl.one_mem⟩ by rfl,
      (c i).localizationEquiv_on_B]
  have hval_eq_of_same_branch
      {Q : Ideal B} [Q.IsPrime]
      {v₁ v₂ : Valuation L (Multiplicative (WithTop ℤ)ᵒᵈ)}
      (c₁ : Chapter11ValuationBranchCorrespondence B L Q v₁)
      (c₂ : Chapter11ValuationBranchCorrespondence B L Q v₂) :
      v₁.IsEquiv v₂ := by
    have hφ :
        v₁.valuationSubring.subtype.comp c₁.localizationEquiv.toRingHom =
          v₂.valuationSubring.subtype.comp c₂.localizationEquiv.toRingHom := by
      apply IsLocalization.ringHom_ext Q.primeCompl
      apply RingHom.ext
      intro b
      change ((c₁.localizationEquiv
          (algebraMap B (Localization.AtPrime Q) b) : v₁.valuationSubring) : L) =
        ((c₂.localizationEquiv
          (algebraMap B (Localization.AtPrime Q) b) : v₂.valuationSubring) : L)
      rw [show algebraMap B (Localization.AtPrime Q) b =
          Localization.mk b ⟨1, Q.primeCompl.one_mem⟩ by rfl,
        c₁.localizationEquiv_on_B, c₂.localizationEquiv_on_B]
      exact (c₁.embedding_compatible b).trans (c₂.embedding_compatible b).symm
    apply (Valuation.isEquiv_iff_valuationSubring v₁ v₂).2
    apply ValuationSubring.ext
    intro z
    change z ∈ v₁.valuationSubring.toSubring ↔
      z ∈ v₂.valuationSubring.toSubring
    rw [chapter11_correspondence_valuationSubring B L Q c₁,
      chapter11_correspondence_valuationSubring B L Q c₂, hφ]
  have hg : Function.Injective g := by
    intro i j hij
    have hPij : P i = P j := congrArg Subtype.val hij
    have hval : (w i).IsEquiv (w j) := by
      let cj : Chapter11ValuationBranchCorrespondence B L (P i) (w j).toValuation :=
        cast (by rw [hPij]) (c j)
      exact hval_eq_of_same_branch (c i) cj
    exact hbranches.2.2.2.1 hval
  have hg_surj : Function.Surjective g := by
    intro q
    have hqbranch : chapter11Branch A B m q.1 := by
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    obtain ⟨i, hi⟩ := hPall q.1 hqbranch
    rcases hi with ⟨cq⟩
    have hemb : (c i).embedding = cq.embedding := by
      apply RingHom.ext
      intro b
      apply Subtype.ext
      exact (c i).embedding_compatible b |>.trans (cq.embedding_compatible b).symm
    have hPiq : P i = q.1 := by
      calc
        P i = (IsLocalRing.maximalIdeal (w i).toValuation.valuationSubring).comap
            (c i).embedding := (c i).center
        _ = (IsLocalRing.maximalIdeal (w i).toValuation.valuationSubring).comap
            cq.embedding := by rw [hemb]
        _ = q.1 := cq.center.symm
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hPiq
  have hinertia (i : ι) :
      (g i).1.inertiaDeg A =
        chapter11AdditiveResidueDegree v (w i) (hbranches.1 i) := by
    let : (P i).IsPrime := (hPbranch i).1
    let : (P i).IsMaximal := (hPbranch i).2.1
    let : (P i).LiesOver m := (hPbranch i).2.2
    change (P i).inertiaDeg A =
      chapter11AdditiveResidueDegree v (w i) (hbranches.1 i)
    rw [Ideal.inertiaDeg_eq_of_isMaximal m (P i)]
    let : Valuation.HasExtension v.toValuation (w i).toValuation :=
      ⟨hbranches.1 i⟩
    let : Algebra A (w i).toValuation.valuationSubring :=
      Valuation.HasExtension.instAlgebra_valuationSubring
        v.toValuation (w i).toValuation
    let S := Localization.AtPrime (P i)
    let eQ : B ⧸ P i ≃+* IsLocalRing.ResidueField S :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal (P i) S
    let eRes : IsLocalRing.ResidueField S ≃+*
        chapter11AdditiveResidueField (w i) :=
      IsLocalRing.ResidueField.mapEquiv (c i).localizationEquiv
    let eTarget : B ⧸ P i ≃+* chapter11AdditiveResidueField (w i) :=
      eQ.trans eRes
    let : m.IsTwoSided := by
      dsimp [m]
      infer_instance
    let eBase : A ⧸ m ≃+* chapter11AdditiveResidueField v := by
      change A ⧸ m ≃+* A ⧸ IsLocalRing.maximalIdeal A
      rfl
    change Module.finrank (A ⧸ m) (B ⧸ P i) =
      Module.finrank (chapter11AdditiveResidueField v)
        (chapter11AdditiveResidueField (w i))
    apply Algebra.finrank_eq_of_equiv_equiv eBase eTarget
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hemb :
        (c i).embedding (algebraMap A B a) =
          algebraMap A (w i).toValuation.valuationSubring a := by
      apply Subtype.ext
      calc
        ((c i).embedding (algebraMap A B a) : L) =
            algebraMap B L (algebraMap A B a) :=
          (c i).embedding_compatible _
        _ = algebraMap A L a := by
          rw [← IsScalarTower.algebraMap_apply A B L]
        _ = algebraMap K L (a : K) := by
          rw [IsScalarTower.algebraMap_apply A K L]
          rfl
        _ = (algebraMap A (w i).toValuation.valuationSubring a : L) := by
          symm
          exact Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
            v.toValuation (w i).toValuation a
    calc
      algebraMap (chapter11AdditiveResidueField v)
          (chapter11AdditiveResidueField (w i))
          (eBase (Ideal.Quotient.mk m a)) =
      algebraMap (chapter11AdditiveResidueField v)
            (chapter11AdditiveResidueField (w i))
            (IsLocalRing.residue A a) := by
        rfl
      _ = IsLocalRing.residue (w i).toValuation.valuationSubring
          (algebraMap A (w i).toValuation.valuationSubring a) := by
        exact Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
          v.toValuation (w i).toValuation a
      _ = IsLocalRing.residue (w i).toValuation.valuationSubring
          ((c i).embedding (algebraMap A B a)) := by rw [hemb]
      _ = eTarget (Ideal.Quotient.mk (P i) (algebraMap A B a)) := by
        change IsLocalRing.residue (w i).toValuation.valuationSubring
            ((c i).embedding (algebraMap A B a)) =
          IsLocalRing.residue (w i).toValuation.valuationSubring
            ((c i).localizationEquiv
              (algebraMap B (Localization.AtPrime (P i))
                (algebraMap A B a)))
        rw [hlocal_on_base]
  have hvalue (i : ι) (b : B) (hb : b ≠ 0) :
      w i (algebraMap B L b) =
        ((emultiplicity (g i).1 (Ideal.span ({b} : Set B))).toNat :
          WithTop ℤ) := by
    let : (P i).IsPrime := (hPbranch i).1
    let : (P i).IsMaximal := (hPbranch i).2.1
    let : (P i).LiesOver m := (hPbranch i).2.2
    have hP0 : P i ≠ (⊥ : Ideal B) :=
      Ideal.ne_bot_of_liesOver_of_ne_bot hm0 (P i)
    have hnorm : ∃ z : L, w i z = (1 : WithTop ℤ) := by
      rcases hbranches.2.1 i with ⟨e, he, hscale, hnorm⟩
      exact hnorm
    have hv := chapter11_branch_value_eq_local_length B L (P i) hP0
      (w i) (c i) hnorm b hb
    have he := chapter11_local_length_eq_emultiplicity B (P i) hP0 b hb
    rw [he] at hv
    simpa [g] using hv
  have hbase_subring :
      v.toValuation.valuationSubring.toSubring =
        Subring.map (algebraMap A K) (⊤ : Subring A) := by
    change A.toSubring = Subring.map (algebraMap A K) (⊤ : Subring A)
    apply Subring.ext
    intro z
    constructor
    · intro hz
      rw [Subring.mem_map]
      exact ⟨⟨z, hz⟩, Subring.mem_top _, rfl⟩
    · intro hz
      rcases Subring.mem_map.mp hz with ⟨a, -, ha⟩
      rw [← ha]
      exact a.property
  have hintegral (b : B) (hb : b ≠ 0) :
      v (Algebra.norm K (algebraMap B L b)) =
        ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
    have hbL : algebraMap B L b ≠ 0 :=
      (map_ne_zero_iff (algebraMap B L)
        (IsIntegralClosure.algebraMap_injective B A L)).2 hb
    have hI0 : Ideal.span ({b} : Set B) ≠ (⊥ : Ideal B) := by
      simp [hb]
    let F := normalizedFactors (Ideal.span ({b} : Set B))
    have hqem (q : m.primesOver B) :
        emultiplicity q.1 (Ideal.span ({b} : Set B)) =
          (F.count q.1 : ℕ∞) := by
      have hq0 : q.1 ≠ (⊥ : Ideal B) :=
        Ideal.ne_bot_of_mem_primesOver hm0 q.2
      have hqprime : Prime q.1 :=
        Ideal.prime_of_isPrime hq0 (Ideal.primesOver.isPrime m q)
      rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
        hqprime.irreducible hI0]
      simp [F, normalize_eq]
    have hqtop (q : m.primesOver B) :
        emultiplicity q.1 (Ideal.span ({b} : Set B)) ≠ (⊤ : ℕ∞) := by
      rw [hqem q]
      simp
    have hsum_top : ∀ q : m.primesOver B,
        (q.1.inertiaDeg A : ℕ∞) *
            emultiplicity q.1 (Ideal.span ({b} : Set B)) ≠ (⊤ : ℕ∞) := by
      intro q
      apply WithTop.mul_ne_top
      · exact ENat.natCast_ne_top _
      · exact hqtop q
    have htoNat :
        (∑ q : m.primesOver B,
          (q.1.inertiaDeg A : ℕ∞) *
            emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat =
          ∑ q : m.primesOver B,
            ((q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat := by
      simpa using (ENat.toNat_sum (s := (Finset.univ : Finset (m.primesOver B)))
        (fun q hq => hsum_top q))
    have hcast :
        ((∑ q : m.primesOver B,
          (q.1.inertiaDeg A : ℕ∞) *
            emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat : WithTop ℤ) =
          ∑ q : m.primesOver B,
            (q.1.inertiaDeg A : WithTop ℤ) *
              ((emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
                WithTop ℤ) := by
      rw [htoNat]
      simp only [ENat.toNat_mul, ENat.toNat_natCast]
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro q hq
      norm_cast
    have hbase_em (a : A) (ha : a ≠ 0) :
        v (algebraMap A K a) =
          ((emultiplicity m (Ideal.span ({a} : Set A))).toNat : WithTop ℤ) := by
      have hord := chapter11_normalized_dvr_ord A K v hbase_subring
        hdefectless.1 a ha
      have hordem : Ring.ord A a =
          emultiplicity m (Ideal.span ({a} : Set A)) := by
        rw [Ring.ord_eq_addVal]
        have hp : Prime (Classical.choose (IsDiscreteValuationRing.exists_prime A)) :=
          Classical.choose_spec (IsDiscreteValuationRing.exists_prime A)
        rw [IsDiscreteValuationRing.addVal, multiplicity_addValuation_apply]
        rw [← Ideal.emultiplicity_eq_emultiplicity_span]
        simp [m, hp.irreducible.maximalIdeal_eq]
      calc
        v (algebraMap A K a) = ((Ring.ord A a).toNat : WithTop ℤ) := hord
        _ = ((emultiplicity m (Ideal.span ({a} : Set A))).toNat : WithTop ℤ) := by
          rw [hordem]
    have hnormEm :
        emultiplicity m (Ideal.span ({Algebra.intNorm A B b} : Set A)) =
          ∑ q : m.primesOver B,
            (q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({b} : Set B)) := by
      exact chapter11_norm_integral_emultiplicity A B K m hm0 b
        hb
    have hintnorm : Algebra.intNorm A B b ≠ 0 := by
      intro hzero
      have hnzero : Algebra.norm K (algebraMap B L b) ≠ 0 :=
        Algebra.norm_ne_zero_iff.mpr hbL
      apply hnzero
      rw [← Algebra.algebraMap_intNorm (A := A) (B := B) (K := K) (L := L) b,
        hzero, map_zero]
    have hnorm_value :
        v (Algebra.norm K (algebraMap B L b)) =
          ((∑ q : m.primesOver B,
            (q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
            WithTop ℤ) := by
      calc
        v (Algebra.norm K (algebraMap B L b)) =
            v (algebraMap A K (Algebra.intNorm A B b)) := by
              rw [Algebra.algebraMap_intNorm (L := L) b]
        _ = ((emultiplicity m
            (Ideal.span ({Algebra.intNorm A B b} : Set A))).toNat :
              WithTop ℤ) := hbase_em (Algebra.intNorm A B b) hintnorm
        _ = ((∑ q : m.primesOver B,
            (q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
            WithTop ℤ) := by rw [hnormEm]
    have hsum_branch :
        (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b)) =
          ∑ q : m.primesOver B,
            (q.1.inertiaDeg A : WithTop ℤ) *
              ((emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
                WithTop ℤ) := by
      let e : ι ≃ m.primesOver B := Equiv.ofBijective g ⟨hg, hg_surj⟩
      calc
        (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b)) =
            ∑ i, (g i).1.inertiaDeg A *
              ((emultiplicity (g i).1 (Ideal.span ({b} : Set B))).toNat :
                WithTop ℤ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hfi : f i = (g i).1.inertiaDeg A := by
            exact (hf i).trans (hinertia i).symm
          rw [hfi, hvalue i b hb]
        _ = ∑ q : m.primesOver B,
            (q.1.inertiaDeg A : WithTop ℤ) *
              ((emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
                WithTop ℤ) := by
          exact Fintype.sum_equiv e _ _ (fun i => rfl)
    calc
      v (Algebra.norm K (algebraMap B L b)) =
          ((∑ q : m.primesOver B,
            (q.1.inertiaDeg A : ℕ∞) *
              emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
            WithTop ℤ) := hnorm_value
      _ = ∑ q : m.primesOver B,
          (q.1.inertiaDeg A : WithTop ℤ) *
            ((emultiplicity q.1 (Ideal.span ({b} : Set B))).toNat :
              WithTop ℤ) := hcast
      _ = ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := hsum_branch.symm
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B x
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply hx
    simp [ha]
  have haL : algebraMap B L a ≠ 0 :=
    (map_ne_zero_iff (algebraMap B L)
      (IsIntegralClosure.algebraMap_injective B A L)).2 ha0
  have hbL : algebraMap B L b ≠ 0 :=
    (map_ne_zero_iff (algebraMap B L)
      (IsIntegralClosure.algebraMap_injective B A L)).2 hb0
  have hnorm_div :
      v (Algebra.norm K (algebraMap B L a / algebraMap B L b)) =
        v (Algebra.norm K (algebraMap B L a)) -
          v (Algebra.norm K (algebraMap B L b)) := by
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
      AddValuation.map_mul, AddValuation.map_inv]
    simp only [sub_eq_add_neg]
  have hbranch_div :
      (∑ i, (f i : WithTop ℤ) *
          w i (algebraMap B L a / algebraMap B L b)) =
        (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L a)) -
          ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
    calc
      (∑ i, (f i : WithTop ℤ) *
          w i (algebraMap B L a / algebraMap B L b)) =
          ∑ i, (f i : WithTop ℤ) *
            (w i (algebraMap B L a) - w i (algebraMap B L b)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [AddValuation.map_div]
      _ = (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L a)) -
          ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
        let aa : ι → ℤ := fun i =>
          Classical.choose
            (WithTop.ne_top_iff_exists.mp ((w i).ne_top_iff.mpr haL))
        let bb : ι → ℤ := fun i =>
          Classical.choose
            (WithTop.ne_top_iff_exists.mp ((w i).ne_top_iff.mpr hbL))
        have haa (i : ι) :
            (aa i : WithTop ℤ) = w i (algebraMap B L a) := by
          dsimp [aa]
          exact Classical.choose_spec
            (WithTop.ne_top_iff_exists.mp ((w i).ne_top_iff.mpr haL))
        have hbb (i : ι) :
            (bb i : WithTop ℤ) = w i (algebraMap B L b) := by
          dsimp [bb]
          exact Classical.choose_spec
            (WithTop.ne_top_iff_exists.mp ((w i).ne_top_iff.mpr hbL))
        calc
          (∑ i, (f i : WithTop ℤ) *
              (w i (algebraMap B L a) - w i (algebraMap B L b))) =
              ∑ i, ((f i : WithTop ℤ) *
                ((aa i : WithTop ℤ) - (bb i : WithTop ℤ))) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [haa i, hbb i]
          _ = (∑ i, (f i : WithTop ℤ) * (aa i : WithTop ℤ)) -
              ∑ i, (f i : WithTop ℤ) * (bb i : WithTop ℤ) := by
            have hsum_coe (u : ι → ℤ) :
                (↑(∑ i, (f i : ℤ) * u i) : WithTop ℤ) =
                  ∑ i, (f i : WithTop ℤ) * (u i : WithTop ℤ) := by
              calc
                (↑(∑ i, (f i : ℤ) * u i) : WithTop ℤ) =
                    ∑ i, (↑((f i : ℤ) * u i) : WithTop ℤ) := by
                  rw [WithTop.coe_sum]
                _ = ∑ i, (f i : WithTop ℤ) * (u i : WithTop ℤ) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  change (↑((f i : ℤ) * u i) : WithTop ℤ) =
                    (↑(f i : ℤ) : WithTop ℤ) * (u i : WithTop ℤ)
                  norm_cast
            have hsubterm (i : ι) :
                (f i : WithTop ℤ) *
                    ((aa i : WithTop ℤ) - (bb i : WithTop ℤ)) =
                  (↑((f i : ℤ) * (aa i - bb i)) : WithTop ℤ) := by
              change (↑(f i : ℤ) : WithTop ℤ) *
                    ((aa i : WithTop ℤ) - (bb i : WithTop ℤ)) =
                  (↑((f i : ℤ) * (aa i - bb i)) : WithTop ℤ)
              norm_cast
            have hcast :
                (∑ i, (f i : WithTop ℤ) *
                    ((aa i : WithTop ℤ) - (bb i : WithTop ℤ))) =
                  (↑(∑ i, (f i : ℤ) * (aa i - bb i)) : WithTop ℤ) := by
              calc
                (∑ i, (f i : WithTop ℤ) *
                    ((aa i : WithTop ℤ) - (bb i : WithTop ℤ))) =
                    ∑ i, (↑((f i : ℤ) * (aa i - bb i)) : WithTop ℤ) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact hsubterm i
                _ = (↑(∑ i, (f i : ℤ) * (aa i - bb i)) : WithTop ℤ) := by
                  rw [WithTop.coe_sum]
            calc
              (∑ i, (f i : WithTop ℤ) *
                  ((aa i : WithTop ℤ) - (bb i : WithTop ℤ))) =
                  (↑(∑ i, (f i : ℤ) * (aa i - bb i)) : WithTop ℤ) := hcast
              _ = (↑((∑ i, (f i : ℤ) * aa i) -
                  ∑ i, (f i : ℤ) * bb i) : WithTop ℤ) := by
                congr 1
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro i hi
                rw [mul_sub]
              _ = (∑ i, (f i : WithTop ℤ) * (aa i : WithTop ℤ)) -
                  ∑ i, (f i : WithTop ℤ) * (bb i : WithTop ℤ) := by
                calc
                  (↑((∑ i, (f i : ℤ) * aa i) -
                    ∑ i, (f i : ℤ) * bb i) : WithTop ℤ) =
                      (↑(∑ i, (f i : ℤ) * aa i) : WithTop ℤ) -
                        (↑(∑ i, (f i : ℤ) * bb i) : WithTop ℤ) :=
                    rfl
                  _ = (∑ i, (f i : WithTop ℤ) * (aa i : WithTop ℤ)) -
                      ∑ i, (f i : WithTop ℤ) * (bb i : WithTop ℤ) := by
                    rw [hsum_coe, hsum_coe]
          _ = (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L a)) -
              ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
            simp_rw [haa, hbb]
  calc
    v (Algebra.norm K (algebraMap B L a / algebraMap B L b)) =
        v (Algebra.norm K (algebraMap B L a)) -
          v (Algebra.norm K (algebraMap B L b)) := hnorm_div
    _ = (∑ i, (f i : WithTop ℤ) * w i (algebraMap B L a)) -
          ∑ i, (f i : WithTop ℤ) * w i (algebraMap B L b) := by
      rw [hintegral a ha0, hintegral b hb0]
    _ = ∑ i, (f i : WithTop ℤ) *
          w i (algebraMap B L a / algebraMap B L b) := hbranch_div.symm


/-- For a base uniformizer, the branch values are e_i, so the norm sees Σ e_i f_i. -/
theorem chapter11_norm_of_uniformizer
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [PerfectField K] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e f : ι → ℕ) (π : K)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w f)
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
  (v : AddValuation K (WithTop ℤ)) (x y : L) :
    v (Algebra.norm K (x / y)) =
      v (Algebra.norm K x) - v (Algebra.norm K y) := by
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv,
    AddValuation.map_mul, AddValuation.map_inv]
  simp only [sub_eq_add_neg]

/-- The uniformizer computation agrees with the degree formula. -/
theorem chapter11_norm_uniformizer_consistency
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [PerfectField K] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] (v : AddValuation K (WithTop ℤ))
    (w : ι → AddValuation L (WithTop ℤ)) (e f : ι → ℕ) (π : K)
    (hbranches : chapter11CompleteNormalizedBranchFamily v w)
    (hf : ∀ i, f i = chapter11AdditiveResidueDegree v (w i) (hbranches.1 i))
    (hdefectless : chapter11DefectlessNormBranchData v w f)
    (hπ : ∀ i, w i (algebraMap K L π) = (e i : WithTop ℤ))
    (hdegree : Module.finrank K L = ∑ i, e i * f i) :
    v (Algebra.norm K (algebraMap K L π)) =
      (Module.finrank K L : WithTop ℤ) := by
  have hι : Nonempty ι := by
    by_contra hι
    let : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
    have hzero : Module.finrank K L = 0 := by simpa using hdegree
    exact (Nat.ne_of_gt Module.finrank_pos) hzero
  let i : ι := Classical.choice hι
  have hπ_ne : π ≠ 0 := by
    intro hzero
    have hi := hπ i
    rw [hzero, map_zero] at hi
    simp at hi
  calc
    v (Algebra.norm K (algebraMap K L π)) =
        ∑ i, (f i : WithTop ℤ) * (e i : WithTop ℤ) :=
      chapter11_norm_of_uniformizer K L v w e f π hbranches hf hdefectless hπ
        hπ_ne
    _ = ((∑ i, e i * f i : ℕ) : WithTop ℤ) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ = (Module.finrank K L : WithTop ℤ) := by
      rw [← hdegree]

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
