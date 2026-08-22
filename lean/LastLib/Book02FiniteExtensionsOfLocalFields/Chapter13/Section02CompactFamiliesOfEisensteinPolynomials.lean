import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section05Conclusion
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.Section06CompactnessAndLocalCompactness
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13

noncomputable section

universe u

open Polynomial
open scoped BigOperators Pointwise Topology

/-! ## 13.2. Compact families of Eisenstein polynomials -/

/-- The coefficient parameter set for monic degree-`e` Eisenstein
polynomials.  The `Fin (e - 1)` coordinates are the nonconstant lower
coefficients, and the final coordinate is the constant coefficient. -/
def chapter13EisensteinCoefficientParameterSet
    {A : Type*} [CommRing A] (m : Ideal A) (e : ℕ) :
    Set ((Fin (e - 1) → A) × A) :=
  Set.pi Set.univ (fun _ : Fin (e - 1) => (m : Set A)) ×ˢ
    ((m : Set A) \ ((m ^ 2 : Ideal A) : Set A))

abbrev Chapter13EisensteinParameterSpace
    (A : Type*) [CommRing A] (m : Ideal A) (e : ℕ) :=
  chapter13EisensteinCoefficientParameterSet m e

/-- The polynomial reconstructed from its coefficient parameters. -/
noncomputable def chapter13EisensteinPolynomial
    {A : Type*} [CommRing A] (m : Ideal A) (e : ℕ)
    (a : Chapter13EisensteinParameterSpace A m e) : A[X] :=
  (X : A[X]) ^ e + C a.1.2 +
    ∑ i : Fin (e - 1), C (a.1.1 i) * X ^ ((i : ℕ) + 1)

theorem chapter13_eisenstein_parameter_polynomial_is_monic
    {A : Type*} [CommRing A] [Nontrivial A]
    (m : Ideal A)
    (e : ℕ) (he : 0 < e)
    (a : Chapter13EisensteinParameterSpace A m e) :
    (chapter13EisensteinPolynomial m e a).Monic := by
  rw [chapter13EisensteinPolynomial]
  apply (monic_X_pow_add_C a.1.2 (Nat.ne_of_gt he)).add_of_left
  rw [degree_X_pow_add_C he]
  refine (degree_sum_le _ _).trans_lt ?_
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe e)).2
  intro i _hi
  have hi' : (i : ℕ) + 1 < e := by omega
  have hi'' : ((i : ℕ) + 1 : WithBot ℕ) < (e : WithBot ℕ) :=
    WithBot.coe_lt_coe.mpr hi'
  exact (degree_C_mul_X_pow_le ((i : ℕ) + 1) (a.1.1 i)).trans_lt hi''

/-- The parameter conditions are exactly the canonical ideal-theoretic
Eisenstein condition. -/
theorem chapter13_eisenstein_parameter_polynomial_is_eisenstein
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (m : Ideal A) (hm : m = IsLocalRing.maximalIdeal A)
    (e : ℕ) (he : 0 < e)
    (a : Chapter13EisensteinParameterSpace A m e) :
    (chapter13EisensteinPolynomial m e a).IsEisensteinAt m := by
  have hsum :
      degree (∑ i : Fin (e - 1), C (a.1.1 i) * X ^ ((i : ℕ) + 1)) <
        (e : WithBot ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe e)).2
    intro i _hi
    have hi' : (i : ℕ) + 1 < e := by omega
    have hi'' : ((i : ℕ) + 1 : WithBot ℕ) < (e : WithBot ℕ) :=
      WithBot.coe_lt_coe.mpr hi'
    exact (degree_C_mul_X_pow_le ((i : ℕ) + 1) (a.1.1 i)).trans_lt hi''
  have hdegree :
      (chapter13EisensteinPolynomial m e a).natDegree = e := by
    rw [chapter13EisensteinPolynomial, natDegree_add_eq_left_of_degree_lt]
    · exact natDegree_X_pow_add_C
    · rw [degree_X_pow_add_C he]
      exact hsum
  have hcoeffmem (i : Fin (e - 1)) : a.1.1 i ∈ m := by
    exact a.2.1 i (Set.mem_univ i)
  refine ⟨?_, ?_, ?_⟩
  · rw [(chapter13_eisenstein_parameter_polynomial_is_monic m e he a).leadingCoeff,
      hm]
    exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one
  · intro n hn
    rw [hdegree] at hn
    by_cases hn0 : n = 0
    · subst n
      simpa [chapter13EisensteinPolynomial, (Nat.ne_of_gt he).symm] using a.2.2.1
    · let i : Fin (e - 1) := ⟨n - 1, by omega⟩
      have hni : n = (i : ℕ) + 1 := by
        dsimp [i]
        omega
      rw [chapter13EisensteinPolynomial, coeff_add, coeff_add, coeff_X_pow,
        if_neg (Nat.ne_of_lt hn), coeff_C, if_neg hn0, zero_add,
        finsetSum_coeff]
      rw [Finset.sum_eq_single i]
      · simp [hni, coeff_C_mul_X_pow, hcoeffmem i]
      · intro j _hj hji
        have hj' : n ≠ (j : ℕ) + 1 := by
          intro h
          apply hji
          apply Fin.ext
          omega
        simp [coeff_C_mul_X_pow, hj']
      · simp
  · simpa [chapter13EisensteinPolynomial, (Nat.ne_of_gt he).symm] using a.2.2.2

/-- Compatibility with Book 1's chosen-uniformizer spelling of Eisenstein. -/
theorem chapter13_eisenstein_parameter_book_facing_form
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (π : A) (e : ℕ) (he : 0 < e)
    (hπ : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A)
    (a : Chapter13EisensteinParameterSpace A
      (IsLocalRing.maximalIdeal A) e) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π
      (chapter13EisensteinPolynomial (IsLocalRing.maximalIdeal A) e a) := by
  have hsum :
      degree (∑ i : Fin (e - 1), C (a.1.1 i) * X ^ ((i : ℕ) + 1)) <
        (e : WithBot ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe e)).2
    intro i _hi
    have hi' : (i : ℕ) + 1 < e := by omega
    have hi'' : ((i : ℕ) + 1 : WithBot ℕ) < (e : WithBot ℕ) :=
      WithBot.coe_lt_coe.mpr hi'
    exact (degree_C_mul_X_pow_le ((i : ℕ) + 1) (a.1.1 i)).trans_lt hi''
  have hdegree :
      (chapter13EisensteinPolynomial (IsLocalRing.maximalIdeal A) e a).natDegree = e := by
    rw [chapter13EisensteinPolynomial, natDegree_add_eq_left_of_degree_lt]
    · exact natDegree_X_pow_add_C
    · rw [degree_X_pow_add_C he]
      exact hsum
  have hE := chapter13_eisenstein_parameter_polynomial_is_eisenstein
    (IsLocalRing.maximalIdeal A) rfl e he a
  refine ⟨(chapter13_eisenstein_parameter_polynomial_is_monic
      (IsLocalRing.maximalIdeal A) e he a), ?_, ?_, ?_, hπ⟩
  · rw [hdegree]
    exact he
  · intro i hi
    rw [hπ]
    exact hE.mem (by simpa [hdegree] using hi)
  · intro h
    change
      (chapter13EisensteinPolynomial (IsLocalRing.maximalIdeal A) e a).coeff 0 ∈
        Ideal.span ({π ^ 2} : Set A) at h
    rw [← Ideal.span_singleton_pow, hπ] at h
    exact hE.notMem h

/-- In the adic topology, the powers of the maximal ideal are compact and
open in a complete DVR with finite residue field. -/
theorem chapter13_complete_dvr_maximal_ideal_powers_compact_open
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal A) A) (n : ℕ) :
    @IsCompact A (IsLocalRing.maximalIdeal A).adicTopology
        ((IsLocalRing.maximalIdeal A ^ n : Ideal A) : Set A) ∧
      @IsOpen A (IsLocalRing.maximalIdeal A).adicTopology
        ((IsLocalRing.maximalIdeal A ^ n : Ideal A) : Set A) := by
  letI : @TopologicalSpace A := (IsLocalRing.maximalIdeal A).adicTopology
  letI : @CompactSpace A (IsLocalRing.maximalIdeal A).adicTopology :=
    @LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.chapter06_complete_dvr_integer_compact
      A _ _ _ _ hcomplete
  let U := (IsLocalRing.maximalIdeal A).openAddSubgroup n
  have hopen : @IsOpen A (IsLocalRing.maximalIdeal A).adicTopology
      ((IsLocalRing.maximalIdeal A ^ n : Ideal A) : Set A) := by
    change @IsOpen A (IsLocalRing.maximalIdeal A).adicTopology (↑U : Set A)
    exact U.isOpen
  have hclosed : @IsClosed A (IsLocalRing.maximalIdeal A).adicTopology
      ((IsLocalRing.maximalIdeal A ^ n : Ideal A) : Set A) := by
    change @IsClosed A (IsLocalRing.maximalIdeal A).adicTopology (↑U : Set A)
    exact U.isClosed
  exact ⟨hclosed.isCompact, hopen⟩

/-- The punctured first maximal-ideal layer is closed. -/
theorem chapter13_maximal_ideal_difference_square_is_closed
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] :
    @IsClosed A (IsLocalRing.maximalIdeal A).adicTopology
      (((IsLocalRing.maximalIdeal A : Ideal A) : Set A) \
        (((IsLocalRing.maximalIdeal A ^ 2 : Ideal A) : Set A))) := by
  let m := IsLocalRing.maximalIdeal A
  let _ : @TopologicalSpace A := m.adicTopology
  have hmclosed : @IsClosed A m.adicTopology (m : Set A) := by
    convert (m.openAddSubgroup 1).isClosed using 1
    ext x
    simp [Ideal.openAddSubgroup, pow_one]
    change x ∈ m ↔ x ∈ m
    rfl
  have hm2open : @IsOpen A m.adicTopology ((m ^ 2 : Ideal A) : Set A) := by
    let U := m.openAddSubgroup 2
    change @IsOpen A m.adicTopology (↑U : Set A)
    exact U.isOpen
  exact IsClosed.sdiff hmclosed hm2open

/-- The coefficient parameter space is compact once its valuation-ring
coordinates are equipped with the compact adic topology. -/
theorem chapter13_eisenstein_parameter_space_compact
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (m : Ideal A) (e : ℕ)
    [TopologicalSpace A] [CompactSpace A]
    (hm_compact : IsCompact (m : Set A))
    (hm_closed : IsClosed ((m : Set A) \
      ((m ^ 2 : Ideal A) : Set A))) :
    IsCompact (chapter13EisensteinCoefficientParameterSet m e) := by
  unfold chapter13EisensteinCoefficientParameterSet
  refine (isCompact_univ_pi (fun _ => hm_compact)).prod ?_
  exact hm_closed.isCompact

/-- The compactness theorem in the exact form used for the chapter's
valuation ring.  The topology is intentionally explicit so it does not
depend on a global choice of topology on a subring type. -/
theorem chapter13_complete_dvr_eisenstein_parameter_space_compact
    {E Γ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ]
    (vE : Valuation E Γ) [Valuation.IsRankOneDiscrete vE]
    [Finite (IsLocalRing.ResidueField vE.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vE.valuationSubring) vE.valuationSubring)
    (e : ℕ) :
    ∃ P : Set ((Fin (e - 1) → vE.valuationSubring) × vE.valuationSubring),
      P = chapter13EisensteinCoefficientParameterSet
        (IsLocalRing.maximalIdeal vE.valuationSubring) e ∧
      @IsCompact ((Fin (e - 1) → vE.valuationSubring) ×
        vE.valuationSubring)
        (letI : TopologicalSpace vE.valuationSubring :=
          (IsLocalRing.maximalIdeal vE.valuationSubring).adicTopology
         inferInstance)
        P := by
  let O := vE.valuationSubring
  let m := IsLocalRing.maximalIdeal O
  let _ : @TopologicalSpace O := m.adicTopology
  let _ : @CompactSpace O m.adicTopology :=
    @LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.chapter06_complete_dvr_integer_compact
      O _ _ _ _ hcomplete
  have hm_compact : IsCompact (m : Set O) := by
    simpa [m, pow_one] using
      (chapter13_complete_dvr_maximal_ideal_powers_compact_open
        (A := O) hcomplete 1).1
  have hm_closed : IsClosed ((m : Set O) \ ((m ^ 2 : Ideal O) : Set O)) := by
    exact chapter13_maximal_ideal_difference_square_is_closed (A := O)
  refine ⟨chapter13EisensteinCoefficientParameterSet m e, rfl, ?_⟩
  exact chapter13_eisenstein_parameter_space_compact m e hm_compact hm_closed

/-- A compact locally constant family has only finitely many values. -/
theorem chapter13_eisenstein_family_has_finitely_many_extension_classes
    {P C : Type*} [TopologicalSpace P]
    (φ : P → C) (hcompact : IsCompact (Set.univ : Set P))
    (hlocally_constant : chapter13LocallyConstant φ) :
    Set.Finite (Set.range φ) :=
  chapter13_compact_locally_constant_range_finite φ hcompact hlocally_constant

noncomputable def chapter13RootFieldClassMap
    (E Ω : Type u) (P : Type*) [Field E] [Field Ω] [Algebra E Ω]
    (root : P → Ω)
    (hfinite : ∀ a : P,
      FiniteDimensional E (chapter13RootField E Ω (root a))) :
    P → Chapter13FiniteExtensionClass E :=
  fun a =>
    letI : FiniteDimensional E (chapter13RootField E Ω (root a)) := hfinite a
    chapter13RootFieldExtensionClass E Ω (root a)

theorem chapter13_eisenstein_root_field_classes_are_finite
    {E Ω : Type u} {P : Type*} [Field E] [Field Ω] [Algebra E Ω]
    [TopologicalSpace P]
    (root : P → Ω)
    (hfinite : ∀ a : P,
      FiniteDimensional E (chapter13RootField E Ω (root a)))
    (hcompact : IsCompact (Set.univ : Set P))
    (hlocally_constant : chapter13LocallyConstant
      (chapter13RootFieldClassMap E Ω P root hfinite)) :
    Set.Finite (Set.range (chapter13RootFieldClassMap E Ω P root hfinite)) :=
  chapter13_compact_locally_constant_range_finite
    (chapter13RootFieldClassMap E Ω P root hfinite) hcompact hlocally_constant

/-- The Chapter 12 local-constancy theorem in the form needed here.  The
source applies it to monic Eisenstein polynomials, which are irreducible;
keeping irreducibility and the fixed degree explicit prevents the false
claim that an arbitrary separable polynomial has one generated field for
all of its roots. -/
theorem chapter13_separable_root_field_has_krasner_neighborhood
    {E Ω : Type*} [NontriviallyNormedField E] [CompleteSpace E]
    [IsUltrametricDist E] [NormedField Ω] [NormedAlgebra E Ω]
    [FiniteDimensional E Ω]
    (g : E[X]) (α : Ω) (d : ℕ)
    (hmonic : g.Monic) (hirreducible : Irreducible g)
    (hseparable : g.Separable) (hdegree : g.natDegree = d)
    (hroot : aeval α g = 0)
    (hsplits : (g.map (algebraMap E Ω)).Splits) :
    ∃ U : Set (Fin d → E), IsOpen U ∧
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.chapter12CoefficientVector d g ∈ U ∧
      ∀ b : Fin d → E, b ∈ U →
        let h := LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.chapter12MonicPolynomial d b
        Irreducible h ∧
          (h.map (algebraMap E Ω)).Splits ∧
          ∀ β : Ω, aeval β h = 0 →
            Nonempty (chapter13RootField E Ω α ≃ₐ[E]
              chapter13RootField E Ω β) := by
  obtain ⟨U, hUopen, hcenter, hstable⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.chapter12_local_constancy_of_generated_field
      g α d hmonic hirreducible hseparable hdegree hroot hsplits
  refine ⟨U, hUopen, hcenter, ?_⟩
  intro b hb
  dsimp
  exact hstable b hb

/-- Coefficientwise congruence modulo a fixed power of the maximal ideal. -/
def chapter13CoefficientCongruent
    {A : Type*} [CommRing A] (m : Ideal A) (n : ℕ)
    (f g : A[X]) : Prop :=
  ∀ i : ℕ, f.coeff i - g.coeff i ∈ m ^ n

theorem chapter13_coefficient_congruent_mono
    {A : Type*} [CommRing A] (m : Ideal A)
    {n N : ℕ} (hnN : n ≤ N) (f g : A[X]) :
    chapter13CoefficientCongruent m N f g →
      chapter13CoefficientCongruent m n f g := by
  intro h i
  exact Ideal.pow_le_pow_right hnN (h i)

/-- A finite Krasner subcover can be refined by one common coefficient
congruence modulus when the congruence sets form the chosen neighborhood
basis. -/
theorem chapter13_finite_subcover_has_common_congruence_modulus
    {A C : Type*} [CommRing A] [TopologicalSpace A]
    (m : Ideal A) (e : ℕ)
    (φ : Chapter13EisensteinParameterSpace A m e → C)
    (hcompact : IsCompact
      (chapter13EisensteinCoefficientParameterSet m e))
    (hopen : ∀ a n, IsOpen {b : Chapter13EisensteinParameterSpace A m e |
      chapter13CoefficientCongruent m n
        (chapter13EisensteinPolynomial m e a)
        (chapter13EisensteinPolynomial m e b)})
    (hlocal_congruence :
      ∀ a, ∃ n : ℕ, ∀ b,
        chapter13CoefficientCongruent m n
          (chapter13EisensteinPolynomial m e a)
          (chapter13EisensteinPolynomial m e b) →
        φ b = φ a) :
    ∃ n : ℕ, ∀ a b,
      chapter13CoefficientCongruent m n
        (chapter13EisensteinPolynomial m e a)
        (chapter13EisensteinPolynomial m e b) →
      φ a = φ b := by
  classical
  have hP : CompactSpace (Chapter13EisensteinParameterSpace A m e) :=
    isCompact_iff_compactSpace.mp hcompact
  have huniv : IsCompact
      (Set.univ : Set (Chapter13EisensteinParameterSpace A m e)) :=
    hP.isCompact_univ
  choose n hn using hlocal_congruence
  obtain ⟨s, hs⟩ :=
    huniv.elim_finite_subcover
      (fun a : Chapter13EisensteinParameterSpace A m e =>
        {b | chapter13CoefficientCongruent m (n a)
          (chapter13EisensteinPolynomial m e a)
          (chapter13EisensteinPolynomial m e b)})
      (fun a => hopen a (n a))
      (by
        intro a _
        refine Set.mem_iUnion.2 ⟨a, ?_⟩
        simp [chapter13CoefficientCongruent])
  have hcover (a : Chapter13EisensteinParameterSpace A m e) :
      ∃ i ∈ s,
        chapter13CoefficientCongruent m (n i)
          (chapter13EisensteinPolynomial m e i)
          (chapter13EisensteinPolynomial m e a) := by
    have ha := hs (Set.mem_univ a)
    simp only [Set.mem_iUnion] at ha
    rcases ha with ⟨i, ⟨hi, hai⟩⟩
    exact ⟨i, hi, hai⟩
  refine ⟨s.sup n, ?_⟩
  intro a b hab
  obtain ⟨i, hi, hai⟩ := hcover a
  have hNi : n i ≤ s.sup n := Finset.le_sup hi
  have hab' := chapter13_coefficient_congruent_mono m hNi
    (chapter13EisensteinPolynomial m e a)
    (chapter13EisensteinPolynomial m e b) hab
  have hib : chapter13CoefficientCongruent m (n i)
      (chapter13EisensteinPolynomial m e i)
      (chapter13EisensteinPolynomial m e b) := by
    intro j
    have hsum := (m ^ n i).add_mem (hai j) (hab' j)
    simpa [sub_add_sub_cancel] using hsum
  exact (hn i a hai).trans (hn i b hib).symm

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13
