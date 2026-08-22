import LastLib.Book03RamificationTheory.Chapter07.Section02UnramifiednessAndTheDifferent
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.IsAdjoinRoot

namespace LastLib.Book03RamificationTheory.Chapter07

noncomputable section

open Polynomial
open scoped BigOperators Pointwise Polynomial nonZeroDivisors

/-! ## 7.3. The derivative formula -/

/-- The monogenic presentation used by the derivative formula. -/
def chapter07MonogenicPresentation
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (α : B) (f : A[X]) : Prop :=
  IsIntegral A α ∧ Algebra.adjoin A ({α} : Set B) = ⊤ ∧ f.Monic ∧
    aeval α f = 0 ∧
    f.map (algebraMap A K) = minpoly K (algebraMap B L α)

def chapter07DerivativeAt
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (f : A[X]) (α : B) : B :=
  aeval α f.derivative

theorem chapter07MonogenicPresentation_is_integral
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (α : B) (f : A[X])
    (h : chapter07MonogenicPresentation A B K L α f) :
    IsIntegral A α := by
  exact h.1

theorem chapter07MonogenicPresentation_generates
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (α : B) (f : A[X])
    (h : chapter07MonogenicPresentation A B K L α f) :
    Algebra.adjoin A ({α} : Set B) = ⊤ := by
  exact h.2.1

theorem chapter07_different_eq_derivative_ideal
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
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f) :
    chapter07DifferentIdeal A B =
      Ideal.span ({chapter07DerivativeAt A B f α} : Set B) := by
  let S : IntermediateField K L :=
    IntermediateField.adjoin K ({algebraMap B L α} : Set L)
  have hBmem : ∀ b : B, algebraMap B L b ∈ S := by
    intro b
    have hb : b ∈ Algebra.adjoin A ({α} : Set B) := by
      rw [hmono.2.1]
      trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hb
    · intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact IntermediateField.subset_adjoin K _ (by simp)
    · intro a
      rw [← IsScalarTower.algebraMap_apply A B L,
        IsScalarTower.algebraMap_apply A K L]
      exact S.algebraMap_mem _
    · intro x y hx hy hxm hym
      simpa only [map_add] using S.add_mem hxm hym
    · intro x y hx hy hxm hym
      simpa only [map_mul] using S.mul_mem hxm hym
  have hS : S = ⊤ := by
    apply top_unique
    intro z hz
    obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective B z
    exact S.div_mem (hBmem b) (hBmem c)
  have hgen : Algebra.adjoin K ({algebraMap B L α} : Set L) = ⊤ := by
    apply Algebra.adjoin_eq_top_of_intermediateField
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)
    exact hS
  have hf : f = minpoly A α := by
    apply Polynomial.map_injective (algebraMap A K)
      (FaithfulSMul.algebraMap_injective A K)
    calc
      f.map (algebraMap A K) = minpoly K (algebraMap B L α) := hmono.2.2.2.2
      _ = (minpoly A α).map (algebraMap A K) :=
        minpoly.isIntegrallyClosed_eq_field_fractions K L hmono.1
  have hcon := conductor_mul_differentIdeal A K L α hgen
  rw [conductor_eq_top_of_adjoin_eq_top hmono.2.1] at hcon
  have hcon' : differentIdeal A B =
      Ideal.span {aeval α (derivative (minpoly A α))} := by
    simpa using hcon
  simpa [chapter07DifferentIdeal, chapter07DerivativeAt, hf] using hcon'

/- Lagrange interpolation in a splitting field. -/
def chapter07InterpolationRootData
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (n : ℕ) (f : K[X]) (roots : Fin n → E) : Prop :=
  f.Monic ∧ f.natDegree = n ∧
    (∀ z : E, eval₂ (algebraMap K E) z f = 0 ↔
      ∃ i : Fin n, z = roots i) ∧
    (∀ i : Fin n,
      eval₂ (algebraMap K E) (roots i) f.derivative ≠ 0)

theorem chapter07_lagrange_interpolation_top_coefficient
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (n : ℕ) (f : K[X]) (roots : Fin n → E)
    (hroots : chapter07InterpolationRootData K E n f roots)
    (g : K[X]) (hg : g.natDegree < n) :
    algebraMap K E (g.coeff (n - 1)) =
      ∑ i : Fin n,
        eval₂ (algebraMap K E) (roots i) g /
          eval₂ (algebraMap K E) (roots i) f.derivative := by
  sorry

/- The same identity with the right-hand side recognized as a field trace. -/
theorem chapter07_interpolation_is_trace
    (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [Normal K Ω]
    (α : L) (f g : K[X])
    (_hf : f = minpoly K α) (_hg : g.natDegree < f.natDegree) :
    algebraMap K Ω
        (Algebra.trace K L
          (aeval α g / aeval α f.derivative)) =
      ∑ σ : L →ₐ[K] Ω,
        eval₂ (algebraMap K Ω) (σ α) g /
          eval₂ (algebraMap K Ω) (σ α) f.derivative := by
  rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04_trace_eq_sum_embeddings K L Ω
    (aeval α g / aeval α f.derivative)]
  simp [aeval_def]

/- The numerator polynomials q_i from the source. -/
def chapter07DualNumerator
    {A : Type*} [CommRing A] (f : A[X]) (n i : ℕ) : A[X] :=
  Finset.sum (Finset.Icc (i + 1) n) (fun j =>
    C (f.coeff j) * X ^ (j - i - 1))

def chapter07DualNumeratorValue
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (f : A[X]) (n i : ℕ) (α : B) : B :=
  aeval α (chapter07DualNumerator f n i)

theorem chapter07_dual_numerator_leading_shape
    {A : Type*} [CommRing A] (f : A[X]) (n i : ℕ)
    (hmonic : f.Monic) (hdegree : f.natDegree = n) (hi : i < n) :
    (chapter07DualNumerator f n i).coeff (n - i - 1) = 1 := by
  classical
  rw [chapter07DualNumerator, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single n]
  · rw [← hdegree]
    rw [if_pos rfl]
    exact hmonic.coeff_natDegree
  · intro j hj hji
    have hj' : i + 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hneq : n - i - 1 ≠ j - i - 1 := by
      intro heq
      omega
    simp [hneq]
  · simp [hi]

theorem chapter07_dual_numerators_form_basis
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L]
    (α : B) (f : A[X]) (n : ℕ)
    (hmono : chapter07MonogenicPresentation A B K L α f)
    (hdegree : f.natDegree = n) :
    LinearIndependent A
        (fun i : Fin n => chapter07DualNumeratorValue f n i α) ∧
      Submodule.span A
            (Set.range (fun i : Fin n =>
            chapter07DualNumeratorValue f n i α)) = ⊤ := by
  classical
  subst n
  let hmap : A[X] →ₐ[A] B := aeval α
  have hsurj : Function.Surjective hmap := by
    apply (AlgHom.range_eq_top hmap).mp
    rw [← Algebra.adjoin_singleton_eq_range_aeval]
    exact hmono.2.1
  have hker : RingHom.ker hmap = Ideal.span ({f} : Set A[X]) := by
    ext p
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · intro hp
      have hpL : Polynomial.aeval (algebraMap B L α)
          (p.map (algebraMap A K)) = 0 := by
        rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply L α p,
          hp, map_zero]
      have hdiv := minpoly.dvd K (algebraMap B L α) hpL
      rw [← hmono.2.2.2.2] at hdiv
      exact (Polynomial.map_dvd_map (algebraMap A K)
        (FaithfulSMul.algebraMap_injective A K) hmono.2.2.1).mp hdiv
    · rintro ⟨q, rfl⟩
      rw [map_mul]
      have hf0 : hmap f = 0 := by
        simpa [hmap] using hmono.2.2.2.1
      rw [hf0, zero_mul]
  let har : IsAdjoinRootMonic B f :=
    { map := hmap
      map_surjective := hsurj
      ker_map := hker
      monic := hmono.2.2.1 }
  have hqdegree (i : Fin f.natDegree) :
      (chapter07DualNumerator f f.natDegree i).degree <
        (f.natDegree - (i : ℕ)) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    rw [chapter07DualNumerator, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : j ≤ f.natDegree := (Finset.mem_Icc.mp hj).2
    have hneq : k ≠ j - (i : ℕ) - 1 := by
      omega
    simp [hneq]
  have hqmod (i : Fin f.natDegree) :
      (chapter07DualNumerator f f.natDegree i) %ₘ f =
        chapter07DualNumerator f f.natDegree i := by
    apply (Polynomial.modByMonic_eq_self_iff hmono.2.2.1).2
    rw [Polynomial.degree_eq_natDegree hmono.2.2.1.ne_zero]
    exact (hqdegree i).trans_le (by
      exact_mod_cast Nat.sub_le f.natDegree (i : ℕ))
  have hqrepr (i : Fin f.natDegree) (k : Fin f.natDegree) :
      har.basis.repr (chapter07DualNumeratorValue f f.natDegree i α) k =
        (chapter07DualNumerator f f.natDegree i).coeff (k : ℕ) := by
    change har.basis.repr (hmap (chapter07DualNumerator f f.natDegree i)) k = _
    rw [har.basis_repr, har.modByMonicHom_map, hqmod]
  have hcoord (g : Fin f.natDegree → A)
      (hrel : ∑ j, g j • chapter07DualNumeratorValue f f.natDegree j α = 0)
      (k : Fin f.natDegree) :
      ∑ j, g j * (chapter07DualNumerator f f.natDegree j).coeff (k : ℕ) = 0 := by
    have hk := congrArg (fun x : B => har.basis.repr x k) hrel
    simp only [map_sum, map_smul, map_zero, Finset.sum_apply', Finsupp.smul_apply,
      smul_eq_mul] at hk
    simpa only [hqrepr, Finsupp.zero_apply] using hk
  have hcoeff (g : Fin f.natDegree → A)
      (hrel : ∑ j, g j • chapter07DualNumeratorValue f f.natDegree j α = 0)
      (i : Fin f.natDegree)
      (hprev : ∀ j : Fin f.natDegree, (j : ℕ) < i → g j = 0) :
      g i = 0 := by
    let k : Fin f.natDegree := ⟨f.natDegree - (i : ℕ) - 1, by omega⟩
    have hsum :
        ∑ j, g j * (chapter07DualNumerator f f.natDegree j).coeff (k : ℕ) = g i := by
      rw [Finset.sum_eq_single i]
      · have hlead := chapter07_dual_numerator_leading_shape f f.natDegree
          (i : ℕ) hmono.2.2.1 rfl i.isLt
        have hqk : (chapter07DualNumerator f f.natDegree i).coeff (k : ℕ) = 1 := by
          simpa [k] using hlead
        simp [hqk]
      · intro j _ hji
        by_cases hlt : (j : ℕ) < i
        · rw [hprev j hlt, zero_mul]
        · have hgt : (i : ℕ) < j := by omega
          have hdeg :
              (chapter07DualNumerator f f.natDegree j).degree < (k : WithBot ℕ) := by
            apply (hqdegree j).trans_le
            rw [show (k : ℕ) = f.natDegree - (i : ℕ) - 1 by rfl]
            apply (WithBot.coe_le_coe).2
            rw [Nat.sub_sub]
            exact Nat.sub_le_sub_left (by omega) f.natDegree
          have hzero :
              (chapter07DualNumerator f f.natDegree j).coeff (k : ℕ) = 0 := by
            exact Polynomial.coeff_eq_zero_of_degree_lt hdeg
          rw [hzero, mul_zero]
      · simp
    exact (hsum.symm).trans (hcoord g hrel k)
  have hli : LinearIndependent A
      (fun i : Fin f.natDegree => chapter07DualNumeratorValue f f.natDegree i α) := by
    rw [Fintype.linearIndependent_iff]
    intro g hrel i
    have hprefix : ∀ r : ℕ, r ≤ f.natDegree →
        ∀ j : Fin f.natDegree, (j : ℕ) < r → g j = 0 := by
      intro r
      induction r with
      | zero =>
          intro _ j hj
          omega
      | succ r ih =>
          intro hr j hj
          by_cases hjeq : (j : ℕ) = r
          · have hrlt : r < f.natDegree := by omega
            let i' : Fin f.natDegree := ⟨r, hrlt⟩
            have hi' := hcoeff g hrel i' (by
              intro k hk
              apply ih
              · omega
              · exact hk)
            have hji : j = i' := Fin.ext (by simpa [i'] using hjeq)
            simpa [hji] using hi'
          · apply ih
            · omega
            · omega
    exact hprefix f.natDegree le_rfl i i.isLt
  refine ⟨hli, ?_⟩
  let S : Submodule A B :=
    Submodule.span A (Set.range (fun i : Fin f.natDegree =>
      chapter07DualNumeratorValue f f.natDegree i α))
  have hbasis_prefix : ∀ r : ℕ, r ≤ f.natDegree →
      ∀ j : Fin f.natDegree, (j : ℕ) < r → har.basis j ∈ S := by
    intro r
    induction r with
    | zero =>
        intro _ j hj
        omega
    | succ r ih =>
        intro hr j hj
        by_cases hlt : (j : ℕ) < r
        · exact ih (by omega) j hlt
        · have hjr : (j : ℕ) = r := by omega
          have hrlt : r < f.natDegree := by omega
          let i : Fin f.natDegree := ⟨f.natDegree - r - 1, by omega⟩
          have hi_lt : (i : ℕ) < f.natDegree := i.isLt
          have hqi_mem :
              chapter07DualNumeratorValue f f.natDegree i α ∈ S :=
            Submodule.subset_span ⟨i, rfl⟩
          have hqi_degree :
              (chapter07DualNumerator f f.natDegree i).degree <
                ((r + 1 : ℕ) : WithBot ℕ) := by
            have h := hqdegree i
            have heq : f.natDegree - (i : ℕ) = r + 1 := by
              dsimp [i]
              omega
            rw [heq] at h
            exact h
          have hsum :
              (∑ k ∈ (Finset.univ.erase j),
                (har.basis.repr
                    (chapter07DualNumeratorValue f f.natDegree i α)) k • har.basis k) +
                (har.basis.repr
                    (chapter07DualNumeratorValue f f.natDegree i α)) j • har.basis j =
              chapter07DualNumeratorValue f f.natDegree i α := by
            rw [Finset.sum_erase_add]
            · exact Module.Basis.sum_repr har.basis _
            · simp
          have hsum_mem :
              ∑ k ∈ (Finset.univ.erase j),
                (har.basis.repr
                    (chapter07DualNumeratorValue f f.natDegree i α)) k • har.basis k ∈ S := by
            apply Submodule.sum_mem
            intro k hk
            by_cases hkl : (k : ℕ) < r
            · exact S.smul_mem _ (ih (by omega) k hkl)
            · have hkj : (j : ℕ) < k := by
                have hne : k ≠ j := (Finset.mem_erase.mp hk).1
                omega
              have hzero :
                  (chapter07DualNumerator f f.natDegree i).coeff (k : ℕ) = 0 := by
                apply Polynomial.coeff_eq_zero_of_degree_lt
                have hkr : r < (k : ℕ) := by
                  rw [← hjr]
                  exact hkj
                have hrk : r + 1 ≤ (k : ℕ) := Nat.succ_le_of_lt hkr
                exact hqi_degree.trans_le ((WithBot.coe_le_coe).2 hrk)
              rw [hqrepr i k, hzero, zero_smul]
              exact S.zero_mem
          have hterm :
              (har.basis.repr
                  (chapter07DualNumeratorValue f f.natDegree i α)) j • har.basis j =
                har.basis j := by
            have hlead := chapter07_dual_numerator_leading_shape f f.natDegree
              (i : ℕ) hmono.2.2.1 rfl i.isLt
            have heq : f.natDegree - (i : ℕ) - 1 = r := by
              dsimp [i]
              omega
            have hqj :
                (chapter07DualNumerator f f.natDegree i).coeff (j : ℕ) = 1 := by
              rw [hjr, ← heq]
              exact hlead
            rw [hqrepr i j, hqj, one_smul]
          have hdiff :
              chapter07DualNumeratorValue f f.natDegree i α -
                  ∑ k ∈ (Finset.univ.erase j),
                    (har.basis.repr
                        (chapter07DualNumeratorValue f f.natDegree i α)) k • har.basis k =
                har.basis j := by
            calc
              chapter07DualNumeratorValue f f.natDegree i α -
                    ∑ k ∈ (Finset.univ.erase j),
                      (har.basis.repr
                          (chapter07DualNumeratorValue f f.natDegree i α)) k • har.basis k =
                  ((∑ k ∈ (Finset.univ.erase j),
                      (har.basis.repr
                          (chapter07DualNumeratorValue f f.natDegree i α)) k • har.basis k) +
                    (har.basis.repr
                        (chapter07DualNumeratorValue f f.natDegree i α)) j • har.basis j) -
                    ∑ k ∈ (Finset.univ.erase j),
                      (har.basis.repr
                          (chapter07DualNumeratorValue f f.natDegree i α)) k • har.basis k :=
                congrArg (fun x : B => x -
                  ∑ k ∈ (Finset.univ.erase j),
                    (har.basis.repr
                        (chapter07DualNumeratorValue f f.natDegree i α)) k • har.basis k) hsum.symm
              _ = (har.basis.repr
                    (chapter07DualNumeratorValue f f.natDegree i α)) j • har.basis j := by
                abel
              _ = har.basis j := hterm
          exact hdiff ▸ S.sub_mem hqi_mem hsum_mem
  have hbasis_mem : ∀ j : Fin f.natDegree, har.basis j ∈ S := by
    intro j
    exact hbasis_prefix f.natDegree le_rfl j j.isLt
  change S = ⊤
  apply top_unique
  intro b hb
  rw [← Module.Basis.sum_repr har.basis b]
  apply Submodule.sum_mem
  intro j hj
  exact S.smul_mem _ (hbasis_mem j)

theorem chapter07_trace_dual_basis_formula
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (α : B) (f : A[X]) (n : ℕ)
    (hmono : chapter07MonogenicPresentation A B K L α f)
    (hdegree : f.natDegree = n)
    (i j : Fin n) :
    Algebra.trace K L
        ((algebraMap B L (chapter07DualNumeratorValue f n i α) /
            algebraMap B L (chapter07DerivativeAt A B f α)) *
          (algebraMap B L α) ^ (j : ℕ)) =
      if i = j then 1 else 0 := by
  classical
  subst n
  let β : L := algebraMap B L α
  let S : IntermediateField K L := IntermediateField.adjoin K ({β} : Set L)
  have hBmem : ∀ b : B, algebraMap B L b ∈ S := by
    intro b
    have hb : b ∈ Algebra.adjoin A ({α} : Set B) := by
      rw [hmono.2.1]
      trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hb
    · intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact IntermediateField.subset_adjoin K _ (by simp [β])
    · intro a
      rw [← IsScalarTower.algebraMap_apply A B L,
        IsScalarTower.algebraMap_apply A K L]
      exact S.algebraMap_mem _
    · intro x y hx hy hxm hym
      simpa only [map_add] using S.add_mem hxm hym
    · intro x y hx hy hxm hym
      simpa only [map_mul] using S.mul_mem hxm hym
  have hgen : Algebra.adjoin K ({β} : Set L) = ⊤ := by
    apply Algebra.adjoin_eq_top_of_intermediateField
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)
    apply top_unique
    intro z hz
    obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective B z
    exact S.div_mem (hBmem b) (hBmem c)
  let pb : PowerBasis K L :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral β) hgen
  have hpbgen : pb.gen = β := by
    simp [pb]
  have hdim : pb.dim = f.natDegree := by
    calc
      pb.dim = (minpoly K β).natDegree := by rfl
      _ = (f.map (algebraMap A K)).natDegree := by rw [hmono.2.2.2.2]
      _ = f.natDegree := hmono.2.2.1.natDegree_map _
  have hqrec (i : ℕ) (hi : i < f.natDegree) :
      chapter07DualNumeratorValue f f.natDegree i α =
        algebraMap A B (f.coeff (i + 1)) +
          if i + 1 < f.natDegree then
            chapter07DualNumeratorValue f f.natDegree (i + 1) α * α else 0 := by
    rw [chapter07DualNumeratorValue, chapter07DualNumerator]
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega),
      Finset.sum_insert (by simp)]
    simp only [aeval_def, eval₂_finsetSum, eval₂_add, eval₂_C, eval₂_mul]
    have hi0 : i + 1 - i - 1 = 0 := by omega
    simp
    by_cases hnext : i + 1 < f.natDegree
    · rw [if_pos hnext]
      rw [chapter07DualNumeratorValue, chapter07DualNumerator]
      rw [aeval_def, eval₂_finsetSum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : i + 2 ≤ j := (Finset.mem_Icc.mp hj).1
      have heq : j - i - 1 = (j - (i + 1) - 1) + 1 := by omega
      rw [heq, pow_succ]
      simp [eval₂_mul, eval₂_C]; ring
    · rw [if_neg hnext]
      simp [Nat.not_lt.mp hnext]
  have hmin_deg : (minpoly K β).natDegree = f.natDegree := by
    calc
      (minpoly K β).natDegree = (f.map (algebraMap A K)).natDegree := by
        rw [hmono.2.2.2.2]
      _ = f.natDegree := hmono.2.2.1.natDegree_map _
  have hqcoeff : ∀ i : ℕ, i < f.natDegree →
      algebraMap B L (chapter07DualNumeratorValue f f.natDegree i α) =
        (minpolyDiv K β).coeff i := by
    let P : ℕ → Prop := fun i => i < f.natDegree →
      algebraMap B L (chapter07DualNumeratorValue f f.natDegree i α) =
        (minpolyDiv K β).coeff i
    have hP : ∀ i, P i := by
      apply Nat.strong_decreasing_induction (P := P)
      · refine ⟨f.natDegree - 1, ?_⟩
        intro m hm hmlt
        omega
      · intro i ih hi
        by_cases hnext : i + 1 < f.natDegree
        · have hnextq := ih (i + 1) (by omega) hnext
          have hrec := congrArg (algebraMap B L) (hqrec i hi)
          rw [if_pos hnext] at hrec
          simp only [map_add, map_mul] at hrec
          rw [coeff_minpolyDiv, ← hnextq]
          have hmincoeff :
              (minpoly K β).coeff (i + 1) = algebraMap A K (f.coeff (i + 1)) := by
            rw [← hmono.2.2.2.2, coeff_map]
          have htower :
              algebraMap B L (algebraMap A B (f.coeff (i + 1))) =
                algebraMap K L (algebraMap A K (f.coeff (i + 1))) := by
            rw [← IsScalarTower.algebraMap_apply A B L,
              IsScalarTower.algebraMap_apply A K L]
          rw [htower] at hrec
          rw [hmincoeff]
          simpa [β, IsScalarTower.algebraMap_apply] using hrec
        · have hlast : i + 1 = f.natDegree := by omega
          have hq_last :
              chapter07DualNumeratorValue f f.natDegree i α = 1 := by
            have hexp : f.natDegree - i - 1 = 0 := by omega
            rw [chapter07DualNumeratorValue, chapter07DualNumerator, hlast]
            simp [hmono.2.2.1.coeff_natDegree, hexp]
          have hdivdeg : (minpolyDiv K β).natDegree = f.natDegree - 1 := by
            rw [natDegree_minpolyDiv, hmin_deg]
          rw [hq_last]
          simp only [map_one]
          have hi_eq : i = f.natDegree - 1 := by omega
          rw [hi_eq, ← hdivdeg]
          exact (minpolyDiv_monic (Algebra.IsIntegral.isIntegral β)).coeff_natDegree.symm
    exact hP
  have hderiv :
      algebraMap B L (chapter07DerivativeAt A B f α) =
        aeval β (derivative (minpoly K β)) := by
    change algebraMap B L (eval₂ (algebraMap A B) α f.derivative) =
      eval₂ (algebraMap K L) β (derivative (minpoly K β))
    rw [hom_eval₂]
    rw [show (algebraMap B L).comp (algebraMap A B) = algebraMap A L by
      ext a
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A B L]]
    rw [show algebraMap B L α = β by rfl]
    have hderiv_map :
        (f.derivative).map (algebraMap A K) = derivative (minpoly K β) := by
      rw [← derivative_map, hmono.2.2.2.2]
    rw [← hderiv_map, eval₂_map]
    congr 1
    ext a
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A K L]
  have hdual (r : Fin f.natDegree) :
      pb.basis.traceDual (Fin.cast hdim.symm r) =
        algebraMap B L (chapter07DualNumeratorValue f f.natDegree r α) /
          algebraMap B L (chapter07DerivativeAt A B f α) := by
    rw [Module.Basis.traceDual_powerBasis_eq pb, hpbgen]
    change (minpolyDiv K β).coeff (r : ℕ) /
        aeval β (derivative (minpoly K β)) =
      algebraMap B L (chapter07DualNumeratorValue f f.natDegree r α) /
        algebraMap B L (chapter07DerivativeAt A B f α)
    rw [← hqcoeff (r : ℕ) r.isLt, ← hderiv]
  have htrace := pb.basis.trace_mul_traceDual
    (Fin.cast hdim.symm j) (Fin.cast hdim.symm i)
  rw [hdual i] at htrace
  simpa [PowerBasis.coe_basis, hpbgen, β, mul_comm, eq_comm, Fin.ext_iff] using htrace

def chapter07InversePrincipalSet
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (δ : B) : Set L :=
  {x | ∃ b : B, algebraMap B L b = x * algebraMap B L δ}

theorem chapter07_inverse_principal_mem_iff
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (δ : B) (x : L) :
    x ∈ chapter07InversePrincipalSet A B K L δ ↔
      ∃ b : B, algebraMap B L b = x * algebraMap B L δ := Iff.rfl

theorem chapter07_codifferent_eq_inverse_derivative_principal
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDedekindDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra K L]
    [Algebra B L] [Algebra A L] [IsScalarTower A K L]
    [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    (α : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L α f) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04TraceDual A B K L =
      chapter07InversePrincipalSet A B K L
        (chapter07DerivativeAt A B f α) := by
  classical
  let β : L := algebraMap B L α
  let T : Subalgebra A L := Algebra.adjoin A ({β} : Set L)
  let S : IntermediateField K L := IntermediateField.adjoin K ({β} : Set L)
  have hBmem : ∀ b : B, algebraMap B L b ∈ S := by
    intro b
    have hb : b ∈ Algebra.adjoin A ({α} : Set B) := by
      rw [hmono.2.1]
      trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hb
    · intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact IntermediateField.subset_adjoin K _ (by simp [β])
    · intro a
      rw [← IsScalarTower.algebraMap_apply A B L,
        IsScalarTower.algebraMap_apply A K L]
      exact S.algebraMap_mem _
    · intro x y hx hy hxm hym
      simpa only [map_add] using S.add_mem hxm hym
    · intro x y hx hy hxm hym
      simpa only [map_mul] using S.mul_mem hxm hym
  have hgen : Algebra.adjoin K ({β} : Set L) = ⊤ := by
    apply Algebra.adjoin_eq_top_of_intermediateField
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)
    apply top_unique
    intro z hz
    obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective B z
    exact S.div_mem (hBmem b) (hBmem c)
  have hmap_mem : ∀ b : B, algebraMap B L b ∈ T := by
    intro b
    have hb : b ∈ Algebra.adjoin A ({α} : Set B) := by
      rw [hmono.2.1]
      trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hb
    · intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact Algebra.subset_adjoin (by simp [β])
    · intro a
      rw [← IsScalarTower.algebraMap_apply A B L]
      exact T.algebraMap_mem _
    · intro x y hx hy hxm hym
      simpa only [map_add] using T.add_mem hxm hym
    · intro x y hx hy hxm hym
      simpa only [map_mul] using T.mul_mem hxm hym
  have hmap_surj : ∀ z : L, z ∈ T → ∃ b : B, algebraMap B L b = z := by
    intro z hz
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
    · intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨α, rfl⟩
    · intro a
      refine ⟨algebraMap A B a, ?_⟩
      rw [IsScalarTower.algebraMap_apply A B L]
    · intro x y hx hy hxm hym
      rcases hxm with ⟨bx, hbx⟩
      rcases hym with ⟨b_y, hby⟩
      refine ⟨bx + b_y, ?_⟩
      rw [map_add, hbx, hby]
    · intro x y hx hy hxm hym
      rcases hxm with ⟨bx, hbx⟩
      rcases hym with ⟨b_y, hby⟩
      refine ⟨bx * b_y, ?_⟩
      rw [map_mul, hbx, hby]
  have hdual_eq :
      (Submodule.traceDual A K (1 : Submodule B L) : Set L) =
        (Algebra.traceForm K L).dualSubmodule T.toSubmodule := by
    ext x
    constructor
    · intro hx
      change x ∈ (Algebra.traceForm K L).dualSubmodule T.toSubmodule
      rw [LinearMap.BilinForm.mem_dualSubmodule]
      intro z hz
      obtain ⟨b, hb⟩ := hmap_surj z hz
      obtain ⟨a, ha⟩ := (Submodule.mem_traceDual.mp hx)
        (algebraMap B L b) (by simp [Submodule.one_eq_range])
      apply Submodule.mem_one.mpr
      refine ⟨a, ?_⟩
      simpa [Algebra.traceForm_apply, ← hb] using ha
    · intro hx
      change x ∈ (Algebra.traceForm K L).dualSubmodule T.toSubmodule at hx
      rw [LinearMap.BilinForm.mem_dualSubmodule] at hx
      apply Submodule.mem_traceDual.mpr
      intro z hz
      obtain ⟨b, hb⟩ := (show ∃ b : B, algebraMap B L b = z by
        simpa [Submodule.one_eq_range] using hz)
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp <|
        hx
          (algebraMap B L b) (hmap_mem b)
      refine ⟨a, ?_⟩
      simpa [Algebra.traceForm_apply, ← hb] using ha
  have hβint : IsIntegral A β :=
    IsIntegral.map (IsScalarTower.toAlgHom A B L) hmono.1
  have hformula := traceForm_dualSubmodule_adjoin (A := A) (K := K) (L := L)
    (x := β) hgen hβint
  have hderiv :
      algebraMap B L (chapter07DerivativeAt A B f α) =
        aeval β (derivative (minpoly K β)) := by
    change algebraMap B L (eval₂ (algebraMap A B) α f.derivative) =
      eval₂ (algebraMap K L) β (derivative (minpoly K β))
    rw [hom_eval₂]
    rw [show (algebraMap B L).comp (algebraMap A B) = algebraMap A L by
      ext a
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A B L]]
    rw [show algebraMap B L α = β by rfl]
    have hderiv_map :
        (f.derivative).map (algebraMap A K) = derivative (minpoly K β) := by
      rw [← derivative_map, hmono.2.2.2.2]
    rw [← hderiv_map, eval₂_map]
    congr 1
    ext a
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A K L]
  have hδ : aeval β (derivative (minpoly K β)) ≠ 0 := by
    exact (Algebra.IsSeparable.isSeparable K β).aeval_derivative_ne_zero (minpoly.aeval K β)
  rw [← chapter07_codifferent_coe_eq_set A B K L, hdual_eq, hformula]
  ext x
  change x ∈
      ((aeval β (derivative (minpoly K β)))⁻¹ • T.toSubmodule : Submodule A L) ↔
    x ∈ chapter07InversePrincipalSet A B K L (chapter07DerivativeAt A B f α)
  rw [Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hδ)]
  simp only [inv_inv]
  constructor
  · intro hx
    have hxT : aeval β (derivative (minpoly K β)) * x ∈ T := by
      simpa only [Subalgebra.mem_toSubmodule] using hx
    obtain ⟨b, hb⟩ := hmap_surj (aeval β (derivative (minpoly K β)) * x) hxT
    refine ⟨b, ?_⟩
    simpa [hderiv, mul_comm] using hb
  · rintro ⟨b, hb⟩
    have hbx :
        aeval β (derivative (minpoly K β)) * x = algebraMap B L b := by
      rw [hb, hderiv]
      ring
    rw [hbx]
    simpa only [Subalgebra.mem_toSubmodule] using hmap_mem b

theorem chapter07_eisenstein_different_exponent_eq_derivative_valuation
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
    (vL : AddValuation L (WithTop ℤ)) (mB : Ideal B) (d : ℕ)
    (πL : B) (f : A[X])
    (hmono : chapter07MonogenicPresentation A B K L πL f)
    (hD : chapter07DifferentIdeal A B = mB ^ d)
    (_hmB : mB = IsLocalRing.maximalIdeal B)
    (_hπL : chapter07IsUniformizer vL (algebraMap B L πL))
    (hpower_valuation : ∀ z : B, z ≠ 0 →
      Ideal.span ({z} : Set B) = mB ^ d →
        vL (algebraMap B L z) = (d : WithTop ℤ)) :
    vL (algebraMap B L (chapter07DerivativeAt A B f πL)) =
      (d : WithTop ℤ) := by
  have hderiv :
      algebraMap B L (chapter07DerivativeAt A B f πL) =
        aeval (algebraMap B L πL)
          (derivative (minpoly K (algebraMap B L πL))) := by
    change algebraMap B L (eval₂ (algebraMap A B) πL f.derivative) =
      eval₂ (algebraMap K L) (algebraMap B L πL)
        (derivative (minpoly K (algebraMap B L πL)))
    rw [hom_eval₂]
    rw [show (algebraMap B L).comp (algebraMap A B) = algebraMap A L by
      ext a
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A B L]]
    have hderiv_map :
        f.derivative.map (algebraMap A K) =
          derivative (minpoly K (algebraMap B L πL)) := by
      rw [← derivative_map, hmono.2.2.2.2]
    rw [← hderiv_map, eval₂_map]
    congr 1
    ext a
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A K L]
  have hδ :
      aeval (algebraMap B L πL)
          (derivative (minpoly K (algebraMap B L πL))) ≠ 0 := by
    exact (Algebra.IsSeparable.isSeparable K (algebraMap B L πL)).aeval_derivative_ne_zero
      (minpoly.aeval K (algebraMap B L πL))
  have hne : chapter07DerivativeAt A B f πL ≠ 0 := by
    intro hz
    apply hδ
    rw [← hderiv, hz]
    simp
  have hspan :
      Ideal.span ({chapter07DerivativeAt A B f πL} : Set B) = mB ^ d := by
    rw [← chapter07_different_eq_derivative_ideal A B K L πL f hmono, hD]
  exact hpower_valuation (chapter07DerivativeAt A B f πL) hne hspan

end

end LastLib.Book03RamificationTheory.Chapter07
