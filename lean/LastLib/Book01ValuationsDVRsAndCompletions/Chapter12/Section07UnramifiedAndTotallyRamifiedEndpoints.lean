import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

noncomputable section

open Function Ideal IsLocalRing Polynomial
open Filter Topology
open scoped BigOperators TensorProduct WithZero Polynomial

universe u

/-! # Chapter 12: Completion and finite extensions

This file is a statement-generation pass for §§12.1--12.8 of Book 1.  The
declarations deliberately record the interfaces and relationships used in the
chapter; proofs are postponed.
-/

/-! # Book 1, Chapter 12, Section 12.7: Unramified and Totally Ramified Endpoints
-/

/-! ## 12.7. Unramified and totally ramified endpoints -/

/-- The foundational unramified condition: `e = 1` and separable residue extension. -/
def foundationalUnramified (e : ℕ) (residueSeparable : Prop) : Prop :=
  e = 1 ∧ residueSeparable

/-- The foundational totally ramified condition: `f = 1`. -/
def foundationalTotallyRamified (f : ℕ) : Prop :=
  f = 1

/-- The two endpoint degree allocations in a defectless complete extension. -/
theorem endpoint_degree_allocations
    (degree e f : ℕ) (hdegree : degree = e * f)
    (hunramified : e = 1) (htotallyRamified : f = 1) :
    degree = f ∧ degree = e := by
  constructor
  · simpa [hunramified] using hdegree
  · simpa [htotallyRamified] using hdegree

/-- A monic irreducible separable residue polynomial prescribes the unramified
    branch invariants after a monic lift and a chosen root. -/
theorem separable_residue_polynomial_lift_is_unramified
    {A K L Γ : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (w : Valuation L Γ)
    [vK.HasExtension w] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete w]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (fbar : (A ⧸ IsLocalRing.maximalIdeal A)[X]) (f : A[X]) (Pi : L)
    (hmonic : fbar.Monic ∧ f.Monic)
    (hirreducible : Irreducible fbar)
    (hseparable : fbar.Separable)
    (hlift : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) = fbar)
    (hroot : aeval Pi (f.map (algebraMap A K)) = 0)
    (hgenerates : Algebra.adjoin K ({Pi} : Set L) = ⊤)
    (hbaseIntegers : vK.Integers A)
    (hbaseValuationRing :
      (vK.valuationSubring : Set K) = Set.range (algebraMap A K))
    (hupperIntegralClosure :
      (w.valuationSubring : Set L) = (integralClosure A L : Set L)) :
    Irreducible (f.map (algebraMap A K)) ∧
      Module.finrank K L = fbar.natDegree ∧
      chapterRamificationIndex vK.valuationSubring w.valuationSubring
          (IsLocalRing.maximalIdeal w.valuationSubring) = 1 ∧
      chapterResidueDegree vK.valuationSubring w.valuationSubring
          (IsLocalRing.maximalIdeal w.valuationSubring) = fbar.natDegree := by
  sorry

/-- Eisenstein polynomials in the form used by the chapter. -/
def IsEisensteinAt
    {A : Type*} [CommRing A] [IsLocalRing A]
    (π : A) (f : A[X]) : Prop :=
  f.Monic ∧ 0 < f.natDegree ∧
    (∀ i < f.natDegree, f.coeff i ∈ Ideal.span {π}) ∧
    f.constantCoeff ∉ Ideal.span {π ^ 2} ∧
    Ideal.span {π} = IsLocalRing.maximalIdeal A

/-- The power-basis expansion associated to a root of an Eisenstein polynomial. -/
def eisensteinExpansion
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (Pi : L) (a : Fin n → K) : L :=
  ∑ i, algebraMap K L (a i) * Pi ^ (i : ℕ)

/-- Coefficients are integral exactly when they lie in the base localization ring. -/
def coefficientsAreIntegral
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    {n : ℕ} (a : Fin n → K) : Prop :=
  ∀ i, IsLocalization.IsInteger A (a i)

/-- The power-basis expansion is unique for an Eisenstein root. -/
theorem eisenstein_power_basis_expansion_unique
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    (hf : IsEisensteinAt π f) (hroot : aeval Pi f = 0)
    (hdegree : f.natDegree = n)
    (hgenerates : Algebra.adjoin K ({Pi} : Set L) = ⊤) :
    ∀ x : L, ∃! a : Fin n → K, x = eisensteinExpansion Pi a := by
  have hspan : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A := hf.2.2.2.2
  let _ : (Ideal.span ({π} : Set A)).IsPrime := by
    rw [hspan]
    infer_instance
  have hE : f.IsEisensteinAt (Ideal.span ({π} : Set A)) := by
    apply hf.1.isEisensteinAt_of_mem_of_notMem
    · rw [hspan]
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    · intro i hi
      exact hf.2.2.1 i hi
    · simpa [Ideal.span_singleton_pow] using hf.2.2.2.1
  have hprimitive : f.IsPrimitive := hf.1.isPrimitive
  have hirrA : Irreducible f :=
    hE.irreducible inferInstance hprimitive hf.2.1
  have hirrK : Irreducible (f.map (algebraMap A K)) :=
    (hprimitive.irreducible_iff_irreducible_map_fraction_map).mp hirrA
  have hrootK : aeval Pi (f.map (algebraMap A K)) = 0 := by
    simpa only [aeval_map_algebraMap, IsScalarTower.algebraMap_eq A K L] using hroot
  have hmapMonic : (f.map (algebraMap A K)).Monic := hf.1.map (algebraMap A K)
  have hmin : f.map (algebraMap A K) = minpoly K Pi :=
    minpoly.eq_of_irreducible_of_monic hirrK hrootK hmapMonic
  have hPiIntegral : IsIntegral K Pi := ⟨f.map (algebraMap A K), hmapMonic, hrootK⟩
  let B : PowerBasis K L := PowerBasis.ofAdjoinEqTop hPiIntegral hgenerates
  have hBgen : B.gen = Pi := by
    exact PowerBasis.ofAdjoinEqTop_gen hPiIntegral hgenerates
  have hBdim : B.dim = n := by
    rw [PowerBasis.ofAdjoinEqTop_dim, ← hmin,
      natDegree_map_eq_of_injective (IsFractionRing.injective A K), hdegree]
  let e : Fin n ≃ Fin B.dim := finCongr hBdim.symm
  intro x
  let a : Fin n → K := fun i => B.basis.repr x (e i)
  have hsumB : x = ∑ j, algebraMap K L (B.basis.repr x j) * Pi ^ (j : ℕ) := by
    calc
      x = ∑ j, B.basis.repr x j • B.basis j := (B.basis.sum_repr x).symm
      _ = ∑ j, algebraMap K L (B.basis.repr x j) * Pi ^ (j : ℕ) := by
        simp [B.basis_eq_pow, hBgen, Algebra.smul_def]
  have hsum : x = ∑ i, algebraMap K L (a i) * Pi ^ (i : ℕ) := by
    calc
      x = ∑ j, algebraMap K L (B.basis.repr x j) * Pi ^ (j : ℕ) := hsumB
      _ = ∑ i, algebraMap K L (a i) * Pi ^ (i : ℕ) := by
        symm
        refine Fintype.sum_equiv e _ _ ?_
        intro i
        rfl
  refine ⟨a, ?_, ?_⟩
  · simpa [eisensteinExpansion] using hsum
  · intro b hb
    have hexpand (c : Fin n → K) :
        (∑ i, algebraMap K L (c i) * Pi ^ (i : ℕ)) =
          ∑ j, c (e.symm j) • B.basis j := by
      calc
        (∑ i, algebraMap K L (c i) * Pi ^ (i : ℕ)) =
            ∑ i, c i • B.basis (e i) := by
              simp [e, B.basis_eq_pow, hBgen, Algebra.smul_def]
        _ = ∑ j, c (e.symm j) • B.basis j := by
          refine Fintype.sum_equiv e _ _ ?_
          intro i
          simp
    have hcoords :
        (fun j => a (e.symm j)) = (fun j => b (e.symm j)) := by
      have hEq :
          (∑ j, a (e.symm j) • B.basis j) =
            ∑ j, b (e.symm j) • B.basis j := by
        rw [← hexpand a, ← hexpand b]
        exact hsum.symm.trans hb
      have hrepr := congrArg (fun y : L => B.basis.repr y) hEq
      funext j
      have hj := congrArg (fun z : Fin B.dim →₀ K => z j) hrepr
      simpa only [B.basis.repr_sum_self] using hj
    funext i
    exact (congrFun hcoords (e i)).symm

/-- The valuation of the `i`th power-basis term has value congruent to `i mod n`. -/
theorem eisenstein_term_values_are_distinct_modulo_degree
    {n : ℕ} (ω : ℕ → ℤ) (a : Fin n → ℕ) :
    ∀ i j : Fin n, i ≠ j →
      ((n : ℤ) * ω (a i) + (i : ℤ)) % (n : ℤ) ≠
        ((n : ℤ) * ω (a j) + (j : ℤ)) % (n : ℤ) := by
  intro i j hij
  have hn : 0 < n := by
    have hi := i.isLt
    omega
  have hi0 : 0 ≤ (i : ℤ) := by omega
  have hj0 : 0 ≤ (j : ℤ) := by omega
  have hin : (i : ℤ) < (n : ℤ) := by exact_mod_cast i.isLt
  have hjn : (j : ℤ) < (n : ℤ) := by exact_mod_cast j.isLt
  have hmi : ((n : ℤ) * ω (a i) + (i : ℤ)) % (n : ℤ) = (i : ℤ) := by
    rw [show (n : ℤ) * ω (a i) + (i : ℤ) =
        (i : ℤ) + (n : ℤ) * ω (a i) by ring,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt hi0 hin]
  have hmj : ((n : ℤ) * ω (a j) + (j : ℤ)) % (n : ℤ) = (j : ℤ) := by
    rw [show (n : ℤ) * ω (a j) + (j : ℤ) =
        (j : ℤ) + (n : ℤ) * ω (a j) by ring,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt hj0 hjn]
  rw [hmi, hmj]
  intro heq
  apply hij
  apply Fin.ext
  exact_mod_cast heq

/-- A strictly least nonzero term cannot cancel in a nonarchimedean sum. -/
theorem least_valued_term_does_not_cancel
    {L Γ : Type*} [Ring L] [LinearOrderedCommMonoidWithZero Γ]
    (w : Valuation L Γ) {ι : Type*} [Fintype ι] [Nonempty ι]
    (terms : ι → L) (i₀ : ι)
    /- Formal correction: with Mathlib's multiplicative valuation order, the
       dominant term is the strictly greatest-valued one. -/
    (hgreatest : ∀ j, j ≠ i₀ → w (terms j) < w (terms i₀))
    (hnonzero : terms i₀ ≠ 0) :
    w (∑ i, terms i) = w (terms i₀) := by
  classical
  by_cases hzero : terms i₀ = 0
  · exact (hnonzero hzero).elim
  · apply w.map_sum_eq_of_lt (s := Finset.univ) (j := i₀)
    · simp
    · intro i hi
      have hi' : i ≠ i₀ := by simpa using hi
      exact hgreatest i hi'

/-! The root-order theorem is placed before the coefficient criterion so the
    latter can use the integral-closure description directly. -/

 /-- The Eisenstein order is generated by the root. -/
theorem eisenstein_integral_closure_is_root_order
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    (hf : IsEisensteinAt π f) (hroot : aeval Pi f = 0)
    (_hdegree : f.natDegree = n)
    (hgenerates : Algebra.adjoin K ({Pi} : Set L) = ⊤) :
    (integralClosure A L : Set L) =
      (Algebra.adjoin A ({Pi} : Set L) : Set L) := by
  subst n
  have hspan : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A := hf.2.2.2.2
  let _ : (Ideal.span ({π} : Set A)).IsPrime := by
    rw [hspan]
    infer_instance
  have hE : f.IsEisensteinAt (Ideal.span ({π} : Set A)) := by
    apply hf.1.isEisensteinAt_of_mem_of_notMem
    · rw [hspan]
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    · intro i hi
      exact hf.2.2.1 i hi
    · simpa [Ideal.span_singleton_pow] using hf.2.2.2.1
  have hπ0 : π ≠ 0 := by
    intro hπ
    apply IsDiscreteValuationRing.not_a_field A
    have hzero : Ideal.span ({(0 : A)} : Set A) = (⊥ : Ideal A) := by simp
    rw [hπ, hzero] at hspan
    exact hspan.symm
  have hπirr : Irreducible π :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ0 hspan.symm
  have hPiIntegral : IsIntegral A Pi := ⟨f, hf.1, hroot⟩
  have hAinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hPiIntegralK : IsIntegral K Pi := by
    exact hPiIntegral.tower_top
  let B : PowerBasis K L := PowerBasis.ofAdjoinEqTop hPiIntegralK hgenerates
  have hBgen : B.gen = Pi := by
    exact PowerBasis.ofAdjoinEqTop_gen hPiIntegralK hgenerates
  have hirrA : Irreducible f := hE.irreducible inferInstance hf.1.isPrimitive hf.2.1
  have hprimitive : f.IsPrimitive := hf.1.isPrimitive
  have hirrK : Irreducible (f.map (algebraMap A K)) :=
    (hprimitive.irreducible_iff_irreducible_map_fraction_map).mp hirrA
  have hrootK : aeval Pi (f.map (algebraMap A K)) = 0 := by
    simpa only [aeval_map_algebraMap, IsScalarTower.algebraMap_eq A K L] using hroot
  have hminK : f.map (algebraMap A K) = minpoly K Pi :=
    minpoly.eq_of_irreducible_of_monic hirrK hrootK (hf.1.map (algebraMap A K))
  have hmap : (minpoly A Pi).map (algebraMap A K) = f.map (algebraMap A K) := by
    exact (minpoly.isIntegrallyClosed_eq_field_fractions' K hPiIntegral).symm.trans hminK.symm
  have hminA : f = minpoly A Pi := by
    apply Polynomial.ext
    intro i
    apply IsFractionRing.injective A K
    simpa only [coeff_map] using (congrArg (fun q : K[X] => q.coeff i) hmap).symm
  have hEmin : (minpoly A B.gen).IsEisensteinAt (Ideal.span ({π} : Set A)) := by
    rw [hBgen, ← hminA]
    exact hE
  apply Set.Subset.antisymm
  · intro z hz
    change IsIntegral A z at hz
    have hzK : z ∈ Algebra.adjoin K ({Pi} : Set L) := by
      rw [hgenerates]
      trivial
    obtain ⟨d, hd⟩ :=
      multiple_mem_adjoin_of_mem_localization_adjoin
        (nonZeroDivisors A) K ({Pi} : Set L) z hzK
    have hd0 : (d : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
    obtain ⟨m, u, hum⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hπirr
    have hpow : (π ^ m) • z ∈ Algebra.adjoin A ({Pi} : Set L) := by
      have hu :=
        (Algebra.adjoin A ({Pi} : Set L)).smul_mem hd (↑u⁻¹ : A)
      change (↑u⁻¹ : A) • ((d : A) • z) ∈ Algebra.adjoin A ({Pi} : Set L) at hu
      rw [smul_smul, hum] at hu
      simpa using hu
    have hBint : IsIntegral A B.gen := by
      simpa [hBgen] using hPiIntegral
    have hz' : z ∈ Algebra.adjoin A ({B.gen} : Set L) :=
      mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
        (irreducible_iff_prime.mp hπirr) hBint hz hpow hEmin
    simpa [hBgen] using hz'
  · intro z hz
    exact (adjoin_le_integralClosure hPiIntegral) hz

/-- Integrality of an Eisenstein expansion is equivalent to integral coefficients. -/
theorem eisenstein_expansion_integrality_iff
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    (hf : IsEisensteinAt π f) (hroot : aeval Pi f = 0)
    (hdegree : f.natDegree = n)
    (hgenerates : Algebra.adjoin K ({Pi} : Set L) = ⊤)
    (a : Fin n → K) :
    IsIntegral A (eisensteinExpansion Pi a) ↔
      ∀ i, IsLocalization.IsInteger A (a i) := by
  have hspan : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A := hf.2.2.2.2
  let _ : (Ideal.span ({π} : Set A)).IsPrime := by
    rw [hspan]
    infer_instance
  have hE : f.IsEisensteinAt (Ideal.span ({π} : Set A)) := by
    apply hf.1.isEisensteinAt_of_mem_of_notMem
    · rw [hspan]
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    · intro i hi
      exact hf.2.2.1 i hi
    · simpa [Ideal.span_singleton_pow] using hf.2.2.2.1
  have hPiIntegral : IsIntegral A Pi := ⟨f, hf.1, hroot⟩
  have hAinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let _ : Module.IsTorsionFree A L :=
    Module.IsTorsionFree.of_smul_eq_zero (by
      intro r x hrx
      rcases eq_or_ne r 0 with rfl | hr
      · exact Or.inl rfl
      · right
        have hmap : algebraMap A L r ≠ 0 := by
          intro hzero
          apply hr
          apply hAinj
          simpa using hzero
        apply (mul_eq_zero.mp ?_).resolve_left hmap
        simpa [Algebra.smul_def] using hrx)
  have hPiIntegralK : IsIntegral K Pi := hPiIntegral.tower_top
  have hprimitive : f.IsPrimitive := hf.1.isPrimitive
  have hirrA : Irreducible f := hE.irreducible inferInstance hprimitive hf.2.1
  have hirrK : Irreducible (f.map (algebraMap A K)) :=
    (hprimitive.irreducible_iff_irreducible_map_fraction_map).mp hirrA
  have hrootK : aeval Pi (f.map (algebraMap A K)) = 0 := by
    simpa only [aeval_map_algebraMap, IsScalarTower.algebraMap_eq A K L] using hroot
  have hminK : f.map (algebraMap A K) = minpoly K Pi :=
    minpoly.eq_of_irreducible_of_monic hirrK hrootK (hf.1.map (algebraMap A K))
  have hmap : (minpoly A Pi).map (algebraMap A K) = f.map (algebraMap A K) := by
    exact (minpoly.isIntegrallyClosed_eq_field_fractions' K hPiIntegral).symm.trans hminK.symm
  have hminA : f = minpoly A Pi := by
    apply Polynomial.ext
    intro i
    apply IsFractionRing.injective A K
    simpa only [coeff_map] using (congrArg (fun q : K[X] => q.coeff i) hmap).symm
  let C : PowerBasis A (Algebra.adjoin A ({Pi} : Set L)) :=
    Algebra.adjoin.powerBasis' hPiIntegral
  have hCdim : C.dim = n := by
    rw [Algebra.adjoin.powerBasis'_dim hPiIntegral, ← hminA, hdegree]
  let e : Fin n ≃ Fin C.dim := finCongr hCdim.symm
  constructor
  · intro hx
    have hxmem : eisensteinExpansion Pi a ∈
        (Algebra.adjoin A ({Pi} : Set L) : Set L) := by
      rw [← eisenstein_integral_closure_is_root_order π f Pi hf hroot hdegree hgenerates]
      change IsIntegral A (eisensteinExpansion Pi a)
      exact hx
    let xA : Algebra.adjoin A ({Pi} : Set L) := ⟨eisensteinExpansion Pi a, hxmem⟩
    let b : Fin n → K := fun i =>
      algebraMap A K (C.basis.repr xA (e i))
    have hCgen : C.gen =
        (⟨Pi, Algebra.subset_adjoin (Set.mem_singleton Pi)⟩ :
          Algebra.adjoin A ({Pi} : Set L)) := by
      exact Algebra.adjoin.powerBasis'_gen hPiIntegral
    have hsumC : eisensteinExpansion Pi a =
        ∑ j, algebraMap A L (C.basis.repr xA j) * Pi ^ (j : ℕ) := by
      have hsum := congrArg
        (fun y : Algebra.adjoin A ({Pi} : Set L) => (y : L))
        (C.basis.sum_repr xA).symm
      simpa [xA, C.basis_eq_pow, hCgen, Algebra.smul_def] using hsum
    have hsum : eisensteinExpansion Pi a =
        ∑ i, algebraMap A L (C.basis.repr xA (e i)) * Pi ^ (i : ℕ) := by
      calc
        eisensteinExpansion Pi a =
            ∑ j, algebraMap A L (C.basis.repr xA j) * Pi ^ (j : ℕ) := hsumC
        _ = ∑ i, algebraMap A L (C.basis.repr xA (e i)) * Pi ^ (i : ℕ) := by
          symm
          refine Fintype.sum_equiv e _ _ ?_
          intro i
          rfl
    have hbx : eisensteinExpansion Pi a = eisensteinExpansion Pi b := by
      simpa [eisensteinExpansion, b, IsScalarTower.algebraMap_apply A K L] using hsum
    have huniq := eisenstein_power_basis_expansion_unique
      π f Pi hf hroot hdegree hgenerates (eisensteinExpansion Pi a)
    have hba : b = a := huniq.unique hbx rfl
    intro i
    refine ⟨C.basis.repr xA (e i), ?_⟩
    simpa [b] using congrFun hba i
  · intro hcoeff
    change IsIntegral A (∑ i, algebraMap K L (a i) * Pi ^ (i : ℕ))
    refine IsIntegral.sum _ fun i hi => ?_
    rcases hcoeff i with ⟨c, hc⟩
    have hcoef : IsIntegral A (algebraMap K L (a i)) := by
      rw [← hc]
      simpa only [IsScalarTower.algebraMap_apply A K L] using
        (isIntegral_algebraMap : IsIntegral A (algebraMap A L c))
    exact hcoef.mul (hPiIntegral.pow (i : ℕ))

/-- A uniformizer is characterized by generating the maximal ideal. -/
def isUniformizerElement
    (R : Type*) [CommRing R] [IsLocalRing R] (π : R) : Prop :=
  π ∈ IsLocalRing.maximalIdeal R ∧
    IsLocalRing.maximalIdeal R = Ideal.span {π}

/-- An Eisenstein root is a uniformizer and has ramification index equal to the degree. -/
theorem eisenstein_root_is_uniformizer_and_totally_ramified
    {A K L Γ : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L]
    (vK : Valuation K Γ) (v : Valuation L Γ) [vK.HasExtension v]
    [Valuation.IsRankOneDiscrete vK] [Valuation.IsRankOneDiscrete v]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    (hf : IsEisensteinAt π f) (hroot : aeval Pi f = 0)
    (hdegree : f.natDegree = n)
    (hgenerates : Algebra.adjoin K ({Pi} : Set L) = ⊤)
    (hvaluation : v Pi = Valuation.IsRankOneDiscrete.generator v)
    (hbaseIntegers : vK.Integers A)
    (hbaseValuationRing :
      (vK.valuationSubring : Set K) = Set.range (algebraMap A K))
    (hupperIntegralClosure :
      (v.valuationSubring : Set L) = (integralClosure A L : Set L)) :
    v.IsUniformizer Pi ∧
      chapterRamificationIndex vK.valuationSubring v.valuationSubring
          (IsLocalRing.maximalIdeal v.valuationSubring) = n ∧
      chapterResidueDegree vK.valuationSubring v.valuationSubring
          (IsLocalRing.maximalIdeal v.valuationSubring) = 1 ∧
      ∀ a : K, v (algebraMap K L a) = (vK a) ^ n := by
  sorry

/-- The residue field does not change in an Eisenstein extension. -/
theorem eisenstein_residue_field_is_unchanged
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    [IsLocalRing (Algebra.adjoin A ({Pi} : Set L))]
    (hf : IsEisensteinAt π f) (hroot : aeval Pi f = 0)
    (hdegree : f.natDegree = n) :
    Nonempty
      ((A ⧸ IsLocalRing.maximalIdeal A) ≃+*
        (Algebra.adjoin A ({Pi} : Set L) ⧸
          IsLocalRing.maximalIdeal (Algebra.adjoin A ({Pi} : Set L)))) := by
  have hAinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  let B := Algebra.adjoin A ({Pi} : Set L)
  have hPiIntegral : IsIntegral A Pi := ⟨f, hf.1, hroot⟩
  let _ : Algebra.IsIntegral A B := by
    apply Algebra.IsIntegral.adjoin
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hPiIntegral
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_injective_smul_one A B).mpr (by
      intro a b hab
      apply hAinj
      have h := congrArg (fun x : B => (x : L)) (hab)
      have h' : ((algebraMap A B a : B) : L) =
          ((algebraMap A B b : B) : L) := by
        simpa only [Algebra.smul_def, map_mul, map_one, mul_one] using h
      calc
        algebraMap A L a = algebraMap B L (algebraMap A B a) :=
          (IsScalarTower.algebraMap_apply A B L a).symm
        _ = ((algebraMap A B a : B) : L) := rfl
        _ = ((algebraMap A B b : B) : L) := h'
        _ = algebraMap B L (algebraMap A B b) := rfl
        _ = algebraMap A L b := IsScalarTower.algebraMap_apply A B L b)
  have hmcomap :
      (IsLocalRing.maximalIdeal B).comap (algebraMap A B) =
        IsLocalRing.maximalIdeal A := by
    exact IsLocalRing.maximalIdeal_comap (algebraMap A B)
  let piB : B := ⟨Pi, Algebra.subset_adjoin (Set.mem_singleton Pi)⟩
  have hrootB : aeval piB f = 0 := by
    apply Subtype.ext
    change (algebraMap B L) (aeval piB f) = 0
    rw [aeval_def, hom_eval₂]
    change eval₂ ((algebraMap B L).comp (algebraMap A B)) Pi f = 0
    rw [← IsScalarTower.algebraMap_eq A B L]
    simpa [aeval_def] using hroot
  let _ : Nontrivial B := by
    refine ⟨0, 1, ?_⟩
    intro h
    have h' := congrArg (fun x : B => (x : L)) h
    exact zero_ne_one h'
  let _ : (IsLocalRing.maximalIdeal B).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal B).isPrime
  let _ : Nontrivial (B ⧸ IsLocalRing.maximalIdeal B) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  let qB : B →+* (B ⧸ IsLocalRing.maximalIdeal B) :=
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)
  let qA : A →+* (B ⧸ IsLocalRing.maximalIdeal B) :=
    qB.comp (algebraMap A B)
  have hcoeff_zero (i : ℕ) (hi : i < n) : qA (f.coeff i) = 0 := by
    have hfi : f.coeff i ∈ IsLocalRing.maximalIdeal A := by
      have hfi' := hf.2.2.1 i (by simpa [hdegree] using hi)
      rw [hf.2.2.2.2] at hfi'
      exact hfi'
    have hfi' : f.coeff i ∈
        (IsLocalRing.maximalIdeal B).comap (algebraMap A B) := by
      rw [hmcomap]
      exact hfi
    change qB (algebraMap A B (f.coeff i)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hfi'
  have hmap_poly : f.map qA = (X ^ n : (B ⧸ IsLocalRing.maximalIdeal B)[X]) := by
    apply Polynomial.ext
    intro i
    by_cases hi : i < n
    · rw [coeff_map, hcoeff_zero i hi, coeff_X_pow, if_neg (Nat.ne_of_lt hi)]
    · by_cases hin : i = n
      · subst i
        rw [coeff_map, ← hdegree, hf.1.coeff_natDegree, map_one,
          coeff_X_pow_self]
      · have hni : n < i := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hi) (Ne.symm hin)
        have hfi : f.coeff i = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          simpa [hdegree] using hni
        rw [coeff_map, hfi, map_zero, coeff_X_pow, if_neg hin]
  have hrootQ :
      (f.map qA).eval (qB piB) = 0 := by
    change (f.map qA).eval₂ (RingHom.id _) (qB piB) = 0
    rw [eval₂_map]
    have hcomp : (RingHom.id _).comp qA = qB.comp (algebraMap A B) := by
      ext a
      rfl
    rw [hcomp]
    have hq := congrArg qB hrootB
    rw [aeval_def, hom_eval₂] at hq
    exact hq
  have hpiQ : qB piB = 0 := by
    rw [hmap_poly] at hrootQ
    have hz : qB piB = 0 ∧ ¬n = 0 := by simpa using hrootQ
    exact hz.1
  let qMap : A ⧸ IsLocalRing.maximalIdeal A →+*
      B ⧸ IsLocalRing.maximalIdeal B :=
    Ideal.quotientMap (IsLocalRing.maximalIdeal B) (algebraMap A B) hmcomap.ge
  have hsurj : Function.Surjective qMap := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro b
    have hb : (b : L) ∈ B := b.property
    refine Algebra.adjoin_induction
      (p := fun x hx => ∃ u, qMap u = qB ⟨x, hx⟩) ?_ ?_ ?_ ?_ hb
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨0, by simpa [qMap, qB] using hpiQ.symm⟩
    · intro a
      refine ⟨Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a, ?_⟩
      rfl
    · intro x z hx hz hxh hzh
      rcases hxh with ⟨u, hu⟩
      rcases hzh with ⟨v, hv⟩
      refine ⟨u + v, ?_⟩
      simpa only [map_add, hu, hv] using
        (show qMap (u + v) = qB ⟨x + z, add_mem hx hz⟩ by
          rw [map_add, hu, hv, ← qB.map_add]
          rfl)
    · intro x z hx hz hxh hzh
      rcases hxh with ⟨u, hu⟩
      rcases hzh with ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      simpa only [map_mul, hu, hv] using
        (show qMap (u * v) = qB ⟨x * z, mul_mem hx hz⟩ by
          rw [map_mul, hu, hv, ← qB.map_mul]
          rfl)
  have hinj : Function.Injective qMap := by
    apply Ideal.quotientMap_injective'
    exact hmcomap.le
  exact ⟨RingEquiv.ofBijective qMap ⟨hinj, hsurj⟩⟩

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
