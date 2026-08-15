import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section06TheValuationRingInAFiniteCompleteExtension
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section06AlgebraicConsequences
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
    : (e = 1 → degree = f) ∧ (f = 1 → degree = e) := by
  constructor
  · intro hunramified
    simpa [hunramified] using hdegree
  · intro htotallyRamified
    simpa [htotallyRamified] using hdegree

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
          (IsLocalRing.maximalIdeal w.valuationSubring) = fbar.natDegree ∧
      fbar.Separable := by
  have hred : LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.residuePolynomial f = fbar := by
    simpa only [LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.residuePolynomial,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.residueMap] using hlift
  have hredirr : Irreducible
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.residuePolynomial f) := by
    rw [hred]
    exact hirreducible
  have hirr : Irreducible (f.map (algebraMap A K)) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.irreducible_of_irreducible_residue_reduction
      f hmonic.2 hredirr
  have hrootK : aeval Pi (f.map (algebraMap A K)) = 0 := hroot
  have hmin : f.map (algebraMap A K) = minpoly K Pi :=
    minpoly.eq_of_irreducible_of_monic hirr hrootK
      (hmonic.2.map (algebraMap A K))
  have hPiIntegral : IsIntegral K Pi :=
    ⟨f.map (algebraMap A K), hmonic.2.map (algebraMap A K), hrootK⟩
  let B : PowerBasis K L := PowerBasis.ofAdjoinEqTop hPiIntegral hgenerates
  have hdim : Module.finrank K L = fbar.natDegree := by
    rw [PowerBasis.finrank B, PowerBasis.ofAdjoinEqTop_dim, ← hmin,
      natDegree_map_eq_of_injective (IsFractionRing.injective A K)]
    calc
      f.natDegree =
          (f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).natDegree :=
        (hmonic.2.natDegree_map _).symm
      _ = fbar.natDegree := congrArg Polynomial.natDegree hlift
  let alg : A →+* vK.valuationSubring :=
    (algebraMap A K).codRestrict vK.valuationSubring
      (fun a => hbaseIntegers.map_le_one a)
  have halg_bij : Function.Bijective alg := by
    constructor
    · intro a b hab
      apply hbaseIntegers.hom_inj
      exact congrArg Subtype.val hab
    · intro x
      obtain ⟨a, ha⟩ :=
        (Set.ext_iff.mp hbaseValuationRing (x : K)).mp x.property
      refine ⟨a, Subtype.ext ?_⟩
      exact ha
  let e : A ≃+* vK.valuationSubring := RingEquiv.ofBijective alg halg_bij
  have hcompleteR : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal A) e).mpr
      (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
  have : Module.Finite K L := B.finite
  have hprod :
      Module.finrank K L =
        chapterRamificationIndex vK.valuationSubring w.valuationSubring
            (IsLocalRing.maximalIdeal w.valuationSubring) *
          chapterResidueDegree vK.valuationSubring w.valuationSubring
            (IsLocalRing.maximalIdeal w.valuationSubring) :=
    complete_extension_defectless_without_separability vK w hcompleteR
  have : Module.Finite vK.valuationSubring w.valuationSubring :=
    complete_extension_unit_ball_is_finite vK w hcompleteR
  have hrootL : aeval Pi f = 0 := by
    simpa only [aeval_map_algebraMap, IsScalarTower.algebraMap_eq A K L] using hrootK
  have hPiA : IsIntegral A Pi := ⟨f, hmonic.2, hrootL⟩
  have hPiB : Pi ∈ (w.valuationSubring : Set L) :=
    (Set.ext_iff.mp hupperIntegralClosure Pi).2 hPiA
  let PiS : w.valuationSubring := ⟨Pi, hPiB⟩
  let aS : A →+* w.valuationSubring :=
    (algebraMap vK.valuationSubring w.valuationSubring).comp alg
  have haS (a : A) :
      (aS a : L) = algebraMap A L a := by
    change algebraMap K L (alg a : K) = algebraMap A L a
    rw [show (alg a : K) = algebraMap A K a by rfl,
      IsScalarTower.algebraMap_apply A K L]
  have hrootS : Polynomial.eval₂ aS PiS f = 0 := by
    apply Subtype.ext
    change algebraMap w.valuationSubring L (Polynomial.eval₂ aS PiS f) = 0
    rw [Polynomial.hom_eval₂]
    have hcomp :
        (algebraMap w.valuationSubring L).comp aS = algebraMap A L := by
      ext a
      exact haS a
    have hPiS :
        (algebraMap w.valuationSubring L) PiS = Pi := rfl
    rw [hcomp, hPiS]
    exact hrootL
  let p : Ideal vK.valuationSubring := IsLocalRing.maximalIdeal vK.valuationSubring
  let q : Ideal w.valuationSubring := IsLocalRing.maximalIdeal w.valuationSubring
  have hmapE : Ideal.map (e : A →+* vK.valuationSubring) (IsLocalRing.maximalIdeal A) = p := by
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  let ebar : (A ⧸ IsLocalRing.maximalIdeal A) ≃+*
      (vK.valuationSubring ⧸ p) :=
    Ideal.quotientEquiv (IsLocalRing.maximalIdeal A) p e hmapE.symm
  have hcomp :
      ((algebraMap (vK.valuationSubring ⧸ p) (w.valuationSubring ⧸ q)).comp
          (ebar : (A ⧸ IsLocalRing.maximalIdeal A) →+* (vK.valuationSubring ⧸ p))).comp
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) =
        (Ideal.Quotient.mk q).comp aS := by
    ext a
    simp [ebar, aS, e, alg, p, q]
  have hbarMonic :
      (fbar.map (ebar : (A ⧸ IsLocalRing.maximalIdeal A) →+*
        (vK.valuationSubring ⧸ p))).Monic :=
    hmonic.1.map (ebar : (A ⧸ IsLocalRing.maximalIdeal A) →+*
      (vK.valuationSubring ⧸ p))
  have hbarIrr : Irreducible
      (fbar.map (ebar : (A ⧸ IsLocalRing.maximalIdeal A) →+*
        (vK.valuationSubring ⧸ p))) := by
    exact Polynomial.Monic.irreducible_of_irreducible_map
      (φ := (ebar.symm : (vK.valuationSubring ⧸ p) →+*
        (A ⧸ IsLocalRing.maximalIdeal A)))
      (f := fbar.map (ebar : (A ⧸ IsLocalRing.maximalIdeal A) →+*
        (vK.valuationSubring ⧸ p))) hbarMonic (by
          simpa [Polynomial.map_map] using hirreducible)
  have hrootSq :
      Polynomial.eval₂ ((Ideal.Quotient.mk q).comp aS)
          (Ideal.Quotient.mk q PiS) f = 0 := by
    have h := congrArg (Ideal.Quotient.mk q) hrootS
    simpa only [Polynomial.hom_eval₂, map_zero] using h
  have hrootbar :
      Polynomial.eval₂ (algebraMap (vK.valuationSubring ⧸ p)
          (w.valuationSubring ⧸ q)) (Ideal.Quotient.mk q PiS) (fbar.map ebar) = 0 := by
    rw [Polynomial.eval₂_map, ← hlift, Polynomial.eval₂_map, hcomp]
    exact hrootSq
  let _ : Field (vK.valuationSubring ⧸ p) := Ideal.Quotient.field p
  let _ : Field (w.valuationSubring ⧸ q) := Ideal.Quotient.field q
  have hminbar : fbar.map ebar =
      minpoly (vK.valuationSubring ⧸ p) (Ideal.Quotient.mk q PiS) :=
    minpoly.eq_of_irreducible_of_monic (A := vK.valuationSubring ⧸ p)
      hbarIrr hrootbar hbarMonic
  have hle : fbar.natDegree ≤
      Module.finrank (vK.valuationSubring ⧸ p) (w.valuationSubring ⧸ q) := by
    have h := minpoly.natDegree_le (A := vK.valuationSubring ⧸ p)
      (B := w.valuationSubring ⧸ q) (Ideal.Quotient.mk q PiS)
    rw [← hminbar] at h
    calc
      fbar.natDegree =
          (fbar.map (ebar : (A ⧸ IsLocalRing.maximalIdeal A) →+*
            (vK.valuationSubring ⧸ p))).natDegree :=
        (hmonic.1.natDegree_map
          (ebar : (A ⧸ IsLocalRing.maximalIdeal A) →+*
            (vK.valuationSubring ⧸ p))).symm
      _ ≤ Module.finrank (vK.valuationSubring ⧸ p) (w.valuationSubring ⧸ q) := h
  have hres0 := Ideal.inertiaDeg_eq_of_isMaximal
    (R := vK.valuationSubring) (S := w.valuationSubring) (p := p) (q := q)
  have hle' : fbar.natDegree ≤
      chapterResidueDegree vK.valuationSubring w.valuationSubring q := by
    calc
      fbar.natDegree ≤
          Module.finrank (vK.valuationSubring ⧸ p) (w.valuationSubring ⧸ q) := hle
      _ = chapterResidueDegree vK.valuationSubring w.valuationSubring q := by
        simpa only [chapterResidueDegree] using hres0.symm
  have hepos : 0 <
      chapterRamificationIndex vK.valuationSubring w.valuationSubring q := by
    unfold chapterRamificationIndex
    exact Ideal.ramificationIdx_pos (R := vK.valuationSubring)
      (S := w.valuationSubring) (q := q)
  have hrespos : 0 <
      chapterResidueDegree vK.valuationSubring w.valuationSubring q := by
    unfold chapterResidueDegree
    exact Ideal.inertiaDeg_pos (R := vK.valuationSubring)
      (S := w.valuationSubring) (q := q)
  have hmul_le :
      chapterRamificationIndex vK.valuationSubring w.valuationSubring q *
          chapterResidueDegree vK.valuationSubring w.valuationSubring q ≤
        chapterResidueDegree vK.valuationSubring w.valuationSubring q := by
    calc
      chapterRamificationIndex vK.valuationSubring w.valuationSubring q *
            chapterResidueDegree vK.valuationSubring w.valuationSubring q =
          Module.finrank K L := hprod.symm
      _ = fbar.natDegree := hdim
      _ ≤ chapterResidueDegree vK.valuationSubring w.valuationSubring q := hle'
  have he_le_one :
      chapterRamificationIndex vK.valuationSubring w.valuationSubring q ≤ 1 := by
    exact Nat.le_of_mul_le_mul_right (by simpa using hmul_le) hrespos
  have heq :
      chapterRamificationIndex vK.valuationSubring w.valuationSubring q = 1 := by
    omega
  have hfq :
      chapterResidueDegree vK.valuationSubring w.valuationSubring q =
        fbar.natDegree := by
    calc
      chapterResidueDegree vK.valuationSubring w.valuationSubring q =
          1 * chapterResidueDegree vK.valuationSubring w.valuationSubring q := by simp
      _ = chapterRamificationIndex vK.valuationSubring w.valuationSubring q *
          chapterResidueDegree vK.valuationSubring w.valuationSubring q := by rw [heq]
      _ = Module.finrank K L := hprod.symm
      _ = fbar.natDegree := hdim
  simpa [p, q] using (show
      Irreducible (f.map (algebraMap A K)) ∧
        Module.finrank K L = fbar.natDegree ∧
        chapterRamificationIndex vK.valuationSubring w.valuationSubring q = 1 ∧
        chapterResidueDegree vK.valuationSubring w.valuationSubring q =
          fbar.natDegree ∧ fbar.Separable from
        ⟨hirr, hdim, heq, hfq, hseparable⟩)

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

/-- Coefficients are integral exactly when they lie in the base ring. -/
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
      /- `Valuation.HasExtension` records the canonical equivalence of the
         restricted and base valuations.  A literal power formula in the
         common codomain requires an additional normalization choice; it is
         not implied by the extension class alone. -/
      vK.IsEquiv (v.comap (algebraMap K L)) ∧
      Module.finrank K L = n := by
  have hPiIntegralA : IsIntegral A Pi := ⟨f, hf.1, hroot⟩
  have hPiIntegralK : IsIntegral K Pi := hPiIntegralA.tower_top
  have hspan : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A :=
    hf.2.2.2.2
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
  have hmin : f.map (algebraMap A K) = minpoly K Pi :=
    minpoly.eq_of_irreducible_of_monic hirrK hrootK (hf.1.map (algebraMap A K))
  let B : PowerBasis K L := PowerBasis.ofAdjoinEqTop hPiIntegralK hgenerates
  have hdim : Module.finrank K L = n := by
    rw [PowerBasis.finrank B, PowerBasis.ofAdjoinEqTop_dim, ← hmin,
      natDegree_map_eq_of_injective (IsFractionRing.injective A K), hdegree]
  let alg : A →+* vK.valuationSubring :=
    (algebraMap A K).codRestrict vK.valuationSubring
      (fun a => hbaseIntegers.map_le_one a)
  have halg_bij : Function.Bijective alg := by
    constructor
    · intro a b hab
      apply hbaseIntegers.hom_inj
      exact congrArg Subtype.val hab
    · intro x
      obtain ⟨a, ha⟩ :=
        (Set.ext_iff.mp hbaseValuationRing (x : K)).mp x.property
      refine ⟨a, Subtype.ext ?_⟩
      exact ha
  let e : A ≃+* vK.valuationSubring := RingEquiv.ofBijective alg halg_bij
  let _ : Module.Finite K L := B.finite
  have hPiB : Pi ∈ (v.valuationSubring : Set L) :=
    (Set.ext_iff.mp hupperIntegralClosure Pi).2 hPiIntegralA
  let PiS : v.valuationSubring := ⟨Pi, hPiB⟩
  have horder :
      (v.valuationSubring : Set L) =
        (Algebra.adjoin A ({Pi} : Set L) : Set L) :=
    hupperIntegralClosure.trans
      (eisenstein_integral_closure_is_root_order π f Pi hf hroot hdegree hgenerates)
  let p : Ideal vK.valuationSubring := IsLocalRing.maximalIdeal vK.valuationSubring
  let q : Ideal v.valuationSubring := IsLocalRing.maximalIdeal v.valuationSubring
  have hmapE : Ideal.map (e : A →+* vK.valuationSubring)
      (IsLocalRing.maximalIdeal A) = p := by
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  let aS : A →+* v.valuationSubring :=
    (algebraMap vK.valuationSubring v.valuationSubring).comp alg
  have haS (a : A) :
      (aS a : L) = algebraMap A L a := by
    change algebraMap K L (alg a : K) = algebraMap A L a
    rw [show (alg a : K) = algebraMap A K a by rfl,
      IsScalarTower.algebraMap_apply A K L]
  have hqover : q.comap (algebraMap vK.valuationSubring v.valuationSubring) = p :=
    (Ideal.over_def q p).symm
  have hAq (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : aS a ∈ q := by
    have hpa : alg a ∈ p := by
      rw [← hmapE]
      exact Ideal.mem_map_of_mem e ha
    change (algebraMap vK.valuationSubring v.valuationSubring) (alg a) ∈ q
    change alg a ∈ q.comap (algebraMap vK.valuationSubring v.valuationSubring)
    rw [hqover]
    exact hpa
  have hrootL : Polynomial.eval₂ (algebraMap A L) Pi f = 0 := by
    simpa only [aeval_def] using hroot
  have hrootS : Polynomial.eval₂ aS PiS f = 0 := by
    apply Subtype.ext
    change algebraMap v.valuationSubring L (Polynomial.eval₂ aS PiS f) = 0
    rw [Polynomial.hom_eval₂]
    have hcompS :
        (algebraMap v.valuationSubring L).comp aS = algebraMap A L := by
      ext a
      exact haS a
    have hPiS : (algebraMap v.valuationSubring L) PiS = Pi := rfl
    rw [hcompS, hPiS]
    exact hrootL
  have hPiS_q : PiS ∈ q := by
    by_contra hnot
    have hPiQ : Ideal.Quotient.mk q PiS ≠ 0 := by
      intro hz
      apply hnot
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hz
    have hrootq :
        Polynomial.eval₂ ((Ideal.Quotient.mk q).comp aS)
            (Ideal.Quotient.mk q PiS) f = 0 := by
      have h := congrArg (Ideal.Quotient.mk q) hrootS
      simpa only [Polynomial.hom_eval₂, map_zero] using h
    have hcoeffq (i : ℕ) (hi : i < n) :
        Ideal.Quotient.mk q (aS (f.coeff i)) = 0 := by
      apply (Ideal.Quotient.eq_zero_iff_mem).2
      apply hAq
      rw [← hspan]
      exact hf.2.2.1 i (by omega)
    have hcoeff_n : f.coeff n = 1 := by
      rw [← hdegree]
      exact hf.1.leadingCoeff
    have hsum :
        (∑ i ∈ Finset.range (n + 1),
          ((Ideal.Quotient.mk q).comp aS) (f.coeff i) *
            (Ideal.Quotient.mk q PiS) ^ i) = 0 := by
      have hnlt : f.natDegree < n + 1 := by
        rw [hdegree]
        exact Nat.lt_succ_self n
      rw [← Polynomial.eval₂_eq_sum_range'
        ((Ideal.Quotient.mk q).comp aS) hnlt (Ideal.Quotient.mk q PiS)]
      exact hrootq
    have hlow :
        (∑ i ∈ Finset.range n,
          ((Ideal.Quotient.mk q).comp aS) (f.coeff i) *
            (Ideal.Quotient.mk q PiS) ^ i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hcoeffq i (Finset.mem_range.mp hi)]
    have hsum' := hsum
    rw [Finset.sum_range_succ, hlow] at hsum'
    have hpow : (Ideal.Quotient.mk q PiS) ^ n = 0 := by
      simpa [hcoeff_n] using hsum'
    exact (pow_ne_zero n hPiQ) hpow
  have hn : 0 < n := by
    rw [← hdegree]
    exact hf.2.1
  let J : Ideal v.valuationSubring := Ideal.span {PiS}
  have hJleq : J ≤ q := by
    apply Ideal.span_le.2
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    simpa [J, hx] using hPiS_q
  have hpowJ (z : v.valuationSubring) (i : ℕ) (hi : 0 < i) :
      z * PiS ^ i ∈ J := by
    apply J.mul_mem_left
    apply Ideal.pow_mem_of_mem
    · exact Ideal.subset_span (Set.mem_singleton PiS)
    · exact hi
  have hroot_sum :
      (∑ i ∈ Finset.range (n + 1), aS (f.coeff i) * PiS ^ i) = 0 := by
    have hnlt : f.natDegree < n + 1 := by
      rw [hdegree]
      exact Nat.lt_succ_self n
    rw [← Polynomial.eval₂_eq_sum_range' aS hnlt PiS]
    exact hrootS
  have hconstJ : aS (f.constantCoeff) ∈ J := by
    have hsum := Finset.add_sum_erase (Finset.range (n + 1))
      (fun i => aS (f.coeff i) * PiS ^ i) (a := 0) (by simp)
    have hrest :
        (∑ i ∈ (Finset.range (n + 1)).erase 0,
          aS (f.coeff i) * PiS ^ i) ∈ J := by
      apply Ideal.sum_mem
      intro i hi
      exact hpowJ _ i (Nat.pos_of_ne_zero (Finset.mem_erase.mp hi).1)
    have hzero :
        aS (f.coeff 0) +
            (∑ i ∈ (Finset.range (n + 1)).erase 0,
              aS (f.coeff i) * PiS ^ i) = 0 := by
      simpa using hsum.trans hroot_sum
    change aS (f.coeff 0) ∈ J
    rw [eq_neg_of_add_eq_zero_left hzero]
    exact J.neg_mem hrest
  have hconstspan : f.constantCoeff ∈ Ideal.span ({π} : Set A) := by
    rw [Polynomial.constantCoeff]
    exact hf.2.2.1 0 (by simpa [hdegree] using hn)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hconstspan
  have hconst_factor : f.constantCoeff = π * u := by
    simpa [Polynomial.constantCoeff, mul_comm] using hu
  have hu_not : u ∉ IsLocalRing.maximalIdeal A := by
    intro hu_max
    have hu_span : u ∈ Ideal.span ({π} : Set A) := by
      rw [hspan]
      exact hu_max
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hu_span
    apply hf.2.2.2.1
    apply Ideal.mem_span_singleton.mpr
    refine ⟨r, ?_⟩
    calc
      f.constantCoeff = π * u := hconst_factor
      _ = π * (π * r) := by rw [hr]
      _ = π ^ 2 * r := by ring
  have huq : aS u ∉ q := by
    intro huq
    have hpu : alg u ∈ p := by
      rw [← hqover]
      exact huq
    have hepu : e u ∈ p := by
      change alg u ∈ p
      exact hpu
    have hemax : e u ∈ Ideal.map (e : A →+* vK.valuationSubring)
        (IsLocalRing.maximalIdeal A) := by
      rw [hmapE]
      exact hepu
    exact hu_not
      ((Ideal.apply_mem_of_equiv_iff (I := IsLocalRing.maximalIdeal A)
        (f := e) (x := u)).mp hemax)
  have huunit : IsUnit (aS u) := (IsLocalRing.notMem_maximalIdeal).mp huq
  have hmulJ : aS π * aS u ∈ J := by
    rw [← map_mul, ← hconst_factor]
    exact hconstJ
  have hπJ : aS π ∈ J := by
    apply (J.unit_mul_mem_iff_mem huunit).mp
    simpa [mul_comm] using hmulJ
  have hbaseJ (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : aS a ∈ J := by
    have ha_span : a ∈ Ideal.span ({π} : Set A) := by
      rw [hspan]
      exact ha
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha_span
    rw [hr, map_mul]
    simpa [mul_comm] using J.mul_mem_left (aS r) hπJ
  have hq_le_J : q ≤ J := by
    intro x hx
    have hxInt : IsIntegral A (x : L) :=
      (Set.ext_iff.mp hupperIntegralClosure (x : L)).1 x.property
    obtain ⟨a, ha, _⟩ :=
      eisenstein_power_basis_expansion_unique π f Pi hf hroot hdegree hgenerates (x : L)
    have hIntExp : IsIntegral A (eisensteinExpansion Pi a) := by
      rw [← ha]
      exact hxInt
    have hcoeff : ∀ i, IsLocalization.IsInteger A (a i) :=
      (eisenstein_expansion_integrality_iff π f Pi hf hroot hdegree hgenerates a).mp hIntExp
    choose c hc using hcoeff
    have hcS (i : Fin n) : algebraMap A L (c i) ∈
        (v.valuationSubring : Set L) := by
      exact (Set.ext_iff.mp hupperIntegralClosure _).2 isIntegral_algebraMap
    let cS : Fin n → v.valuationSubring := fun i =>
      ⟨algebraMap A L (c i), hcS i⟩
    have hcS_eq (i : Fin n) : cS i = aS (c i) := by
      apply Subtype.ext
      change algebraMap A L (c i) = (aS (c i) : L)
      exact (haS (c i)).symm
    have hxeq : x = ∑ i, cS i * PiS ^ (i : ℕ) := by
      apply Subtype.ext
      change algebraMap v.valuationSubring L x =
        algebraMap v.valuationSubring L (∑ i, cS i * PiS ^ (i : ℕ))
      simp only [map_sum, map_mul, map_pow]
      have hax : algebraMap v.valuationSubring L x = eisensteinExpansion Pi a := by
        change (x : L) = _
        exact ha
      rw [hax]
      simp [eisensteinExpansion, cS, PiS, hc, IsScalarTower.algebraMap_apply A K L]
    let i0 : Fin n := ⟨0, hn⟩
    have hrestq :
        (∑ i ∈ Finset.univ.erase i0, cS i * PiS ^ (i : ℕ)) ∈ q := by
      apply Ideal.sum_mem
      intro i hi
      apply hJleq
      exact hpowJ (cS i) (i : ℕ) (Nat.pos_of_ne_zero (by
        intro hi'
        exact (Finset.mem_erase.mp hi).1 (Fin.ext hi')))
    have hsumx := Finset.add_sum_erase Finset.univ
      (fun i : Fin n => cS i * PiS ^ (i : ℕ)) (a := i0) (Finset.mem_univ i0)
    have hsumx0 :
      cS i0 * PiS ^ (i0 : ℕ) +
            (∑ i ∈ Finset.univ.erase i0, cS i * PiS ^ (i : ℕ)) = x := by
      calc
        _ = ∑ i, cS i * PiS ^ (i : ℕ) := hsumx
        _ = x := hxeq.symm
    have htermq : cS i0 * PiS ^ (i0 : ℕ) ∈ q := by
      have h := q.sub_mem hx hrestq
      rw [← hsumx0] at h
      simpa using h
    have hc0q : aS (c i0) ∈ q := by
      simpa [i0, hcS_eq i0] using htermq
    have hpc0 : alg (c i0) ∈ p := by
      rw [← hqover]
      exact hc0q
    have hc0max : c i0 ∈ IsLocalRing.maximalIdeal A := by
      have hec0 : e (c i0) ∈ p := by
        change alg (c i0) ∈ p
        exact hpc0
      have hec0' : e (c i0) ∈ Ideal.map (e : A →+* vK.valuationSubring)
          (IsLocalRing.maximalIdeal A) := by
        rw [hmapE]
        exact hec0
      exact (Ideal.apply_mem_of_equiv_iff (I := IsLocalRing.maximalIdeal A)
        (f := e) (x := c i0)).mp hec0'
    have hc0J : cS i0 ∈ J := by
      rw [hcS_eq i0]
      exact hbaseJ (c i0) hc0max
    rw [hxeq]
    apply Ideal.sum_mem
    intro i hi
    by_cases hi0 : i = i0
    · subst i
      simpa [i0] using hc0J
    · exact hpowJ (cS i) (i : ℕ) (Nat.pos_of_ne_zero (by
        intro hi'
        apply hi0
        apply Fin.ext
        exact hi'))
  let _ : Algebra A v.valuationSubring := aS.toAlgebra
  let _ : IsScalarTower A v.valuationSubring L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    exact (haS a).symm
  have hPiIntegralS : IsIntegral A PiS := by
    refine ⟨f, hf.1, ?_⟩
    change Polynomial.eval₂ aS PiS f = 0
    exact hrootS
  have htop :
      Algebra.adjoin A ({PiS} : Set v.valuationSubring) = ⊤ := by
    apply top_unique
    intro x hx
    have hxL : (x : L) ∈ Algebra.adjoin A ({Pi} : Set L) := by
      exact (Set.ext_iff.mp horder (x : L)).mp x.property
    refine Algebra.adjoin_induction (R := A) (s := ({Pi} : Set L))
      (p := fun y _ => ∀ hy : y ∈ (v.valuationSubring : Set L),
        (⟨y, hy⟩ : v.valuationSubring) ∈
          Algebra.adjoin A ({PiS} : Set v.valuationSubring)) ?_ ?_ ?_ ?_ hxL
        x.property
    · intro y hy hyS
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact Algebra.subset_adjoin (Set.mem_singleton PiS)
    · intro a haS'
      have heq : (⟨algebraMap A L a, haS'⟩ : v.valuationSubring) =
          algebraMap A v.valuationSubring a := by
        apply Subtype.ext
        exact (haS a).symm
      rw [heq]
      exact Subalgebra.algebraMap_mem _ a
    · intro y z hy hz ihy ihz hyzS
      have hyS : y ∈ (v.valuationSubring : Set L) :=
        (Set.ext_iff.mp horder y).2 hy
      have hzS : z ∈ (v.valuationSubring : Set L) :=
        (Set.ext_iff.mp horder z).2 hz
      have heq : (⟨y + z, hyzS⟩ : v.valuationSubring) =
          (⟨y, hyS⟩ : v.valuationSubring) + ⟨z, hzS⟩ := by
        apply Subtype.ext
        rfl
      rw [heq]
      exact add_mem (ihy hyS) (ihz hzS)
    · intro y z hy hz ihy ihz hyzS
      have hyS : y ∈ (v.valuationSubring : Set L) :=
        (Set.ext_iff.mp horder y).2 hy
      have hzS : z ∈ (v.valuationSubring : Set L) :=
        (Set.ext_iff.mp horder z).2 hz
      have heq : (⟨y * z, hyzS⟩ : v.valuationSubring) =
          (⟨y, hyS⟩ : v.valuationSubring) * ⟨z, hzS⟩ := by
        apply Subtype.ext
        rfl
      rw [heq]
      exact mul_mem (ihy hyS) (ihz hzS)
  let C : Subalgebra A v.valuationSubring :=
    Algebra.adjoin A ({PiS} : Set v.valuationSubring)
  let _ : Module.Finite A C := by
    dsimp [C]
    exact Algebra.finite_adjoin_simple_of_isIntegral hPiIntegralS
  let fC : C →ₐ[A] v.valuationSubring :=
    { toFun := fun x => x.1
      map_one' := rfl
      map_add' := by intro x y; rfl
      map_mul' := by intro x y; rfl
      map_zero' := rfl
      commutes' := by intro a; rfl }
  have hfC : Function.Surjective fC := by
    intro x
    have hxC : x ∈ C := by
      change x ∈ Algebra.adjoin A ({PiS} : Set v.valuationSubring)
      rw [htop]
      trivial
    exact ⟨⟨x, hxC⟩, rfl⟩
  let _ : Module.Finite A v.valuationSubring :=
    Module.Finite.of_surjective fC.toLinearMap hfC
  let _ : Algebra vK.valuationSubring A := e.symm.toRingHom.toAlgebra
  let _ : IsScalarTower vK.valuationSubring A v.valuationSubring := by
    apply IsScalarTower.of_algebraMap_eq'
    ext r
    calc
      ((algebraMap vK.valuationSubring v.valuationSubring r :
          v.valuationSubring) : L) = algebraMap K L (r : K) :=
        Valuation.HasExtension.coe_algebraMap_valuationSubring_eq vK v r
      _ = algebraMap K L (algebraMap A K (e.symm r)) := by
        congr 1
        change (r : K) = (alg (e.symm r) : K)
        calc
          (r : K) = (e (e.symm r) : K) := by rw [e.apply_symm_apply]
          _ = (alg (e.symm r) : K) := by
            change ((RingEquiv.ofBijective alg halg_bij) (e.symm r) : K) = _
            rw [RingEquiv.ofBijective_apply]
      _ = algebraMap A L (e.symm r) := by
        rw [IsScalarTower.algebraMap_apply A K L]
      _ = ((algebraMap A v.valuationSubring (e.symm r) :
          v.valuationSubring) : L) := (haS (e.symm r)).symm
  let ea : vK.valuationSubring ≃ₐ[vK.valuationSubring] A :=
    AlgEquiv.ofRingEquiv (f := e.symm) (by intro r; rfl)
  let _ : Module.Finite vK.valuationSubring A :=
    Module.Finite.equiv ea.toLinearEquiv
  let _ : Module.Finite vK.valuationSubring v.valuationSubring :=
    Module.Finite.trans A v.valuationSubring
  let _ : Module.IsTorsionFree vK.valuationSubring v.valuationSubring := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a x hax
    rcases eq_or_ne a 0 with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr (mul_left_cancel₀
        (show algebraMap vK.valuationSubring v.valuationSubring a ≠ 0 by
          intro h
          have hz : algebraMap vK.valuationSubring v.valuationSubring a =
              algebraMap vK.valuationSubring v.valuationSubring (0 : vK.valuationSubring) := by
            simpa using h
          exact ha ((Valuation.HasExtension.algebraMap_injective
            (vK := vK) (vA := v)) hz))
        (by simpa [Algebra.smul_def] using hax))
  let _ : Module.Free vK.valuationSubring v.valuationSubring := by infer_instance
  let _ : FaithfulSMul vK.valuationSubring v.valuationSubring :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Valuation.HasExtension.algebraMap_injective (vK := vK) (vA := v))
  let _ : Fintype (p.primesOver v.valuationSubring) :=
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver p)
  have hq_eq (q' : p.primesOver v.valuationSubring) :
      q'.1 = IsLocalRing.maximalIdeal v.valuationSubring := by
    exact IsLocalRing.eq_maximalIdeal
      (q'.2.1.isMaximal
        (Ideal.ne_bot_of_mem_primesOver
          (IsDiscreteValuationRing.not_a_field vK.valuationSubring) q'.2))
  let _ : Unique (p.primesOver v.valuationSubring) :=
    { default := Ideal.primesOver.mk p
        (IsLocalRing.maximalIdeal v.valuationSubring)
      uniq := fun q' => Subtype.ext (hq_eq q') }
  have hdefault :
      (default : p.primesOver v.valuationSubring).1 =
        IsLocalRing.maximalIdeal v.valuationSubring :=
    hq_eq default
  have hfinrank :
      Module.finrank vK.valuationSubring v.valuationSubring =
        Module.finrank K L := by
    exact (IsFractionRing.finrank_eq vK.valuationSubring K
      v.valuationSubring L).symm
  have hsum :=
    Ideal.sum_ramification_inertia_eq_finrank
      (p := p) (S := v.valuationSubring)
  rw [Fintype.sum_unique, hfinrank] at hsum
  have hprod :
      chapterRamificationIndex vK.valuationSubring v.valuationSubring q *
          chapterResidueDegree vK.valuationSubring v.valuationSubring q =
        Module.finrank K L := by
    simpa only [chapterRamificationIndex, chapterResidueDegree, hdefault] using hsum
  let qS : v.valuationSubring →+* (v.valuationSubring ⧸ q) :=
    Ideal.Quotient.mk q
  let qA : A →+* (v.valuationSubring ⧸ q) := qS.comp aS
  have hsurjA : Function.Surjective qA := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro b
    have hb : b ∈ Algebra.adjoin A ({PiS} : Set v.valuationSubring) := by
      rw [htop]
      trivial
    refine Algebra.adjoin_induction (R := A)
      (s := ({PiS} : Set v.valuationSubring))
      (p := fun x _ => ∃ a : A, qA a = qS x) ?_ ?_ ?_ ?_ hb
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      refine ⟨0, ?_⟩
      simpa [qA, qS] using
        ((Ideal.Quotient.eq_zero_iff_mem).2 hPiS_q).symm
    · intro a
      exact ⟨a, rfl⟩
    · intro x z hx hz ihx ihz
      rcases ihx with ⟨a, ha⟩
      rcases ihz with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      exact (show qA (a + b) = qS (x + z) by
        rw [map_add, ha, hb, ← qS.map_add])
    · intro x z hx hz ihx ihz
      rcases ihx with ⟨a, ha⟩
      rcases ihz with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      exact (show qA (a * b) = qS (x * z) by
        rw [map_mul, ha, hb, ← qS.map_mul])
  let qMap :
      (vK.valuationSubring ⧸ p) →+* (v.valuationSubring ⧸ q) :=
    Ideal.quotientMap q (algebraMap vK.valuationSubring v.valuationSubring)
      hqover.ge
  have hsurj : Function.Surjective qMap := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hsurjA (qS b)
    refine ⟨Ideal.Quotient.mk p (alg a), ?_⟩
    simpa [qMap, qS, qA, aS] using ha
  have hinj : Function.Injective qMap := by
    apply Ideal.quotientMap_injective'
    exact hqover.le
  let _ : Algebra (vK.valuationSubring ⧸ p)
      (v.valuationSubring ⧸ q) :=
    Ideal.Quotient.algebraQuotientOfLEComap hqover.ge
  let _ : Field (vK.valuationSubring ⧸ p) := Ideal.Quotient.field p
  let _ : Field (v.valuationSubring ⧸ q) := Ideal.Quotient.field q
  have hresfin :
      Module.finrank (vK.valuationSubring ⧸ p)
          (v.valuationSubring ⧸ q) = 1 := by
    apply Module.finrank_of_bijective_algebraMap
    simpa [qMap] using ⟨hinj, hsurj⟩
  have hres0 := Ideal.inertiaDeg_eq_of_isMaximal
    (R := vK.valuationSubring) (S := v.valuationSubring) (p := p) (q := q)
  have hfq :
      chapterResidueDegree vK.valuationSubring v.valuationSubring q = 1 := by
    calc
      chapterResidueDegree vK.valuationSubring v.valuationSubring q =
          Module.finrank (vK.valuationSubring ⧸ p)
            (v.valuationSubring ⧸ q) := by
        simpa only [chapterResidueDegree] using hres0
      _ = 1 := hresfin
  have heq :
      chapterRamificationIndex vK.valuationSubring v.valuationSubring q = n := by
    calc
      chapterRamificationIndex vK.valuationSubring v.valuationSubring q =
          Module.finrank K L := by
        simpa [hfq] using hprod
      _ = n := hdim
  have hqJ : q = J := le_antisymm hq_le_J hJleq
  have huniform : v.IsUniformizer Pi := by
    apply Valuation.isUniformizer_of_maximalIdeal_eq_span (v := v) (r := PiS)
    simpa [q, J] using hqJ
  have hequiv : vK.IsEquiv (v.comap (algebraMap K L)) :=
    Valuation.HasExtension.val_isEquiv_comap (vR := vK) (vA := v)
  simpa [p, q] using (show
      v.IsUniformizer Pi ∧
        chapterRamificationIndex vK.valuationSubring v.valuationSubring q = n ∧
        chapterResidueDegree vK.valuationSubring v.valuationSubring q = 1 ∧
        vK.IsEquiv (v.comap (algebraMap K L)) ∧
        Module.finrank K L = n from
    ⟨huniform, heq, hfq, hequiv, hdim⟩)

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
