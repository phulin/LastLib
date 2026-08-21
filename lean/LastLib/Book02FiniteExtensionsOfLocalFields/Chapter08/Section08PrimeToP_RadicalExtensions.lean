import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section04WorkedEisensteinExtensions
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section07RootsOfUnity
import Mathlib.FieldTheory.KummerExtension

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial

/-! # 8.8. Prime-to-`p` radical extensions -/

/-- The Kummer polynomial for a radical extension. -/
def chapter08KummerPolynomial
    {K : Type*} [CommRing K] (a : K) (e : ℕ) : K[X] :=
  X ^ e - C a

/-- The root algebra used by Mathlib's Kummer interface. -/
abbrev chapter08KummerRadicalField
    (K : Type*) [CommRing K] (a : K) (e : ℕ) : Type _ :=
  AdjoinRoot (chapter08KummerPolynomial a e)

/-- The radical presentation appearing in Book §8.8. -/
def chapter08TameRadicalPresentation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (u π : K) (α : L) (e : ℕ) : Prop :=
  algebraMap K L (u * π) = α ^ e ∧
    Algebra.adjoin K ({α} : Set L) = ⊤

/-- Book §8.8: a unit times a uniformizer gives an Eisenstein radical
polynomial of degree `e`. -/
theorem chapter08_tame_radical_polynomial_is_eisenstein
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (π : A) (u : Aˣ) (e : ℕ) (he : 0 < e)
    (hπ : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A)) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π
      (chapter08KummerPolynomial ((u : A) * π) e) := by
  have hspan : Ideal.span ({(u : A) * π} : Set A) =
      Ideal.span ({π} : Set A) :=
    Ideal.span_singleton_mul_left_unit u.isUnit π
  have hmax : IsLocalRing.maximalIdeal A =
      Ideal.span ({(u : A) * π} : Set A) :=
    hπ.trans hspan.symm
  have hr := chapter08_radical_polynomial_is_eisenstein
    ((u : A) * π) hmax e he
  change LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π
    (chapter08RadicalPolynomial ((u : A) * π) e)
  unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt at hr ⊢
  rcases hr with ⟨hmonic, hdegree, hcoeff, hconstant, hprime⟩
  refine ⟨hmonic, hdegree, ?_, ?_, hspan.symm.trans hprime⟩
  · intro i hi
    rw [← hspan]
    exact hcoeff i hi
  · intro hconstant_square
    apply hconstant
    rw [← Ideal.span_singleton_pow, hspan, Ideal.span_singleton_pow]
    exact hconstant_square

/-- Book §8.8: adjoining a root of the tame radical polynomial has the
totally ramified degree-`e`, residue-degree-one profile. -/
theorem chapter08_tame_radical_extension_profile
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (p e : ℕ) (_hp : Nat.Prime p) (_he : Nat.Coprime e p)
    [CharP (IsLocalRing.ResidueField A) p]
    (u : Aˣ) (π : A) (α : L)
    (_hπ : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A)
    (_hroot : chapter08TameRadicalPresentation
      (algebraMap A K (u : A)) (algebraMap A K π) α e)
    (_hdegree : Module.finrank K L = e)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hA : vK.Integers A)
    (hπK : vK (algebraMap A K π) = 1)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = e • vK x) :
    ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
        vK vL hval,
      ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData d q ∧
          q.degree = e ∧ q.ramificationIndex = e ∧ q.residueDegree = 1 ∧
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified q := by
  have he : 0 < e := by
    by_contra h
    have he0 : e = 0 := Nat.eq_zero_of_not_pos h
    have hcop : Nat.Coprime 0 p := by simpa [he0] using _he
    have hpone : p = 1 := by simpa using hcop
    exact _hp.ne_one hpone
  have hscale' := hscale
  clear hscale'
  let P : A[X] := chapter08KummerPolynomial ((u : A) * π) e
  have hE0 := chapter08_tame_radical_polynomial_is_eisenstein π u e he _hπ.symm
  have hE :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10EisensteinAtUniformizer
        P π := by
    rcases hE0 with ⟨hmonic, hdegree, hcoeff, hconstant, hspan⟩
    refine ⟨hmonic, Nat.ne_of_gt hdegree, ?_, ?_⟩
    · intro i hi
      apply Ideal.mem_span_singleton.mp
      exact hcoeff i (by simpa [P] using hi)
    · intro hdiv
      apply hconstant
      exact Ideal.mem_span_singleton.mpr hdiv
  rcases _hroot with ⟨hpow, hgen⟩
  have hroot : Polynomial.eval₂ (algebraMap A L) α P = 0 := by
    have hpow' : α ^ e = algebraMap A L ((u : A) * π) := by
      calc
        α ^ e = algebraMap K L
            (algebraMap A K (u : A) * algebraMap A K π) := hpow.symm
        _ = algebraMap A L ((u : A) * π) := by
          simp [IsScalarTower.algebraMap_apply A K L, map_mul]
    simpa [P, chapter08KummerPolynomial] using (sub_eq_zero.mpr hpow')
  have hPdegree : P.natDegree = e := by
    dsimp [P, chapter08KummerPolynomial]
    rw [natDegree_X_pow_sub_C]
  have hdegree : Module.finrank K L = P.natDegree :=
    _hdegree.trans hPdegree.symm
  obtain ⟨d, q, hd, hqdeg, hqram, hqres, hqtotal⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_eisenstein_totally_ramified_profile
      P π α hE hroot hgen hdegree vK vL hdiscreteK hdiscreteL hval hA hπK
  exact ⟨d, q, hd, hqdeg.trans hPdegree, hqram.trans hPdegree,
    hqres, hqtotal⟩

/-- The ratio by which a Kummer automorphism acts on a chosen radical root.
-/
def chapter08KummerAutomorphismRatio
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (α : L) : L :=
  σ α / α

/-- Book §8.8: the ratio `σ(α)/α` is an `e`th root of unity. -/
theorem chapter08_kummer_automorphism_ratio_is_root_of_unity
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (e : ℕ) (a : K) (α : L) (σ : L ≃ₐ[K] L)
    (hα : α ≠ 0)
    (hroot : α ^ e = algebraMap K L a) :
    chapter08KummerAutomorphismRatio σ α ^ e = 1 := by
  unfold chapter08KummerAutomorphismRatio
  have hσroot : (σ α) ^ e = algebraMap K L a := by
    calc
      (σ α) ^ e = σ (α ^ e) := (map_pow σ α e).symm
      _ = σ (algebraMap K L a) := by rw [hroot]
      _ = algebraMap K L a := σ.commutes a
  have ha : algebraMap K L a ≠ 0 := by
    intro ha0
    apply hα
    exact eq_zero_of_pow_eq_zero (by rw [hroot, ha0])
  rw [div_pow, hσroot, hroot, div_self ha]

/-- Book §8.8: when the base field contains the relevant roots of unity, the
Kummer radical field is Galois and its automorphism group is the roots-of-unity
group. -/
theorem chapter08_kummer_radical_is_galois_with_roots_of_unity
    {K : Type*} [Field K] {a : K} {e : ℕ} [NeZero e]
    [Fact (Irreducible (chapter08KummerPolynomial a e))]
    (hζ : (primitiveRoots e K).Nonempty) :
    IsGalois K (chapter08KummerRadicalField K a e) ∧
      Nonempty
      (rootsOfUnity e K ≃*
          (chapter08KummerRadicalField K a e ≃ₐ[K]
            chapter08KummerRadicalField K a e)) := by
  have H : Irreducible (X ^ e - C a) := by
    simpa [chapter08KummerPolynomial] using
      (Fact.out : Irreducible (chapter08KummerPolynomial a e))
  let _ : Fact (Irreducible (X ^ e - C a)) := ⟨H⟩
  let _ : IsSplittingField K (chapter08KummerRadicalField K a e)
      (X ^ e - C a) := isSplittingField_AdjoinRoot_X_pow_sub_C hζ H
  exact ⟨isGalois_of_isSplittingField_X_pow_sub_C hζ H _,
    ⟨autAdjoinRootXPowSubCEquiv hζ H⟩⟩

/-- The profile-level formulation of an unramified base change which supplies
the missing prime-to-`p` roots of unity. -/
def chapter08UnramifiedRootsOfUnityProfile
    (q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile) : Prop :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified q

/-- Book §8.8: adjoining prime-to-residue-characteristic roots of unity is an
unramified operation in the local-field setting. -/
/- Proof roadmap.

The statement is intentionally about the actual valuation branch, not merely
about a cyclotomic polynomial.  In particular, do not apply
`chapter10_unramified_lift_profile` directly: that theorem asks for an
irreducible separable reduction of a chosen integral polynomial, and proving
that the reduction of the minimal polynomial of `ζ` is irreducible is already
the ramification argument needed here.  The Eisenstein radical profile above
is the opposite (totally ramified) branch and is not relevant.

1. Put `A := vK.toValuation.valuationSubring`,
   `B := vK'.toValuation.valuationSubring`,
   `k := Chapter10ResidueField vK.toValuation`, and
   `l := Chapter10ResidueField vK'.toValuation`.  Install
   `Valuation.HasExtension vK.toValuation vK'.toValuation` with `_hval`, and
   use `Chapter10ResidueFieldMap` for `k →+* l`.  Obtain
   `d : Chapter10HeterogeneousExtensionData vK vK' _hval` from
   `chapter10_heterogeneous_extension_data_exists` (both declarations are in
   `Book01.../Chapter10/Section04RamificationIndexAndResidueDegree.lean`).

2. First prove `0 < e` from `_he` and `Fact.out : p.Prime`.  From
   `_hζ.pow_eq_one` show `vK' ζ = 0`; hence `ζ` and `ζ⁻¹` lie in `B` and give a
   unit `ζB : Bˣ`.  The base residue characteristic and
   `CharP.of_ringHom_of_ne_zero (Chapter10ResidueFieldMap _ _) p
     (Fact.out : p.Prime).ne_zero`
   give `CharP l p`.  Then use
   `CharP.isUnit_natCast_iff` and the geometric-sum argument from
   `chapter07_reduction_preserves_primitive_root_order`
   (`Book02.../Chapter07/Section07RootsOfUnity.lean`) to prove that
   `IsLocalRing.residue B (ζB : B)` is still a primitive `e`th root.  The
   Chapter07 theorem itself needs `[HenselianLocalRing B]`, which is not
   presently available, so reuse its elementary injectivity argument rather
   than trying to manufacture that instance.  Completeness `_hcomplete`
   supplies the corresponding Henselian structure only on `A` via
   `IsAdicComplete.henselianRing` and `HenselianLocalRing.TFAE`.

3. Prove the key integral-model claim
   `Algebra.adjoin A ({ζB : B} : Set B) = ⊤`.  Expand `_hgen` with
   `Algebra.adjoin_eq_span`/the power basis generated by `ζ`; clear a
   coefficient of least `vK`-value, and reduce.  Hensel uniqueness for
   `X ^ e - 1`, supplied by
   `chapter07_prime_to_residue_characteristic_root_lifts_uniquely` on `A`,
   rules out cancellation that would introduce a value outside the base value
   group.  This yields simultaneously:
   (a) every value of `K'` is a base value, so the normalized restriction scale
   from `chapter10_normalized_restriction_formula` is `1`; and
   (b) `l = k[res(ζB)]`, so the residue extension is generated by that root.
   These are the two bridge facts not packaged by the current Chapter07
   cyclotomic interface.

4. Apply `chapter10_normalized_ramification_index_eq_scale` with `n := 1`,
   `_hdiscreteK`, `_hdiscreteK'`, and the scale-one result to get
   `d.ramificationIndex = 1`.  Since the generator of `l/k` is a root of
   `X ^ e - 1` and its derivative is nonzero (use
   `chapter07_prime_to_residue_characteristic_roots_are_simple`), obtain
   `Chapter10ResidueExtensionIsSeparable vK vK'`; together these prove
   `Chapter10UnramifiedBranch vK vK' _hval d`.

5. The heterogeneous fundamental inequality
   `chapter10_heterogeneous_single_extension_fundamental_inequality`, combined
   with the spanning set `1, res(ζB), ..., res(ζB)^(finrank K K' - 1)` coming
   from step 3, gives
   `d.residueDegree = Module.finrank K K'`.  Define
   `q := { degree := Module.finrank K K', ramificationIndex := 1,
     residueDegree := Module.finrank K K' }`; unfold
   `Chapter10ProfileRealizedByData`, `chapter08UnramifiedRootsOfUnityProfile`,
   and `Chapter10Unramified` to assemble all conjuncts.

No extra irreducibility or integral-closure hypothesis should be added to this
consumer: those facts follow from the complete discrete valuation and the
prime-to-`p` cyclotomic generator. -/
theorem chapter08_prime_to_p_roots_of_unity_are_unramified
    {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    (p e : ℕ) [Fact p.Prime] (_he : Nat.Coprime e p)
    (vK : AddValuation K (WithTop ℤ))
    (vK' : AddValuation K' (WithTop ℤ))
    (_hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (_hdiscreteK' :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK')
    (_hval : vK.IsEquiv (AddValuation.comap (algebraMap K K') vK'))
    [CharP (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueField vK) p]
    (_hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
        vK.toValuation.valuationSubring)
    (ζ : K') (_hζ : IsPrimitiveRoot ζ e)
    (_hgen : Algebra.adjoin K ({ζ} : Set K') = ⊤) :
    ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
        vK vK' _hval,
      ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData d q ∧
          q.degree = Module.finrank K K' ∧ q.ramificationIndex = 1 ∧
          q.residueDegree = Module.finrank K K' ∧
          chapter08UnramifiedRootsOfUnityProfile q ∧
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10UnramifiedBranch
            vK vK' _hval d := by
  sorry

/-- The formal derivative of a prime-exponent radical polynomial. -/
theorem chapter08_prime_radical_derivative_formula
    {A : Type*} [CommRing A] (a : A) (p : ℕ) :
    (chapter08KummerPolynomial a p).derivative =
      C (p : A) * X ^ (p - 1) := by
  simp [chapter08KummerPolynomial, Polynomial.derivative_sub,
    Polynomial.derivative_pow]

/-- Book §8.8: in equal characteristic `p`, the prime radical has zero
derivative, which is the wild/inseparable obstruction. -/
theorem chapter08_prime_radical_is_wild_in_equal_characteristic
    {K : Type*} [Field K] (a : K) (p : ℕ) [CharP K p] :
    (chapter08KummerPolynomial a p).derivative = 0 := by
  rw [chapter08_prime_radical_derivative_formula]
  simp

/-- In mixed characteristic the derivative coefficients are all in the
maximal ideal when the residue characteristic divides the exponent;
this is the valuation-theoretic source of the wild warning (Section 8.8). -/
theorem chapter08_prime_radical_derivative_coefficients_in_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A]
    (a : A) (p : ℕ) (hp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    ∀ i, (chapter08KummerPolynomial a p).derivative.coeff i ∈
      IsLocalRing.maximalIdeal A := by
  intro i
  rw [chapter08_prime_radical_derivative_formula]
  by_cases hi : i = p - 1
  · subst i
    simpa using hp
  · simp [hi]

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
