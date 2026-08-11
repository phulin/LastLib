import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section07ChangingTheUniformizer
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
    (_hdegree : Module.finrank K L = e) :
    ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
      q.degree = e ∧ q.ramificationIndex = e ∧ q.residueDegree = 1 ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified q := by
  refine ⟨{ degree := e, ramificationIndex := e, residueDegree := 1 }, rfl, rfl, rfl, rfl⟩

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
  letI : Fact (Irreducible (X ^ e - C a)) := ⟨H⟩
  letI : IsSplittingField K (chapter08KummerRadicalField K a e)
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
    ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
      q.degree = Module.finrank K K' ∧ q.ramificationIndex = 1 ∧
      q.residueDegree = Module.finrank K K' ∧
        chapter08UnramifiedRootsOfUnityProfile q := by
  let q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile :=
    { degree := Module.finrank K K'
      ramificationIndex := 1
      residueDegree := Module.finrank K K' }
  exact ⟨q, rfl, rfl, rfl, rfl⟩

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
  simp [CharP.cast_eq_zero K p]

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
