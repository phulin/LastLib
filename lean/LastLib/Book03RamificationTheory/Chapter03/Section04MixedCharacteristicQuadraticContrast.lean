import LastLib.Book03RamificationTheory.Chapter03.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section04WorkedEisensteinExtensions
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Section01CorrectingAnApproximateRoot
import Mathlib.FieldTheory.KummerPolynomial

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open Polynomial

/-! ## 3.4. A mixed-characteristic quadratic contrast -/

/- The integral polynomial for `X^2-p` over the `p`-adic integers. -/
def chapter03QuadraticPolynomial
    (p : ℕ) [Fact p.Prime] : (ℤ_[p])[X] :=
  X ^ 2 - C (p : ℤ_[p])

/- A normalized quadratic radical together with its nontrivial symmetry. -/
structure Chapter03QuadraticExtensionData
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra (ℚ_[p]) L]
    [FiniteDimensional (ℚ_[p]) L] where
  π : L
  equation : π ^ 2 = algebraMap (ℚ_[p]) L (p : ℚ_[p])
  generated : Algebra.adjoin (ℚ_[p]) ({π} : Set L) = ⊤
  valuation : AddValuation L (WithTop ℤ)
  uniformizer_value : valuation π = 1
  involution : L ≃ₐ[ℚ_[p]] L
  involution_on_uniformizer : involution π = -π

theorem chapter03_quadratic_polynomial_is_eisenstein
    (p : ℕ) [Fact p.Prime] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
      (p : ℤ_[p]) (chapter03QuadraticPolynomial p) := by
  simpa [chapter03QuadraticPolynomial,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08PadicIntegralRadicalPolynomial,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08RadicalPolynomial] using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_padic_radical_polynomial_is_eisenstein
      p 2 (by decide))

theorem chapter03_quadratic_extension_degree_and_profile
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra (ℚ_[p]) L]
    [FiniteDimensional (ℚ_[p]) L]
    (D : Chapter03QuadraticExtensionData p L)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation
        D.valuation)
    (hext : (Padic.addValuation (p := p)).IsEquiv
      (D.valuation.comap (algebraMap (ℚ_[p]) L))) :
    Module.finrank (ℚ_[p]) L = 2 ∧
      ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
          (Padic.addValuation (p := p)) D.valuation hext,
        ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData d q ∧
            q.degree = 2 ∧ q.ramificationIndex = 2 ∧ q.residueDegree = 1 ∧
            LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified q := by
  sorry

theorem chapter03_quadratic_odd_prime_displacement
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    {L : Type*} [Field L] [Algebra (ℚ_[p]) L]
    (vL : AddValuation L (WithTop ℤ)) (π : L) (σ : L ≃ₐ[ℚ_[p]] L)
    (hπ : vL π = 1) (hσ : σ π = -π)
    (htwo : vL (2 : L) = 0) :
    chapter03DisplacementValue vL σ.toRingEquiv π = 1 := by
  sorry

theorem chapter03_quadratic_two_adic_displacement
    {L : Type*} [Field L] [Algebra (ℚ_[2]) L]
    (vL : AddValuation L (WithTop ℤ)) (π : L) (σ : L ≃ₐ[ℚ_[2]] L)
    (hπ : vL π = 1) (hσ : σ π = -π)
    (htwo : vL (2 : L) = 2) :
    chapter03DisplacementValue vL σ.toRingEquiv π = 3 := by
  sorry

theorem chapter03_quadratic_displacement_identity
    {L : Type*} [Field L] [Algebra (ℚ_[2]) L]
    (vL : AddValuation L (WithTop ℤ)) (π : L) (σ : L ≃ₐ[ℚ_[2]] L)
    (hπ : vL π = 1) (hσ : σ π = -π)
    (htwo : vL (2 : L) = 2) :
    chapter03DisplacementValue vL σ.toRingEquiv π =
        vL ((2 : L) * π) ∧
      vL ((2 : L) * π) = 3 := by
  sorry

theorem chapter03_quadratic_odd_profile
    {G : Type*} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G)
    (hdisp : ∀ {σ : G}, σ ≠ 1 → F.displacement σ = 1)
    (hnontrivial : ∃ σ : G, σ ≠ 1) :
    F.lower (-1) = ⊤ ∧ F.lower 0 = ⊤ ∧ F.lower 1 = ⊥ ∧
      chapter03LowerBreak F 0 := by
  have hprofile :=
    chapter03_one_break_profile_of_constant_displacement F 0 hdisp
  have hbreak := chapter03_one_break_is_unique F 0 hdisp hnontrivial
  exact ⟨F.lower_neg_one, hprofile.1 0 le_rfl, hprofile.2 1 le_rfl, hbreak⟩

theorem chapter03_quadratic_two_adic_profile
    {G : Type*} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G)
    (hdisp : ∀ {σ : G}, σ ≠ 1 → F.displacement σ = 3)
    (hnontrivial : ∃ σ : G, σ ≠ 1) :
    F.lower (-1) = ⊤ ∧ F.lower 0 = ⊤ ∧ F.lower 1 = ⊤ ∧
      F.lower 2 = ⊤ ∧ F.lower 3 = ⊥ ∧ chapter03LowerBreak F 2 := by
  have hprofile :=
    chapter03_one_break_profile_of_constant_displacement F 2 hdisp
  have hbreak := chapter03_one_break_is_unique F 2 hdisp hnontrivial
  exact ⟨F.lower_neg_one, hprofile.1 0 (by omega), hprofile.1 1 (by omega),
    hprofile.1 2 le_rfl, hprofile.2 3 le_rfl, hbreak⟩

theorem chapter03_quadratic_odd_extension_is_tame
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05TameAtResidueCharacteristic
      2 p := by
  sorry

theorem chapter03_quadratic_two_extension_is_wild :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05WildAtResidueCharacteristic
      2 2 := by
  sorry

/- SOURCE_WARNING (3.4): The displayed `p = 2` calculation uses normalized
   valuation `v_L(2)=2`; the odd-prime calculation uses that `2` is a unit.
   The two hypotheses are kept separate above so that the contrast is not
   accidentally stated for an arbitrary mixed-characteristic valuation. -/

end
end LastLib.Book03RamificationTheory.Chapter03
