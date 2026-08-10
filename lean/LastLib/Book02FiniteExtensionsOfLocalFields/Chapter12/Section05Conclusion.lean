import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section04TheMultiplicativePicture

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Polynomial
open scoped BigOperators WithZero Polynomial

/-! ## 12.5. Conclusion -/

/-- Book 2, §12.5: the finite flat degree is the sum of local `e f` blocks. -/
theorem coherent_sum_ramification_times_residue_degree
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsDomain R]
    [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S,
        q.1.ramificationIdx R * q.1.inertiaDeg R = Module.finrank R S := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.final_sum_ramification_times_residue_degree p

/-- Book 2, §12.5: for fraction fields the same equality reads `∑ e f = [L : K]`. -/
theorem coherent_fraction_field_degree_formula
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsDomain R]
    [Algebra (FractionRing R) (FractionRing S)]
    [Module.Finite R S] [Module.Flat R S] [Fintype (p.primesOver S)]
    (hfrac : Module.finrank R S =
      Module.finrank (FractionRing R) (FractionRing S)) :
    ∑ q : p.primesOver S,
        q.1.ramificationIdx R * q.1.inertiaDeg R =
      Module.finrank (FractionRing R) (FractionRing S) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.final_fraction_field_degree_formula p hfrac

/-- Book 2, §12.5: completeness or henselian uniqueness leaves one branch upstairs. -/
theorem coherent_complete_or_henselian_base_has_one_branch
    {K Γ E : Type u} [Field K] [Field E]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K E]
    (v : Valuation K Γ)
    (hunique : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueExtensionToEveryAlgebraicField v)
    [Algebra.IsAlgebraic K E] :
    ∃ W : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension v E,
      ∀ W' : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension v E,
        (letI : LinearOrderedCommGroupWithZero W.valueGroup := W.orderedValueGroup
         letI : LinearOrderedCommGroupWithZero W'.valueGroup := W'.orderedValueGroup
         W'.valuation.IsEquiv W.valuation) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_or_henselian_base_has_one_branch v hunique

/--
Book 2, §12.5: an Eisenstein root supplies coordinates for the totally
ramified direction, including the uniformizer, ramification index, and
residue degree.
-/
theorem coherent_eisenstein_coordinates_control_total_ramification
    {A K L Γ : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L]
    (vK : Valuation K Γ) (v : Valuation L Γ) [vK.HasExtension v]
    [Valuation.IsRankOneDiscrete v]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval Pi f = 0) (hdegree : f.natDegree = n)
    (hgenerates : Algebra.adjoin K ({Pi} : Set L) = ⊤)
    (hvaluation : v Pi = Valuation.IsRankOneDiscrete.generator v)
    (hbase : vK (algebraMap A K π) = (v Pi) ^ n) :
    v.IsUniformizer Pi ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          vK.valuationSubring v.valuationSubring
          (IsLocalRing.maximalIdeal v.valuationSubring) = n ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
          vK.valuationSubring v.valuationSubring
          (IsLocalRing.maximalIdeal v.valuationSubring) = 1 := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_root_is_uniformizer_and_totally_ramified
    vK v π f Pi hf hroot hdegree hgenerates hvaluation hbase

/-- Book 2, §12.5: Eisenstein coordinates leave the residue field unchanged. -/
theorem coherent_eisenstein_coordinates_preserve_residue_field
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    [IsLocalRing (Algebra.adjoin A ({Pi} : Set L))]
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval Pi f = 0) (hdegree : f.natDegree = n) :
    Nonempty
      ((A ⧸ IsLocalRing.maximalIdeal A) ≃+*
        (Algebra.adjoin A ({Pi} : Set L) ⧸
          IsLocalRing.maximalIdeal (Algebra.adjoin A ({Pi} : Set L)))) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_residue_field_is_unchanged
    (A := A) (K := K) (L := L) π f Pi hf hroot hdegree

/-- Book 2, §12.5: the integral closure is the Eisenstein root order. -/
theorem coherent_eisenstein_coordinates_generate_integral_closure
    {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {n : ℕ} (π : A) (f : A[X]) (Pi : L)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval Pi f = 0) (hdegree : f.natDegree = n)
    (hgenerates : Algebra.adjoin K ({Pi} : Set L) = ⊤) :
    (integralClosure A L : Set L) =
      (Algebra.adjoin A ({Pi} : Set L) : Set L) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.eisenstein_integral_closure_is_root_order
    (A := A) (K := K) (L := L) π f Pi hf hroot hdegree hgenerates

/-- Book 2, §12.5: the assembled valuation/ring/residue/branch dictionary. -/
theorem coherent_local_arithmetic_dictionary
    {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [IsLocalRing A] [Algebra A K] [Algebra A B] [Algebra K L] [Algebra B L]
    (P : Ideal B) [P.IsPrime]
    (v : Valuation K ℤᵐ⁰) (w : Valuation L ℤᵐ⁰)
    (hext : v.IsEquiv (w.comap (algebraMap K L)))
    (hP : P.IsMaximal)
    (hcenter : ∀ x : B, x ∈ P ↔ w (algebraMap B L x) < 1) :
    Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Chapter12LocalArithmeticDictionary
        (A := A) (K := K) (B := B) (L := L) P v w) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.local_arithmetic_dictionary
    P v w hext hP hcenter

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
