import LastLib.Book03RamificationTheory.Chapter03.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section04WorkedEisensteinExtensions
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.Section06ResiduesAndLeadingCoefficients
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open Polynomial
open scoped BigOperators LaurentSeries

/-! ## 3.3. An equal-characteristic wild extension -/

/- The Artin--Schreier equation used throughout this section. -/
def chapter03ArtinSchreierEquation
    (K : Type*) [Field K] (p m : ℕ) (t y : K) : Prop :=
  y ^ p - y = t ^ (-(m : ℤ))

/- The polynomial form of an Artin--Schreier equation. -/
def chapter03ArtinSchreierPolynomial
    {K : Type*} [CommRing K] (p : ℕ) (a : K) : K[X] :=
  X ^ p - X - C a

def chapter03ArtinSchreierRootSet
    {K : Type*} [Field K] (p : ℕ) (a : K) : Set K :=
  {z | z ^ p - z = a}

/- The equation and generation data for `y^p-y=t^{-m}`. -/
structure Chapter03ArtinSchreierExtensionData
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p] where
  y : L
  positive_exponent : 0 < m
  prime_to_characteristic : Nat.Coprime m p
  equation :
    chapter03ArtinSchreierEquation L p m
      (algebraMap (LaurentSeries k) L
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k)) y
  generated : Algebra.adjoin (LaurentSeries k) ({y} : Set L) = ⊤

theorem chapter03_artin_schreier_derivative
    {K : Type*} [Field K] (p : ℕ) [CharP K p] (a : K) :
    (chapter03ArtinSchreierPolynomial p a).derivative = -1 := by
  sorry

theorem chapter03_artin_schreier_no_root_in_laurent_series
    (k : Type*) [Field k] (p m : ℕ) [Fact p.Prime] [CharP k p]
    (hm : Nat.Coprime m p) :
    ∀ z : LaurentSeries k,
      z ^ p - z ≠
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) ^
          (-(m : ℤ)) := by
  sorry

theorem chapter03_artin_schreier_translation
    {K : Type*} [Field K] (p : ℕ) [CharP K p]
    (a y z : K) (hroot : y ^ p - y = a) :
    (y - z) ^ p - (y - z) = a - (z ^ p - z) := by
  sorry

theorem chapter03_artin_schreier_root_set_is_a_translation
    {K : Type*} [Field K] (p : ℕ) [CharP K p]
    (a y : K) (hroot : y ^ p - y = a) :
    chapter03ArtinSchreierRootSet p a =
      {z | ∃ c : K, c ^ p - c = 0 ∧ z = y + c} := by
  sorry

theorem chapter03_artin_schreier_irreducible_of_no_root
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (a : K)
    (hno_root : ∀ z : K, z ^ p - z ≠ a) :
    Irreducible (chapter03ArtinSchreierPolynomial p a) := by
  sorry

theorem chapter03_artin_schreier_roots_form_a_prime_order_orbit
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (a y : K) (hroot : y ^ p - y = a) :
    ∀ z : K, z ^ p - z = a →
      ∃ c : K, c ^ p - c = 0 ∧ z = y + c := by
  sorry

theorem chapter03_artin_schreier_degree_and_cyclic_profile
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (D : Chapter03ArtinSchreierExtensionData (k := k) (L := L) p m)
    (hno_root :
      ∀ z : LaurentSeries k,
        z ^ p - z ≠
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) ^
            (-(m : ℤ))) :
    Module.finrank (LaurentSeries k) L = p ∧
      ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
        q.degree = p ∧ q.ramificationIndex = p ∧ q.residueDegree = 1 := by
  sorry

theorem chapter03_artin_schreier_y_has_normalized_value
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (D : Chapter03ArtinSchreierExtensionData (k := k) (L := L) p m)
    (vL : AddValuation L (WithTop ℤ))
    (hvalue_t :
      vL (algebraMap (LaurentSeries k) L
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k)) = p) :
    vL D.y = -m := by
  sorry

theorem chapter03_artin_schreier_extension_is_cyclic_galois
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    [FiniteDimensional (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (D : Chapter03ArtinSchreierExtensionData (k := k) (L := L) p m)
    (hno_root :
      ∀ z : LaurentSeries k,
        z ^ p - z ≠
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) ^
            (-(m : ℤ))) :
    IsGalois (LaurentSeries k) L ∧
      Module.finrank (LaurentSeries k) L = p ∧
      ∃ γ : L ≃ₐ[LaurentSeries k] L,
        orderOf γ = p ∧
          (∀ σ : L ≃ₐ[LaurentSeries k] L,
            ∃ n : ℤ, γ ^ n = σ) ∧
          (∀ c : L, c ^ p - c = 0 →
            ∃ σ : L ≃ₐ[LaurentSeries k] L, σ D.y = D.y + c) := by
  sorry

/- The chosen uniformizer `t^a y^b` in the source calculation. -/
def chapter03ArtinSchreierUniformizer
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    (y : L) (a : ℤ) (b : ℕ) : L :=
  algebraMap (LaurentSeries k) L
    ((LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k) ^ a) * y ^ b

theorem chapter03_artin_schreier_bezout_indices
    (p m : ℕ) (hm : Nat.Coprime m p) :
    ∃ a : ℤ, ∃ b : ℕ,
      1 ≤ b ∧ b < p ∧ a * p - b * m = 1 := by
  sorry

theorem chapter03_artin_schreier_chosen_uniformizer_has_value_one
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (vL : AddValuation L (WithTop ℤ)) (y : L) (a : ℤ) (b : ℕ)
    (hvalue_t :
      vL (algebraMap (LaurentSeries k) L
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesUniformizer k)) = p)
    (hvalue_y : vL y = -m)
    (hindices : a * p - b * m = 1) :
    vL (chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b) = 1 := by
  sorry

theorem chapter03_artin_schreier_displacement_calculation
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (vL : AddValuation L (WithTop ℤ)) (y : L) (a : ℤ) (b : ℕ)
    (σ : L ≃ₐ[LaurentSeries k] L) (c : L)
    (hvalue_y : vL y = -m)
    (hvalue_c : vL c = 0)
    (hindices : a * p - b * m = 1)
    (hb : 1 ≤ b) (hbp : b < p)
    (hc : c ^ p - c = 0) (hσy : σ y = y + c) :
    vL (σ (chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b) -
      chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b) = m + 1 := by
  sorry

theorem chapter03_artin_schreier_uniformizer_ratio
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (y : L) (a : ℤ) (b : ℕ) (σ : L ≃ₐ[LaurentSeries k] L) (c : L)
    (hy : y ≠ 0) (hσy : σ y = y + c) :
    σ (chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b) /
        chapter03ArtinSchreierUniformizer (k := k) (L := L) y a b =
      (1 + c / y) ^ b := by
  sorry

theorem chapter03_artin_schreier_first_binomial_term_has_value_m
    {k L : Type*} [Field k] [Field L]
    [Algebra (LaurentSeries k) L]
    (p m : ℕ) [Fact p.Prime] [CharP k p]
    (vL : AddValuation L (WithTop ℤ)) (y c : L) (b : ℕ)
    (hvalue_y : vL y = -m) (hvalue_c : vL c = 0)
    (hb : 1 ≤ b) (hbp : b < p) (hc : c ^ p - c = 0) :
    vL ((1 + c / y) ^ b - 1) = m := by
  sorry

theorem chapter03_artin_schreier_lower_groups
    {G : Type*} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) (m : ℕ)
    (hdisp : ∀ {σ : G}, σ ≠ 1 → F.displacement σ = m + 1)
    (hnontrivial : ∃ σ : G, σ ≠ 1) :
    F.lower (-1) = ⊤ ∧
      (∀ n : ℕ, n ≤ m → F.lower (n : ℤ) = ⊤) ∧
      (∀ n : ℕ, m + 1 ≤ n → F.lower (n : ℤ) = ⊥) ∧
      chapter03LowerBreak F m := by
  have hprofile :=
    chapter03_one_break_profile_of_constant_displacement F m hdisp
  have hbreak := chapter03_one_break_is_unique F m hdisp hnontrivial
  exact ⟨F.lower_neg_one, hprofile.1, hprofile.2, hbreak⟩

/- Changing an Artin--Schreier coordinate changes the right side by an
additive coboundary. -/
theorem chapter03_artin_schreier_change_of_variable
    {K : Type*} [Field K] (p : ℕ) [CharP K p]
    (y z a : K) (hroot : y ^ p - y = a) :
    (y - z) ^ p - (y - z) = a - (z ^ p - z) := by
  exact chapter03_artin_schreier_translation p a y z hroot

theorem chapter03_artin_schreier_divisible_exponent_is_a_coboundary
    {K : Type*} [Field K] (p r : ℕ) [CharP K p] (t : K) :
    t ^ (-(p * r : ℤ)) =
      (t ^ (-(r : ℤ))) ^ p := by
  sorry

/- SOURCE_ISSUE (3.3): The informal sentence that terms with exponent
   divisible by `p` can be removed by replacing `y` by `y - z` is too strong
   for an arbitrary coefficient field `k`: a leading coefficient can be
   removed this way only when it is a `p`th power (or when `k` is perfect).
   The smallest correction is to say “terms that occur in an Artin--Schreier
   coboundary,” or to add perfectness of `k`. -/

/- SOURCE_WARNING (3.3): The restriction `p ∤ m` is a normal-form choice,
   not a restriction on all Artin--Schreier classes.  The preceding change of
   variable and coboundary identity records the precise coordinate operation
   that removes exponents divisible by `p`. -/

end
end LastLib.Book03RamificationTheory.Chapter03
