import LastLib.Book03RamificationTheory.Chapter03.Dependencies
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section09MixedExtensionsInCoordinates
import Mathlib.FieldTheory.Galois.Basic

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open scoped BigOperators Pointwise

/-! ## 3.6. A mixed unramified--tame extension -/

/- The numerical and coordinate data for `K_f/K` followed by a tame radical. -/
structure Chapter03MixedUnramifiedTameData
    (K Kf L k : Type*) [Field K] [Field Kf] [Field L] [Field k]
    [Algebra K Kf] [Algebra Kf L] [Algebra K L]
    [IsScalarTower K Kf L]
    [FiniteDimensional K Kf] [FiniteDimensional Kf L]
    [FiniteDimensional K L] [Fintype k]
    (p e f q : ℕ) [Fact p.Prime] [CharP k p] where
  residue_card : Fintype.card k = q
  positive_ramification_degree : 0 < e
  positive_unramified_degree : 0 < f
  prime_to_residue_characteristic : Nat.Coprime e p
  unramified_degree : Module.finrank K Kf = f
  arithmetic_frobenius : Kf ≃ₐ[K] Kf
  unramified_stage :
    ∃ r : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
      r.degree = f ∧ r.ramificationIndex = 1 ∧ r.residueDegree = f ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified r
  unramified_is_galois : IsGalois K Kf
  root_of_unity_order : e ∣ q ^ f - 1
  ζ : Kf
  primitive_root : IsPrimitiveRoot ζ e
  frobenius_on_tame_root : arithmetic_frobenius ζ = ζ ^ q
  πK : K
  α : L
  radical_equation :
    algebraMap Kf L (algebraMap K Kf πK) = α ^ e
  generated : Algebra.adjoin Kf ({α} : Set L) = ⊤
  ramified_degree : Module.finrank Kf L = e

/- A witness for the semidirect Frobenius--tame-inertia presentation. -/
structure Chapter03MixedGaloisWitness
    {K Kf L : Type*} [Field K] [Field Kf] [Field L]
    [Algebra K Kf] [Algebra Kf L] [Algebra K L]
    [IsScalarTower K Kf L]
    (e q : ℕ) where
  frobenius_on_stage : Kf ≃ₐ[K] Kf
  ζ : Kf
  α : L
  primitive_root : IsPrimitiveRoot ζ e
  F : Gal(L / K)
  τ : Gal(L / K)
  F_restricts :
    ∀ x : Kf,
      F (algebraMap Kf L x) =
        algebraMap Kf L (frobenius_on_stage x)
  F_fixes_radical : F α = α
  tame_action : τ α = algebraMap Kf L ζ * α
  frobenius_on_tame_root : frobenius_on_stage ζ = ζ ^ q
  conjugation : F * τ * F⁻¹ = τ ^ q
  tame_order : orderOf τ = e

/- The source-facing relations, with the chosen radical root explicit. -/
def chapter03MixedFrobeniusTameRelations
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (e q : ℕ) (F τ : L ≃ₐ[K] L) (ζ α : L) : Prop :=
  F α = α ∧ τ α = ζ * α ∧ F ζ = ζ ^ q ∧
    F * τ * F⁻¹ = τ ^ q ∧ orderOf τ = e

theorem chapter03_mixed_extension_has_degree_ef
    {K Kf L k : Type*} [Field K] [Field Kf] [Field L] [Field k]
    [Algebra K Kf] [Algebra Kf L] [Algebra K L]
    [IsScalarTower K Kf L]
    [FiniteDimensional K Kf] [FiniteDimensional Kf L]
    [FiniteDimensional K L] [Fintype k]
    (p e f q : ℕ) [Fact p.Prime] [CharP k p]
    (D : Chapter03MixedUnramifiedTameData K Kf L k p e f q) :
    Module.finrank K L = e * f := by
  sorry

theorem chapter03_mixed_extension_galois_presentation
    {K Kf L k : Type*} [Field K] [Field Kf] [Field L] [Field k]
    [Algebra K Kf] [Algebra Kf L] [Algebra K L]
    [IsScalarTower K Kf L]
    [FiniteDimensional K Kf] [FiniteDimensional Kf L]
    [FiniteDimensional K L] [Fintype k]
    (p e f q : ℕ) [Fact p.Prime] [CharP k p]
    (D : Chapter03MixedUnramifiedTameData K Kf L k p e f q)
    (hseparable :
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08KummerPolynomial
        (algebraMap K Kf D.πK) e).Separable) :
    IsGalois K L ∧
      ∃ F τ : Gal(L / K),
        (∀ x : Kf,
          F (algebraMap Kf L x) =
            algebraMap Kf L (D.arithmetic_frobenius x)) ∧
        F D.α = D.α ∧
        τ D.α = algebraMap Kf L D.ζ * D.α ∧
        F (algebraMap Kf L D.ζ) =
          algebraMap Kf L (D.ζ ^ q) ∧
        F * τ * F⁻¹ = τ ^ q ∧ orderOf τ = e := by
  sorry

theorem chapter03_mixed_frobenius_tame_conjugation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (e q : ℕ) (F τ : L ≃ₐ[K] L) (ζ α : L)
    (hFα : F α = α) (hτα : τ α = ζ * α)
    (hFζ : F ζ = ζ ^ q)
    (hrelation : F * τ * F⁻¹ = τ ^ q)
    (horder : orderOf τ = e) :
    chapter03MixedFrobeniusTameRelations
      e q F τ ζ α := ⟨hFα, hτα, hFζ, hrelation, horder⟩

theorem chapter03_mixed_lower_filtration
    {G : Type*} [Group G] [Finite G]
    (F : LastLib.Book03RamificationTheory.Chapter02.Chapter02LowerFiltration G)
    (τ : G)
    (hinside : ∀ {σ : G}, σ ∈ Subgroup.zpowers τ → σ ≠ 1 →
      F.displacement σ = (1 : WithTop ℤ))
    (houtside : ∀ {σ : G}, σ ∉ Subgroup.zpowers τ →
      F.displacement σ = (0 : WithTop ℤ)) :
    LastLib.Book03RamificationTheory.Chapter02.chapter02IntegerLowerGroup F (-1) = ⊤ ∧
      F.group 0 = Subgroup.zpowers τ ∧ F.group 1 = ⊥ := by
  exact ⟨LastLib.Book03RamificationTheory.Chapter02.chapter02IntegerLowerGroup_neg_one F,
    (chapter03_tame_profile_of_inertia_displacement F (Subgroup.zpowers τ)
      hinside houtside).1,
    (chapter03_tame_profile_of_inertia_displacement F (Subgroup.zpowers τ)
      hinside houtside).2⟩

/- The numerical upstairs/downstairs exponent profile for this mixed tame
stage.  Its field-theoretic interpretation is deferred to the later different
theory; these definitions do not assume that interpretation. -/
def chapter03MixedDifferentExponent (e : ℕ) : ℕ := e - 1

def chapter03MixedDiscriminantExponent (e f : ℕ) : ℕ :=
  f * chapter03MixedDifferentExponent e

theorem chapter03_mixed_different_and_discriminant_exponents
    (e f : ℕ) :
    chapter03MixedDifferentExponent e = e - 1 ∧
      chapter03MixedDiscriminantExponent e f = f * (e - 1) := by
  simp [chapter03MixedDifferentExponent, chapter03MixedDiscriminantExponent]

theorem chapter03_mixed_residue_degree_only_changes_downstairs_exponent
    (e f : ℕ) :
    chapter03MixedDifferentExponent e = e - 1 ∧
      chapter03MixedDiscriminantExponent e f =
        f * chapter03MixedDifferentExponent e := by
  exact ⟨rfl, rfl⟩

/- The identification of these numerical profile values with the actual
   different and discriminant belongs to the later Hilbert/different theory;
   this chapter records only the arithmetic profile without making that later
   theorem a hypothesis of its own conclusion. -/

/- SOURCE_WARNING (3.6): The semidirect presentation needs the chosen lift
   `F` and the chosen tame generator `τ`; the filtration statement itself is
   independent of the choice of Frobenius lift.  The numerical profile above
   separates the later different/discriminant input from the filtration
   calculation. -/

end
end LastLib.Book03RamificationTheory.Chapter03
