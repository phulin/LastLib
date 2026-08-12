import LastLib.Book03RamificationTheory.Chapter03.Dependencies
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section08PrimeToP_RadicalExtensions
import Mathlib.FieldTheory.KummerExtension

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open Polynomial
open scoped BigOperators

/-! ## 3.2. Tame Kummer extensions -/

/- The integral Kummer polynomial in the source's unit-times-uniformizer form. -/
def chapter03TameKummerPolynomial
    {A : Type*} [CommRing A] (u : Aˣ) (π : A) (e : ℕ) : A[X] :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08RadicalPolynomial
    ((u : A) * π) e

/- The hypotheses of the tame Kummer calculation. -/
structure Chapter03TameKummerData
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p] where
  u : Aˣ
  π : A
  α : L
  positive_degree : 0 < e
  prime_to_residue_characteristic : Nat.Coprime e p
  uniformizer : Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A
  root_and_generation :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08TameRadicalPresentation
      (algebraMap A K (u : A)) (algebraMap A K π) α e
  degree : Module.finrank K L = e
  roots_of_unity : (primitiveRoots e K).Nonempty

theorem chapter03_tame_kummer_polynomial_is_eisenstein
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p]
    (D : Chapter03TameKummerData (A := A) (K := K) (L := L) p e) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt D.π
      (chapter03TameKummerPolynomial D.u D.π e) := by
  sorry

theorem chapter03_tame_kummer_extension_profile
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p]
    (D : Chapter03TameKummerData (A := A) (K := K) (L := L) p e) :
    ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
      q.degree = e ∧ q.ramificationIndex = e ∧ q.residueDegree = 1 ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified q := by
  sorry

/- The Kummer automorphism ratio used to describe the Galois action. -/
def chapter03KummerAutomorphismRatio
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (α : L) : L :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08KummerAutomorphismRatio
    σ α

theorem chapter03_tame_kummer_automorphism_ratio_is_an_e_th_root
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p]
    (D : Chapter03TameKummerData (A := A) (K := K) (L := L) p e)
    (σ : L ≃ₐ[K] L) :
    chapter03KummerAutomorphismRatio σ D.α ^ e = 1 := by
  sorry

/- The chosen radical root parametrizes the self-automorphisms. -/
theorem chapter03_tame_kummer_automorphisms_are_radical
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p]
    (D : Chapter03TameKummerData (A := A) (K := K) (L := L) p e) :
    ∃ κ : rootsOfUnity e K ≃* (L ≃ₐ[K] L),
      ∀ ζ : rootsOfUnity e K,
        κ ζ D.α = algebraMap K L ((ζ : Kˣ) : K) * D.α := by
  sorry

theorem chapter03_tame_kummer_displacement_calculation
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p]
    (D : Chapter03TameKummerData (A := A) (K := K) (L := L) p e)
    (vL : AddValuation L (WithTop ℤ))
    (σ : L ≃ₐ[K] L) (ζ : rootsOfUnity e K)
    (hζ : ζ ≠ 1)
    (hσ : σ D.α = algebraMap K L ((ζ : Kˣ) : K) * D.α)
    (hvalue_alpha : vL D.α = 1)
    (hvalue_unit : vL (algebraMap K L (((ζ : Kˣ) : K) - 1)) = 0) :
    vL (σ D.α - D.α) =
        vL (algebraMap K L (((ζ : Kˣ) : K) - 1) * D.α) ∧
      vL (σ D.α - D.α) = 1 := by
  sorry

/- A formula for a tame character once the reduction of roots is supplied. -/
def chapter03TameCharacterFormula
    {I K l : Type*} [Group I] [Field K] [Field l]
    (e : ℕ) (κ : rootsOfUnity e K ≃* I)
    (θ : I →* lˣ) (reduction : rootsOfUnity e K →* lˣ) : Prop :=
  ∀ ζ : rootsOfUnity e K, θ (κ ζ) = reduction ζ

theorem chapter03_tame_character_image_is_cyclic
    {I l : Type*} [Group I] [Finite I] [Field l]
    (θ : I →* lˣ) (hinjective : Function.Injective θ) :
    ∃ ξ : lˣ, Subgroup.zpowers ξ = θ.range := by
  sorry

theorem chapter03_totally_tame_filtration
    {G : Type*} [Group G] [Finite G]
    (F : Chapter03LowerDisplacementFiltration G) (H : Subgroup G)
    (hinside : ∀ {σ : G}, σ ∈ H → σ ≠ 1 → F.displacement σ = 1)
    (houtside : ∀ {σ : G}, σ ∉ H → F.displacement σ = 0) :
    F.lower (-1) = ⊤ ∧ F.lower 0 = H ∧ F.lower 1 = ⊥ := by
  exact ⟨F.lower_neg_one,
    (chapter03_tame_profile_of_inertia_displacement F H hinside houtside).1,
    (chapter03_tame_profile_of_inertia_displacement F H hinside houtside).2⟩

theorem chapter03_tame_kummer_lower_groups
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

/- SOURCE_WARNING (3.2): The Kummer hypotheses are coordinate data, not the
   definition of tameness.  The coordinate-free filtration conclusion is the
   preceding `chapter03_totally_tame_filtration`; after an unramified base
   change a totally tamely ramified Galois stage may be put in this form. -/

end
end LastLib.Book03RamificationTheory.Chapter03
