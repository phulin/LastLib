import LastLib.Book03RamificationTheory.Chapter03.Dependencies
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section08PrimeToP_RadicalExtensions
import Mathlib.FieldTheory.KummerExtension

namespace LastLib.Book03RamificationTheory.Chapter03

noncomputable section

open Polynomial
open scoped BigOperators

/-! ## 3.2. Tame Kummer extensions -/

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
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08KummerPolynomial
        ((D.u : A) * D.π) e) := by
  simpa [
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08KummerPolynomial,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08RadicalPolynomial] using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_tame_radical_polynomial_is_eisenstein
      D.π D.u e D.positive_degree D.uniformizer.symm)

theorem chapter03_tame_kummer_extension_profile
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (p e : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p]
    (D : Chapter03TameKummerData (A := A) (K := K) (L := L) p e)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hval : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hA : vK.Integers A)
    (hπK : vK (algebraMap A K D.π) = 1)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = e • vK x) :
    ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
        vK vL hval,
      ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData d q ∧
          q.degree = e ∧ q.ramificationIndex = e ∧ q.residueDegree = 1 ∧
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10TotallyRamified q := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_tame_radical_extension_profile
    p e (Fact.out : p.Prime) D.prime_to_residue_characteristic
    D.u D.π D.α D.uniformizer D.root_and_generation D.degree
    vK vL hdiscreteK hdiscreteL hval hA hπK hscale

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
  have hπ0 : D.π ≠ 0 := by
    intro hzero
    have hbot : IsLocalRing.maximalIdeal A = (⊥ : Ideal A) := by
      rw [D.uniformizer.symm, hzero]
      simp
    exact IsDiscreteValuationRing.not_a_field A hbot
  have hroot : D.α ^ e = algebraMap K L
      (algebraMap A K (D.u : A) * algebraMap A K D.π) := by
    exact D.root_and_generation.1.symm
  have hα : D.α ≠ 0 := by
    intro hzero
    have hbad : algebraMap K L
        (algebraMap A K (D.u : A) * algebraMap A K D.π) = 0 := by
      rw [← hroot, hzero, zero_pow D.positive_degree.ne']
    have hprod : algebraMap K L
        (algebraMap A K (D.u : A) * algebraMap A K D.π) ≠ 0 := by
      simp [hπ0]
    exact hprod hbad
  simpa [chapter03KummerAutomorphismRatio] using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_kummer_automorphism_ratio_is_root_of_unity
      e (algebraMap A K (D.u : A) * algebraMap A K D.π) D.α σ hα hroot)

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
  let a : K := algebraMap A K (D.u : A) * algebraMap A K D.π
  have hroot : D.α ^ e = algebraMap K L a := by
    simpa [a] using D.root_and_generation.1.symm
  have hgen : IntermediateField.adjoin K ({D.α} : Set L) =
      (⊤ : IntermediateField K L) := by
    exact IntermediateField.adjoin_eq_top_of_algebra K ({D.α} : Set L)
      D.root_and_generation.2
  have hroot' : D.α ^ (Module.finrank K L) = algebraMap K L a := by
    simpa [D.degree] using hroot
  have hK : (primitiveRoots (Module.finrank K L) K).Nonempty := by
    simpa [D.degree] using D.roots_of_unity
  have hirr' : Irreducible
      (Polynomial.X ^ (Module.finrank K L) - Polynomial.C a) :=
    irreducible_X_pow_sub_C_of_root_adjoin_eq_top hroot' hgen
  have hsplit' : IsSplittingField K L
      (Polynomial.X ^ (Module.finrank K L) - Polynomial.C a) :=
    isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hK hroot' hgen
  let : IsSplittingField K L
      (Polynomial.X ^ e - Polynomial.C a) := by
    simpa [D.degree] using hsplit'
  have hirr : Irreducible (Polynomial.X ^ e - Polynomial.C a) := by
    simpa [D.degree] using hirr'
  let : NeZero e := ⟨D.positive_degree.ne'⟩
  let κ : rootsOfUnity e K ≃* (L ≃ₐ[K] L) :=
    (autEquivRootsOfUnity D.roots_of_unity hirr L).symm
  refine ⟨κ, ?_⟩
  intro ζ
  simpa [κ, Subgroup.smul_def, Units.smul_def, Algebra.smul_def] using
    (autEquivRootsOfUnity_smul D.roots_of_unity hirr L hroot (κ ζ)).symm

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
  have hsub : σ D.α - D.α =
      algebraMap K L (((ζ : Kˣ) : K) - 1) * D.α := by
    rw [hσ]
    calc
      algebraMap K L (((ζ : Kˣ) : K)) * D.α - D.α =
          algebraMap K L (((ζ : Kˣ) : K)) * D.α - 1 * D.α := by rw [one_mul]
      _ = (algebraMap K L (((ζ : Kˣ) : K)) - 1) * D.α :=
        (sub_mul _ _ _).symm
      _ = algebraMap K L (((ζ : Kˣ) : K) - 1) * D.α := by
        rw [map_sub, map_one]
  by_cases h : ζ = 1
  · exact (hζ h).elim
  · constructor
    · exact congrArg vL hsub
    · rw [hsub, vL.map_mul, hvalue_unit, hvalue_alpha]
      simp

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
  let f : I → θ.range := fun x => ⟨θ x, ⟨x, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro y
    rcases y with ⟨y, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply hinjective
    simpa [f] using congrArg (fun z : θ.range => (z : lˣ)) hxy
  let e : I ≃ θ.range := Equiv.ofBijective f ⟨hf_injective, hf⟩
  have : Finite θ.range := Finite.of_injective e.symm e.symm.injective
  have : IsCyclic θ.range := by infer_instance
  exact (Subgroup.isCyclic_iff_exists_zpowers_eq_top θ.range).mp inferInstance

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
