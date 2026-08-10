import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section06AWorkedComparison

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

/-! ## 11.7. Explicit norm equations in an unramified extension

The statements in this file separate the valuation coordinate, the residue
unit lift, and the principal-unit correction.  This makes the constructive
proof of the unramified norm equation available as an interface without
choosing Teichmuller representatives.
-/

/- A nonzero element is a solution of the multiplicative norm equation. -/
def chapter11NormEquationSolution
    (K L : Type*) [Field K] [Field L] [Algebra K L] (a : K) : Prop :=
  ∃ x : L, x ≠ 0 ∧ Algebra.norm K x = a

/- The valuation-unit decomposition used in the unramified calculation. -/
def chapter11UnramifiedValueUnitDecomposition
    {K : Type*} [Field K] (vK : AddValuation K (WithTop ℤ))
    (πK : K) (f : ℕ) (a : K) : Prop :=
  ∃ r : ℤ, ∃ u : K,
    u ∈ chapter11UnitFiltration vK 0 ∧
      a = πK ^ ((f : ℤ) * r) * u

/- The usable lift interface below keeps a valuation-ring witness explicit:
   arbitrary residue-map surjectivity does not by itself preserve units. -/
def chapter11PrincipalUnitCorrection
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (u : K) (y₀ : L) : Prop :=
  u / Algebra.norm K y₀ ∈ chapter11UnitFiltration vK 1

/- The norm valuation formula used to begin the equation-solving procedure. -/
theorem chapter11_unramified_norm_equation_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (f : ℕ) (hunram : chapter11UnramifiedValuedExtension vK vL)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1) (x : L) :
    vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x := by
  sorry

/- Divisibility of the valuation is necessary for a nonzero norm equation. -/
theorem chapter11_unramified_norm_equation_valuation_necessary
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (f : ℕ) (hunram : chapter11UnramifiedValuedExtension vK vL)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1) (a : K) (x : L)
    (hx : x ≠ 0) (heq : Algebra.norm K x = a) :
    chapter11ValuationValueDivisibleBy vK f a := by
  unfold chapter11ValuationValueDivisibleBy
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp (vL.ne_top_iff.mpr hx)
  refine ⟨z, ?_⟩
  rw [← heq, chapter11_unramified_norm_equation_valuation_formula
    K L vK vL f hunram hdegree hfres x, ← hz]
  simp [Int.cast_mul]

/- In a discretely valued base, the valuation condition gives the displayed
   power-of-a-uniformizer times unit decomposition. -/
theorem chapter11_unramified_norm_equation_decomposition
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (f : ℕ) (hunram : chapter11UnramifiedValuedExtension vK vL)
    (πK : K) (hπ : chapter11IsUniformizer vK πK) (a : K) (ha : a ≠ 0)
    (hval : chapter11ValuationValueDivisibleBy vK f a) :
    chapter11UnramifiedValueUnitDecomposition vK πK f a := by
  sorry

/- A common uniformizer accounts for the valuation part of the norm equation. -/
theorem chapter11_unramified_common_uniformizer_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πK : K) (πL : L) (f : ℕ)
    (hcommon : chapter11CommonUniformizer vK vL πK πL)
    (hdegree : Module.finrank K L = f) (r : ℤ) :
    Algebra.norm K (πL ^ r) = πK ^ ((f : ℤ) * r) := by
  rw [Algebra.norm_zpow, hcommon.2.2, Algebra.norm_algebraMap, hdegree]
  simp [zpow_mul]

/- The residue-field step produces a unit lift before the principal-unit
   correction is applied.  The unit-lift assumption is stated explicitly
   because surjectivity of a ring residue map alone does not preserve units. -/
theorem chapter11_unramified_residue_unit_lift
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l)
    (hresunit : ∀ z : kˣ, ∃ y : lˣ,
      Algebra.norm k (y : l) = (z : k))
    (hunitlift : ∀ y : lˣ, ∃ y₀ : chapter11ValuationRing vL,
      IsUnit y₀ ∧ ρL y₀ = (y : l))
    (hbaseunit : ∀ u : chapter11ValuationRing vK, IsUnit u →
      ∃ z : kˣ, (z : k) = ρK u)
    (u : chapter11ValuationRing vK) (hu : IsUnit u) :
    ∃ y : lˣ, Algebra.norm k (y : l) = ρK u ∧
      ∃ y₀ : chapter11ValuationRing vL,
        IsUnit y₀ ∧ ρL y₀ = (y : l) := by
  obtain ⟨z, hz⟩ := hbaseunit u hu
  obtain ⟨y, hy⟩ := hresunit z
  obtain ⟨y₀, hy₀, hy₀ρ⟩ := hunitlift y
  refine ⟨y, hy.trans hz, y₀, hy₀, hy₀ρ⟩

/- Proposition 11.1 supplies the correction whose norm is the residual unit
   error. -/
theorem chapter11_unramified_principal_unit_correction
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1))
    (u : K) (y₀ : L) (herror : chapter11PrincipalUnitCorrection K L vK u y₀) :
    ∃ y₁ : L,
      y₁ ∈ chapter11UnitFiltration vL 1 ∧
        Algebra.norm K y₁ = u / Algebra.norm K y₀ := by
  exact hprincipal herror

/- Multiplying the residue lift and the principal correction solves the unit
   equation, and multiplying by the uniformizer power solves the original one. -/
theorem chapter11_unramified_norm_equation_from_lifting
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πK : K) (πL : L) (f : ℕ) (a : K)
    (hdecomp : chapter11UnramifiedValueUnitDecomposition vK πK f a)
    (hcommon : chapter11CommonUniformizer vK vL πK πL)
    (hdegree : Module.finrank K L = f)
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1))
    (hunitlift : ∀ u : K, u ∈ chapter11UnitFiltration vK 0 →
      ∃ y₀ : L,
        y₀ ∈ chapter11UnitFiltration vL 0 ∧
          chapter11PrincipalUnitCorrection K L vK u y₀) :
    chapter11NormEquationSolution K L a := by
  rcases hdecomp with ⟨r, u, hu, ha⟩
  rcases hunitlift u hu with ⟨y₀, hy₀, herror⟩
  rcases chapter11_unramified_principal_unit_correction
      K L vK vL hprincipal u y₀ herror with ⟨y₁, hy₁, hnorm₁⟩
  have hu0 : u ≠ 0 := by
    have hu' := hu
    simp only [chapter11UnitFiltration, if_pos rfl] at hu'
    rcases hu' with ⟨u', hu'⟩
    rw [hu']
    exact Units.ne_zero _
  have hy₀0 : y₀ ≠ 0 := by
    have hy₀' := hy₀
    simp only [chapter11UnitFiltration, if_pos rfl] at hy₀'
    rcases hy₀' with ⟨y₀', hy₀'⟩
    rw [hy₀']
    exact Units.ne_zero _
  have hnorm₀ : Algebra.norm K y₀ ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hy₀0
  have hy₁0 : y₁ ≠ 0 := by
    apply Algebra.norm_ne_zero_iff.mp
    rw [hnorm₁]
    exact div_ne_zero hu0 hnorm₀
  refine ⟨πL ^ r * y₀ * y₁, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (zpow_ne_zero r hcommon.2.1.1) hy₀0) hy₁0
  · calc
      Algebra.norm K (πL ^ r * y₀ * y₁) =
          Algebra.norm K (πL ^ r) * Algebra.norm K y₀ * Algebra.norm K y₁ := by
        rw [map_mul, map_mul]
      _ = πK ^ ((f : ℤ) * r) *
          (Algebra.norm K y₀ * (u / Algebra.norm K y₀)) := by
        rw [chapter11_unramified_common_uniformizer_norm
          K L vK vL πK πL f hcommon hdegree r, hnorm₁]
      _ = πK ^ ((f : ℤ) * r) * u := by
        field_simp
      _ = a := ha.symm

/- Finite residue fields make the valuation divisibility condition sufficient,
   while separability and completeness provide the principal-unit correction. -/
theorem chapter11_unramified_norm_equation_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πK : K) (f : ℕ) (hunram : chapter11UnramifiedValuedExtension vK vL)
    (hπ : chapter11IsUniformizer vK πK)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1)
    [Finite (chapter11ResidueField vK)]
    [Finite (chapter11ResidueField vL)]
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL))
    (πL : L) (hcommon : chapter11CommonUniformizer vK vL πK πL)
    (a : K) (ha : a ≠ 0) :
    chapter11NormEquationSolution K L a ↔
      chapter11ValuationValueDivisibleBy vK f a := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
