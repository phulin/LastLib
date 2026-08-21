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
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : K) : Prop :=
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
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (u : K) (y₀ : L) : Prop :=
  u / Algebra.norm K y₀ ∈ chapter11UnitFiltration vK 1

/- The norm valuation formula used to begin the equation-solving procedure. -/
theorem chapter11_unramified_norm_equation_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (f : ℕ) (hunram : chapter11UnramifiedValuedExtension vK vL)
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) → vL.IsEquiv w)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1) (x : L) :
    vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x := by
  exact chapter11_unramified_comparison_norm_valuation K L vK vL f hunram hunique hdegree hfres x

/- Divisibility of the valuation is necessary for a nonzero norm equation. -/
theorem chapter11_unramified_norm_equation_valuation_necessary
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (f : ℕ) (hunram : chapter11UnramifiedValuedExtension vK vL)
    (hnorm : chapter11NormValuationFormula K L vK vL f)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1) (a : K) (x : L)
    (hx : x ≠ 0) (heq : Algebra.norm K x = a) :
    chapter11ValuationValueDivisibleBy vK f a := by
  unfold chapter11ValuationValueDivisibleBy
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp (vL.ne_top_iff.mpr hx)
  refine ⟨z, ?_⟩
  rw [← heq, hnorm x hx, ← hz]
  change (↑(f : ℤ) : WithTop ℤ) * (z : WithTop ℤ) =
    (↑((f : ℤ) * z) : WithTop ℤ)
  exact (WithTop.coe_mul (f : ℤ) z).symm

/- In a discretely valued base, the valuation condition gives the displayed
   power-of-a-uniformizer times unit decomposition. -/
theorem chapter11_unramified_norm_equation_decomposition
    (K : Type*) [Field K]
    (vK : AddValuation K (WithTop ℤ))
    (f : ℕ)
    (πK : K) (hπ : chapter11IsUniformizer vK πK) (a : K) (ha : a ≠ 0)
    (hval : chapter11ValuationValueDivisibleBy vK f a) :
    chapter11UnramifiedValueUnitDecomposition vK πK f a := by
  unfold chapter11UnramifiedValueUnitDecomposition at ⊢
  unfold chapter11ValuationValueDivisibleBy at hval
  rcases hval with ⟨r, hr⟩
  have hcast : (↑((f : ℤ) * r) : WithTop ℤ) =
      (f : WithTop ℤ) * (r : WithTop ℤ) := by
    change (↑((f : ℤ) * r) : WithTop ℤ) =
      (↑(f : ℤ) : WithTop ℤ) * (r : WithTop ℤ)
    exact WithTop.coe_mul (f : ℤ) r
  have hpow (m : ℤ) : vK (πK ^ m) = (m : WithTop ℤ) := by
    induction m using Int.induction_on with
    | zero => simp
    | succ m ih =>
        rw [zpow_add_one₀ hπ.1, AddValuation.map_mul, ih, hπ.2.1]
        simp
    | pred m ih =>
        rw [zpow_sub_one₀ hπ.1, AddValuation.map_mul, ih, AddValuation.map_inv, hπ.2.1]
        norm_cast
  refine ⟨r, a / πK ^ ((f : ℤ) * r), ?_, ?_⟩
  · rw [chapter11_unit_filtration_zero]
    apply (chapter11_mem_unit_set_iff_valuation_zero vK _).2
    rw [AddValuation.map_div, hr, hpow]
    have htop : (f : WithTop ℤ) * (r : WithTop ℤ) ≠ ⊤ := by
      rw [← hcast, ← hr]
      exact vK.ne_top_iff.mpr ha
    simp [htop]
  · field_simp [hπ.1]

/- A common uniformizer accounts for the valuation part of the norm equation. -/
theorem chapter11_unramified_common_uniformizer_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πK : K) (πL : L) (f : ℕ)
    (hcommon : chapter11CommonUniformizer vK vL πK πL)
    (hdegree : Module.finrank K L = f) (r : ℤ) :
    Algebra.norm K (πL ^ r) = πK ^ ((f : ℤ) * r) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
    (hnorm : chapter11NormValuationFormula K L vK vL f)
    [Finite (chapter11ResidueField vK)]
    [Finite (chapter11ResidueField vL)]
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL))
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L
      (chapter11ResidueField vK) (chapter11ResidueField vL) vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL) 1 N)
    (πL : L) (hcommon : chapter11CommonUniformizer vK vL πK πL)
    (a : K) (ha : a ≠ 0) :
    chapter11NormEquationSolution K L a ↔
      chapter11ValuationValueDivisibleBy vK f a := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
