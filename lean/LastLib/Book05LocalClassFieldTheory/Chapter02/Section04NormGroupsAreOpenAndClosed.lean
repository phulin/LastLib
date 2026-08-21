import LastLib.Book05LocalClassFieldTheory.Chapter02.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter02

noncomputable section

open Function Ideal IsLocalRing
open Filter Topology
open scoped BigOperators Pointwise Polynomial Topology WithTop

/-! ## 2.4. Norm groups are open and closed -/

theorem chapter02_norm_continuous
    (K L : Type*) [NormedField K] [NormedField L]
    [NormedAlgebra K L] [FiniteDimensional K L] :
    Continuous (Algebra.norm K (S := L)) := by
  sorry

theorem chapter02_norm_unit_image_compact_closed
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (d : Chapter02NormUnitMapData K L vK vL)
    [TopologicalSpace (Chapter02UnitGroup vL)]
    [TopologicalSpace (Chapter02UnitGroup vK)]
    [T2Space (Chapter02UnitGroup vK)]
    [TopologicalSpace Kˣ] [T2Space Kˣ]
    (hcompact : IsCompact (Set.univ : Set (Chapter02UnitGroup vL)))
    (hcontinuous : Continuous d.map)
    (hcontinuous_inclusion : Continuous (chapter02UnitInclusion vK)) :
    IsCompact (chapter02NormUnitFieldImage K L vK vL d : Set Kˣ) ∧
      IsClosed (chapter02NormUnitFieldImage K L vK vL d : Set Kˣ) := by
  sorry

theorem chapter02_trace_one_element_exists
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (hseparable : Algebra.IsSeparable K L) :
    ∃ b : L, Algebra.trace K L b = 1 := by
  sorry

theorem chapter02_integral_trace_image_contains_deep_ideal
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvaluation_extension :
      vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hcompleteK : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter02ValuationRing vK))
      (Chapter02ValuationRing vK))
    (hcompleteL : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter02ValuationRing vL))
      (Chapter02ValuationRing vL))
    (hDVRK : IsDiscreteValuationRing (Chapter02ValuationRing vK))
    (hDVRL : IsDiscreteValuationRing (Chapter02ValuationRing vL)) :
    ∃ c : ℕ, 1 ≤ c ∧
      chapter02ValuationIdealPowerSet vK c ⊆
        chapter02TraceImage K L vL 0 := by
  sorry

theorem chapter02_norm_one_add_polynomial_exists
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (b : L)
    (hb : Algebra.trace K L b = 1) :
    ∃ F : K[X],
      F.eval 0 = 0 ∧ F.coeff 1 = 1 ∧
        ∀ t : K, F.eval t = chapter02NormOneAddFunction K L b t := by
  sorry

def Chapter02NormContractionCoefficientBound
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (F : K[X]) (c : ℕ) : Prop :=
  F.coeff 1 = 1 ∧
    ∀ i : ℕ, 2 ≤ i →
      v ((F - Polynomial.X).coeff i) +
          ((i - 1 : ℕ) : WithTop ℤ) * (c : WithTop ℤ) ≥ 1

theorem chapter02_deep_norm_contraction_bound_exists
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (b : L)
    (F : K[X])
    (htrace : Algebra.trace K L b = 1)
    (hF : ∀ t : K, F.eval t = chapter02NormOneAddFunction K L b t)
    (hlocalK : Chapter02LocalField vK)
    (hvaluation_extension :
      vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hbounded : ∃ c : ℕ, 1 ≤ c ∧ ∀ x : K,
      vK x ≥ (c : WithTop ℤ) →
        vL (algebraMap K L x * b) ≥ 1) :
    ∃ c : ℕ, 1 ≤ c ∧
      (∀ x : K, vK x ≥ (c : WithTop ℤ) →
        vL (algebraMap K L x * b) ≥ 1) ∧
      Chapter02NormContractionCoefficientBound vK F c := by
  sorry

theorem chapter02_norm_one_add_is_strict_contraction
    (K : Type*) [Field K]
    (vK : AddValuation K (WithTop ℤ)) (F : K[X]) (c : ℕ)
    (hbound : Chapter02NormContractionCoefficientBound vK F c)
    {t t' : K}
    (ht : vK t ≥ (c : WithTop ℤ))
    (ht' : vK t' ≥ (c : WithTop ℤ)) :
    vK ((F.eval t - t) - (F.eval t' - t')) ≥
      vK (t - t') + 1 := by
  sorry

def chapter02ValuationBall {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (c : ℕ) : Set K :=
  {x | v x ≥ (c : WithTop ℤ)}

theorem chapter02_norm_one_add_maps_deep_ball_onto
    (K : Type*) [Field K]
    (vK : AddValuation K (WithTop ℤ)) (F : K[X]) (c : ℕ)
    (hbound : Chapter02NormContractionCoefficientBound vK F c)
    (hzero : F.eval 0 = 0)
    (hcomplete :
      IsAdicComplete
        (IsLocalRing.maximalIdeal (Chapter02ValuationRing vK))
        (Chapter02ValuationRing vK))
    (hDVR : IsDiscreteValuationRing (Chapter02ValuationRing vK)) :
    Set.SurjOn F.eval (chapter02ValuationBall vK c)
      (chapter02ValuationBall vK c) := by
  sorry

theorem chapter02_complete_ball_fixed_point_of_norm_correction
    (K : Type*) [Field K]
    (vK : AddValuation K (WithTop ℤ)) (F : K[X]) (c : ℕ)
    (hbound : Chapter02NormContractionCoefficientBound vK F c)
    (hzero : F.eval 0 = 0)
    (hcomplete :
      IsAdicComplete
        (IsLocalRing.maximalIdeal (Chapter02ValuationRing vK))
        (Chapter02ValuationRing vK))
    (hDVR : IsDiscreteValuationRing (Chapter02ValuationRing vK)) :
    ∀ s ∈ chapter02ValuationBall vK c, ∃! t,
      t ∈ chapter02ValuationBall vK c ∧ F.eval t = s := by
  sorry

theorem proposition_2_2_deep_principal_units_are_norms
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (d : Chapter02NormUnitMapData K L vK vL)
    (hvaluation_extension :
      vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hcompleteK :
      IsAdicComplete
        (IsLocalRing.maximalIdeal (Chapter02ValuationRing vK))
        (Chapter02ValuationRing vK))
    (hcompleteL :
      IsAdicComplete
        (IsLocalRing.maximalIdeal (Chapter02ValuationRing vL))
        (Chapter02ValuationRing vL))
    (hDVRK : IsDiscreteValuationRing (Chapter02ValuationRing vK))
    (hDVRL : IsDiscreteValuationRing (Chapter02ValuationRing vL)) :
    ∃ c : ℕ, 1 ≤ c ∧
      chapter02FieldUnitFiltration vK c ≤
        chapter02NormPrincipalUnitFieldImage K L vK vL d := by
  sorry

theorem chapter02_norm_subgroup_open_of_deep_units
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [TopologicalSpace Kˣ]
    [IsTopologicalGroup Kˣ]
    (hbasis : Chapter02FieldUnitFiltrationNeighborhoodBasis vK)
    (hdeep : ∃ c : ℕ,
      chapter02FieldUnitFiltration vK c ≤ chapter02NormSubgroup K L) :
    IsOpen (chapter02NormSubgroup K L : Set Kˣ) := by
  sorry

structure Chapter02NormTranslateDecomposition
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (N U : Subgroup Kˣ) (π : Kˣ) where
  f : ℕ
  f_pos : 0 < f
  valuation : Kˣ →* Multiplicative ℤ
  valuation_surjective : Function.Surjective valuation
  valuation_uniformizer : valuation π = Multiplicative.ofAdd 1
  valuation_continuous : Continuous valuation
  units_eq_kernel : U = MonoidHom.ker valuation
  membership_by_valuation : ∀ x : Kˣ,
    x ∈ N ↔ ∃ z : ℤ,
      valuation x = Multiplicative.ofAdd ((f : ℤ) * z)
  membership_by_translate : ∀ x : Kˣ,
    x ∈ N ↔ ∃ z : ℤ, ∃ u : U,
      x = π ^ ((f : ℤ) * z) * (u : Kˣ)

theorem chapter02_norm_subgroup_closed_of_translate_decomposition
    {K : Type*} [Field K] [TopologicalSpace Kˣ] [T2Space Kˣ]
    (N : Subgroup Kˣ) (U : Subgroup Kˣ) (π : Kˣ)
    (hcompact : IsCompact (U : Set Kˣ))
    (hdecomp : Chapter02NormTranslateDecomposition N U π) :
    IsClosed (N : Set Kˣ) := by
  sorry

theorem chapter02_norm_subgroup_is_open_closed_and_finite_index
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ] [T2Space Kˣ]
    (hbasis : Chapter02FieldUnitFiltrationNeighborhoodBasis vK)
    (d : Chapter02NormUnitMapData K L vK vL)
    (hdeep : ∃ c : ℕ, chapter02FieldUnitFiltration vK c ≤
      chapter02NormPrincipalUnitFieldImage K L vK vL d)
    (himage : chapter02NormPrincipalUnitFieldImage K L vK vL d ≤
      chapter02NormSubgroup K L)
    (hcompact : IsCompact
      (chapter02FieldUnitFiltration vK 0 : Set Kˣ))
    (π : Kˣ)
    (htranslate : Chapter02NormTranslateDecomposition
      (chapter02NormSubgroup K L)
      (chapter02FieldUnitFiltration vK 0) π) :
    IsOpen (chapter02NormSubgroup K L : Set Kˣ) ∧
      IsClosed (chapter02NormSubgroup K L : Set Kˣ) ∧
      Finite (Kˣ ⧸ chapter02NormSubgroup K L) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the purely inseparable norm is represented by the
   usual power after embedding the result back into the extension field. -/
theorem chapter02_purely_inseparable_norm_power_form
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L] :
    ∀ x : L,
      algebraMap K L (Algebra.norm K x) =
        x ^ Module.finrank K L := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter02
