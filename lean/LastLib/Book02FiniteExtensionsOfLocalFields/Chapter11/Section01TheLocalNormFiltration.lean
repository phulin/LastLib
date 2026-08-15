import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section07NormsAndIdeals
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section04AbsoluteValueNormalizations
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section05ResidueFieldShadows
import Mathlib.Algebra.Order.Floor.Div

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators

/-! # Book 2, Chapter 11, §11.1

The common interfaces in this file use Mathlib's additive valuations.  The
valuation ring is therefore the canonical `ValuationSubring`; the filtration
is recorded as subsets of the field so that norm images are ordinary set
images.  `U^0` is the unit group of the valuation ring, while positive levels
are written as `1 + m^n`.
-/

/- The valuation ring attached to an additive valuation. -/
abbrev chapter11ValuationRing {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  v.toValuation.valuationSubring

/- The underlying set of units of the valuation ring, viewed in the field. -/
def chapter11UnitSet {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Set K :=
  {x | ∃ u : v.toValuation.valuationSubring.unitGroup,
    x = ((u : Kˣ) : K)}

/- The elements of the valuation ring lying in the `n`th power of its maximal ideal. -/
def chapter11ValuationIdealPowerSet {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Set K :=
  {x | ∃ y : chapter11ValuationRing v,
    y ∈ (IsLocalRing.maximalIdeal (chapter11ValuationRing v)) ^ n ∧
      x = (y : K)}

/- The positive principal-unit layer `1 + m^n`. -/
def chapter11PrincipalUnitSet {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Set K :=
  {x | ∃ y : chapter11ValuationRing v,
    y ∈ (IsLocalRing.maximalIdeal (chapter11ValuationRing v)) ^ n ∧
      x = 1 + (y : K)}

/- The unit filtration used throughout this chapter. -/
def chapter11UnitFiltration {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Set K :=
  if n = 0 then chapter11UnitSet v else chapter11PrincipalUnitSet v n

/- The two endpoint descriptions are useful when moving between set-level
   norm statements and the valuation-ring unit subgroups. -/
theorem chapter11_unit_filtration_zero {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    chapter11UnitFiltration v 0 = chapter11UnitSet v := by
  simp [chapter11UnitFiltration]

theorem chapter11_unit_filtration_succ {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) :
    chapter11UnitFiltration v (n + 1) = chapter11PrincipalUnitSet v (n + 1) := by
  simp [chapter11UnitFiltration]

/- Membership interfaces keep coercions from the valuation ring visible. -/
theorem chapter11_mem_unit_set_iff {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : K) :
    x ∈ chapter11UnitSet v ↔
      ∃ u : v.toValuation.valuationSubring.unitGroup,
        x = ((u : Kˣ) : K) := Iff.rfl

theorem chapter11_mem_principal_unit_set_iff {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter11PrincipalUnitSet v n ↔
      ∃ y : chapter11ValuationRing v,
        y ∈ (IsLocalRing.maximalIdeal (chapter11ValuationRing v)) ^ n ∧
          x = 1 + (y : K) := Iff.rfl

theorem chapter11_mem_valuation_ideal_power_set_iff {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter11ValuationIdealPowerSet v n ↔
      ∃ y : chapter11ValuationRing v,
        y ∈ (IsLocalRing.maximalIdeal (chapter11ValuationRing v)) ^ n ∧
          x = (y : K) := Iff.rfl

theorem chapter11_mem_unit_filtration_iff {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter11UnitFiltration v n ↔
      (n = 0 ∧ x ∈ chapter11UnitSet v) ∨
        (n ≠ 0 ∧ x ∈ chapter11PrincipalUnitSet v n) := by
  by_cases hn : n = 0
  · simp [chapter11UnitFiltration, hn]
  · simp [chapter11UnitFiltration, hn]

/- A unit in the valuation ring is exactly a field element of value zero. -/
theorem chapter11_mem_unit_set_iff_valuation_zero {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : K) :
    x ∈ chapter11UnitSet v ↔ v x = 0 := by
  sorry

/- The image of the `n`th unit layer under the algebra norm. -/
def chapter11NormImage (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vL : AddValuation L (WithTop ℤ)) (n : ℕ) : Set K :=
  Algebra.norm K '' chapter11UnitFiltration vL n

/- The image of an ideal-power layer under the algebra trace. -/
def chapter11TraceImage (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vL : AddValuation L (WithTop ℤ)) (n : ℕ) : Set K :=
  Algebra.trace K L '' chapter11ValuationIdealPowerSet vL n

theorem chapter11_mem_norm_image_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (vL : AddValuation L (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter11NormImage K L vL n ↔
      ∃ y : L, y ∈ chapter11UnitFiltration vL n ∧ Algebra.norm K y = x := Iff.rfl

theorem chapter11_mem_trace_image_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (vL : AddValuation L (WithTop ℤ)) (n : ℕ) (x : K) :
    x ∈ chapter11TraceImage K L vL n ↔
      ∃ y : L, y ∈ chapter11ValuationIdealPowerSet vL n ∧ Algebra.trace K L y = x := Iff.rfl

/- Natural ceiling division, with the standard natural-number convention at zero. -/
def chapter11CeilDiv (n e : ℕ) : ℕ := n ⌈/⌉ e

/- Equivalence of the base valuation with the restriction of the extension valuation. -/
def chapter11ValuationExtension {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ)) : Prop :=
  vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)

/- Exact normalization data: restriction of `vL` scales the normalized base value by `e`. -/
def chapter11ValuationScaling {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) : Prop :=
  ∀ x : K, vL (algebraMap K L x) = (e : WithTop ℤ) * vK x

/- A reusable local interface for the one-branch valuation of a field norm.
   Earlier chapters provide this under explicit rank-one, uniqueness, and
   defectless hypotheses; Chapter 11 keeps the formula available as data so
   its filtration results do not silently assume those hypotheses. -/
def chapter11NormValuationFormula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (f : ℕ) : Prop :=
  ∀ x : L, x ≠ 0 →
    vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x

theorem chapter11_valuation_extension_iff {K L : Type*} [Field K] [Field L]
    [Algebra K L] (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) :
    chapter11ValuationExtension vK vL ↔
      vK.IsEquiv (AddValuation.comap (algebraMap K L) vL) := Iff.rfl

theorem chapter11_valuation_scaling_iff {K L : Type*} [Field K] [Field L]
    [Algebra K L] (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) :
    chapter11ValuationScaling vK vL e ↔
      ∀ x : K, vL (algebraMap K L x) = (e : WithTop ℤ) * vK x := Iff.rfl

/- The normalized complete discrete local-field hypothesis.  Chapter 1 already
   packages rank-one discreteness and adic completeness for additive
   valuations, so reuse that canonical interface here. -/
def chapter11ValuationComplete {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01CompleteAdditiveValuation v

/- The residue field and residue map of a valuation ring. -/
abbrev chapter11ResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  IsLocalRing.ResidueField (chapter11ValuationRing v)

def chapter11ResidueMap {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    chapter11ValuationRing v →+* chapter11ResidueField v :=
  IsLocalRing.residue (chapter11ValuationRing v)

/- The residue maps used in norm and trace formulas are actual residue maps,
   and the base-field embedding descends to the displayed residue extension.
   The compatibility is stated with an explicit integral witness so that no
   noncanonical identification of residue fields is smuggled in. -/
def chapter11ResidueReductionCompatible
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04ResidueMap
      (chapter11ValuationRing vK) k
      (IsLocalRing.maximalIdeal (chapter11ValuationRing vK)) ρK ∧
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04ResidueMap
      (chapter11ValuationRing vL) l
      (IsLocalRing.maximalIdeal (chapter11ValuationRing vL)) ρL ∧
    ∀ x : chapter11ValuationRing vK, ∃ y : chapter11ValuationRing vL,
      (y : L) = algebraMap K L (x : K) ∧
        ρL y = algebraMap k l (ρK x)

theorem chapter11_residue_reduction_compatible_base
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04ResidueMap
        (chapter11ValuationRing vK) k
        (IsLocalRing.maximalIdeal (chapter11ValuationRing vK)) ρK := by
  exact hred.1

theorem chapter11_residue_reduction_compatible_extension
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04ResidueMap
        (chapter11ValuationRing vL) l
        (IsLocalRing.maximalIdeal (chapter11ValuationRing vL)) ρL := by
  exact hred.2.1

theorem chapter11_residue_reduction_compatible_map
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (x : chapter11ValuationRing vK) :
    ∃ y : chapter11ValuationRing vL,
      (y : L) = algebraMap K L (x : K) ∧
        ρL y = algebraMap k l (ρK x) := by
  exact hred.2.2 x

/- The residue-field norm image on nonzero elements. -/
def chapter11ResidueUnitNormImage (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] : Set k :=
  Set.range (fun u : lˣ => Algebra.norm k (u : l))

/- The residue-field `e`th-power image on nonzero elements. -/
def chapter11ResidueUnitPowerImage (k : Type*) [Field k] (e : ℕ) : Set k :=
  Set.range (fun u : kˣ => ((u : k) ^ e))

/- Congruence of field elements modulo a positive unit layer. -/
def chapter11UnitCongruence {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (x y : K) : Prop :=
  x * y⁻¹ ∈ chapter11UnitFiltration v n

/- Divisibility of a finite valuation value by a natural ramification degree. -/
def chapter11ValuationValueDivisibleBy {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (f : ℕ) (x : K) : Prop :=
  ∃ z : ℤ, v x = (((f : ℤ) * z : ℤ) : WithTop ℤ)

/- The norm subgroup of the multiplicative group of a finite field extension. -/
def chapter11NormSubgroup (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  Subgroup.map (Units.map (Algebra.norm K (S := L))) ⊤

theorem chapter11_mem_norm_subgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (u : Kˣ) :
    u ∈ chapter11NormSubgroup K L ↔
      ∃ x : Lˣ, Units.map (Algebra.norm K (S := L)) x = u := by
  sorry

/- The valuation-coordinate times unit-coordinate subset of `Kˣ`, written in `K`. -/
def chapter11ValueUnitProductSet {K : Type*} [Field K]
    (vK : AddValuation K (WithTop ℤ)) (π : K) (f : ℕ) : Set K :=
  {x | ∃ z : ℤ, ∃ u : K, u ∈ chapter11UnitFiltration vK 0 ∧
    x = π ^ ((f : ℤ) * z) * u}

theorem chapter11_mem_value_unit_product_set_iff {K : Type*} [Field K]
    (vK : AddValuation K (WithTop ℤ)) (π : K) (f : ℕ) (x : K) :
    x ∈ chapter11ValueUnitProductSet vK π f ↔
      ∃ z : ℤ, ∃ u : K, u ∈ chapter11UnitFiltration vK 0 ∧
        x = π ^ ((f : ℤ) * z) * u := Iff.rfl

/-! ## 11.1. Continuity and the first constraints -/

/- The determinant norm is continuous in a finite-dimensional normed algebra. -/
theorem chapter11_norm_continuous
    (K L : Type*) [NormedField K] [NormedField L]
    [NormedAlgebra K L] [FiniteDimensional K L] :
    Continuous (Algebra.norm K (S := L)) := by
  sorry

/- The norm is a multiplicative homomorphism and sends `1` to `1`. -/
theorem chapter11_norm_preserves_one
    (K L : Type*) [CommRing K] [Ring L] [Algebra K L] :
    Algebra.norm K (1 : L) = 1 := by
  sorry

/- A valued finite extension sends the base valuation-ring units to base units. -/
-- SOURCE_ISSUE: The hypotheses only identify the chosen valuation after
-- restriction; they do not impose uniqueness of the extension or any
-- norm-valuation formula.  The corrected interface takes the full one-branch
-- norm valuation formula as an explicit, reusable local dependency.
theorem chapter11_norm_maps_valuation_units
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e f : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (hnorm : chapter11NormValuationFormula K L vK vL f) :
    chapter11NormImage K L vL 0 ⊆ chapter11UnitFiltration vK 0 := by
  sorry

/- In a normal closure, the finite separable norm is the product of conjugates. -/
theorem chapter11_norm_eq_product_of_conjugates
    (K L E : Type*) [Field K] [Field L] [Field E] [Algebra K L]
    [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsAlgClosed E] (x : L) :
    algebraMap K E (Algebra.norm K x) =
      ∏ σ : L →ₐ[K] E, σ x := by
  sorry

/- A unit-level lift of the field norm and its residue compatibility.  These
   are the explicit integral-extension data needed to apply the residue norm
   formula without identifying quotient representatives definitionally. -/
def chapter11NormUnitLiftCompatibility
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ) : Prop :=
  ∀ u : (chapter11ValuationRing vL)ˣ,
    ((N u : chapter11ValuationRing vK) : K) =
      Algebra.norm K ((u : chapter11ValuationRing vL) : L)

def chapter11NormResidueCompatibility
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l) (e : ℕ)
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ) : Prop :=
  ∀ u : (chapter11ValuationRing vL)ˣ,
    ρK (N u : chapter11ValuationRing vK) =
      Algebra.norm k (ρL (u : chapter11ValuationRing vL)) ^ e

/- At depth zero the residue of a norm is the `e`th power of the residue
   extension norm.  The residue maps are kept as explicit ring homomorphisms,
   since a residue-field section is not canonical in mixed characteristic. -/
-- SOURCE_ISSUE: `chapter11ResidueReductionCompatible` only records the
-- residue maps on embedded base valuation-ring elements; it supplies no
-- commutation law between the norm and the displayed residue maps.  A
-- proof-ready use must add the unit-level norm lift and its norm-reduction
-- compatibility; those are explicit in the corrected declaration below.
theorem chapter11_norm_depth_zero_residue_formula
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l) (e : ℕ)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hdegree : Module.finrank K L = e * Module.finrank k l)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L k l vK vL ρK ρL e N)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (u : chapter11ValuationRing vL) (hu : IsUnit u) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.norm K (u : L) ∧
        ρK y = Algebra.norm k (ρL u) ^ e := by
  sorry

/- The coarse norm bound along the unit filtration. -/
theorem chapter11_norm_principal_unit_depth_bound
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL) (n : ℕ) (hn : 1 ≤ n) :
    chapter11NormImage K L vL n ⊆
      chapter11UnitFiltration vK (chapter11CeilDiv n e) := by
  sorry

/- Purely inseparable extensions obey the same coarse depth bound; their norm
   computation reduces to powers rather than a product over distinct
   embeddings. -/
theorem chapter11_norm_principal_unit_depth_bound_purely_inseparable
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL) (n : ℕ) (hn : 1 ≤ n) :
    chapter11NormImage K L vL n ⊆
      chapter11UnitFiltration vK (chapter11CeilDiv n e) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
