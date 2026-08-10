import Mathlib
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

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

/- The image of the `n`th unit layer under the algebra norm. -/
def chapter11NormImage (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (n : ℕ) : Set K :=
  Algebra.norm K '' chapter11UnitFiltration vL n

/- The image of an ideal-power layer under the algebra trace. -/
def chapter11TraceImage (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (n : ℕ) : Set K :=
  Algebra.trace K L '' chapter11ValuationIdealPowerSet vL n

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

/- Completeness of the valuation ring in its maximal-ideal topology. -/
def chapter11ValuationComplete {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Prop :=
  IsAdicComplete (IsLocalRing.maximalIdeal (chapter11ValuationRing v))
    (chapter11ValuationRing v)

/- The residue field and residue map of a valuation ring. -/
abbrev chapter11ResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  IsLocalRing.ResidueField (chapter11ValuationRing v)

def chapter11ResidueMap {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    chapter11ValuationRing v →+* chapter11ResidueField v :=
  IsLocalRing.residue (chapter11ValuationRing v)

/- The residue-field norm image on nonzero elements. -/
def chapter11ResidueUnitNormImage (k l : Type*) [Field k] [Field l] [Algebra k l] : Set k :=
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
  ∃ z : ℤ, v x = ((f : ℤ) * z : ℤ)

/- The norm subgroup of the multiplicative group of a finite field extension. -/
def chapter11NormSubgroup (K L : Type*) [Field K] [Field L] [Algebra K L] : Subgroup Kˣ :=
  Subgroup.map (Units.map (Algebra.norm K (S := L))) ⊤

/- The valuation-coordinate times unit-coordinate subset of `Kˣ`, written in `K`. -/
def chapter11ValueUnitProductSet {K : Type*} [Field K]
    (vK : AddValuation K (WithTop ℤ)) (π : K) (f : ℕ) : Set K :=
  {x | ∃ z : ℤ, ∃ u : K, u ∈ chapter11UnitFiltration vK 0 ∧
    x = π ^ ((f : ℤ) * z) * u}

/-! ## 11.1. Continuity and the first constraints -/

/- The determinant norm is continuous in a finite-dimensional normed algebra. -/
theorem chapter11_norm_continuous
    (K L : Type*) [NormedField K] [NormedField L] [Algebra K L]
    [NormedAlgebra K L] [FiniteDimensional K L] :
    Continuous (Algebra.norm K (S := L)) := by
  sorry

/- The norm is a multiplicative homomorphism and sends `1` to `1`. -/
theorem chapter11_norm_preserves_one
    (K L : Type*) [CommRing K] [Ring L] [Algebra K L] :
    Algebra.norm K (1 : L) = 1 := by
  simp

/- A valued finite extension sends the base valuation-ring units to base units. -/
theorem chapter11_norm_maps_valuation_units
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e) :
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

/- At depth zero the residue of a norm is the `e`th power of the residue
   extension norm.  The residue maps are kept as explicit ring homomorphisms,
   since a residue-field section is not canonical in mixed characteristic. -/
theorem chapter11_norm_depth_zero_residue_formula
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l) (e : ℕ)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
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
    (hscale : chapter11ValuationScaling vK vL e) (n : ℕ) (hn : 1 ≤ n) :
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
    (hscale : chapter11ValuationScaling vK vL e) (n : ℕ) (hn : 1 ≤ n) :
    chapter11NormImage K L vL n ⊆
      chapter11UnitFiltration vK (chapter11CeilDiv n e) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
