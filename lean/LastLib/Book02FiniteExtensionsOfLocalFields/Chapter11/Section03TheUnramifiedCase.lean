import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section02LinearizingTheNorm

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators

/-! ## 11.3. The unramified case -/

/- A uniformizer is represented by a generator of the maximal ideal of the
   canonical valuation ring. -/
def chapter11IsUniformizer {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K) : Prop :=
  π ≠ 0 ∧ v π = (1 : WithTop ℤ) ∧ ∃ p : chapter11ValuationRing v,
    (p : K) = π ∧
      IsLocalRing.maximalIdeal (chapter11ValuationRing v) = Ideal.span {p}

/- The unramified valued-extension interface includes both normalization and
   completeness; residue-field separability is supplied by the residue-field
   typeclass assumptions in the theorems below. -/
def chapter11UnramifiedValuedExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ)) : Prop :=
  chapter11ValuationExtension vK vL ∧
    chapter11ValuationScaling vK vL 1 ∧
    chapter11ValuationComplete vK ∧ chapter11ValuationComplete vL

/- A common uniformizer is the same element under the base embedding. -/
def chapter11CommonUniformizer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πK : K) (πL : L) : Prop :=
  chapter11IsUniformizer vK πK ∧ chapter11IsUniformizer vL πL ∧
    πL = algebraMap K L πK

/- The residue-class condition used to describe all unit norms.  The residue
   map has domain the valuation ring, since arbitrary field elements need not
   have a residue. -/
def chapter11ResidueConditionSet
    {K k : Type*} [Field K] [Field k]
    (vK : AddValuation K (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k) (S : Set k) : Set K :=
  {x | x ∈ chapter11UnitSet vK ∧
    ∃ y : chapter11ValuationRing vK, (y : K) = x ∧ ρK y ∈ S}

/- The residue trace is the additive map on the graded layer. -/
theorem chapter11_unramified_residue_trace_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Algebra.IsSeparable k l] :
    Function.Surjective (Algebra.trace k l) := by
  exact Algebra.trace_surjective k l

/- On the `n`th graded layer the norm is the residue trace.  The coefficient
   is stated using an arbitrary integral lift `c`, avoiding a noncanonical
   Teichmüller section in mixed characteristic. -/
theorem chapter11_unramified_norm_first_layer_congruence
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [FiniteDimensional k l] [Algebra.IsSeparable k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l)
    (hdegree : Module.finrank K L = Module.finrank k l)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (πK : K) (πL : L) (hπ : chapter11CommonUniformizer vK vL πK πL)
    (n : ℕ) (hn : 1 ≤ n) (a : chapter11ValuationRing vL) :
    ∃ c : chapter11ValuationRing vK,
      ρK c = Algebra.trace k l (ρL a) ∧
        chapter11UnitCongruence vK (n + 1)
          (Algebra.norm K (1 + (a : L) * πL ^ n))
          (1 + (c : K) * πK ^ n) := by
  sorry

/- Proposition 11.1: completeness and finite separable residue extension make
   the norm onto on all positive principal-unit layers. -/
theorem proposition_11_1_unramified_principal_unit_norm_surjective
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hdegree : Module.finrank K L =
      Module.finrank (chapter11ResidueField vK) (chapter11ResidueField vL))
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL)) :
    Set.SurjOn (Algebra.norm K (S := L))
      (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1) := by
  sorry

/- The complete unit image is exactly the inverse image of the residue norm
   image. -/
theorem proposition_11_1_unramified_all_unit_norm_image
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [FiniteDimensional k l] [Algebra.IsSeparable k l]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* l)
    (hdegree : Module.finrank K L = Module.finrank k l)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1)) :
    chapter11NormImage K L vL 0 =
      chapter11ResidueConditionSet vK ρK
        (chapter11ResidueUnitNormImage k l) := by
  sorry

/- For finite residue fields, the norm is the exponent map displayed in the
   chapter and is surjective on nonzero residue classes. -/
theorem chapter11_finite_residue_norm_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l] [Finite l] :
    Function.Surjective (Algebra.norm k (S := l)) := by
  exact FiniteField.norm_surjective k l

theorem chapter11_finite_residue_norm_is_exponent_map
    (k l : Type*) [Field k] [Field l] [Algebra k l] [Finite l] (x : l) :
    algebraMap k l (Algebra.norm k x) =
      x ^ ((Nat.card l - 1) / (Nat.card k - 1)) := by
  exact FiniteField.algebraMap_norm_eq_pow

/- The valuation coordinate is the only obstruction for the full norm group
   in the finite-residue unramified case. -/
theorem chapter11_unramified_full_norm_image
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πK : K) (f : ℕ)
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    (hπ : chapter11IsUniformizer vK πK)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1)
    [Finite (chapter11ResidueField vK)]
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL)) :
    {x : K | ∃ y : L, y ≠ 0 ∧ x = Algebra.norm K y} =
      chapter11ValueUnitProductSet vK πK f := by
  sorry

/- In the same hypotheses the norm subgroup has index `f` in `Kˣ`. -/
theorem chapter11_unramified_norm_subgroup_index
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πK : K) (f : ℕ)
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    (hπ : chapter11IsUniformizer vK πK)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1)
    [Finite (chapter11ResidueField vK)]
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL)) :
    Nat.card (Kˣ ⧸ chapter11NormSubgroup K L) = f := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
