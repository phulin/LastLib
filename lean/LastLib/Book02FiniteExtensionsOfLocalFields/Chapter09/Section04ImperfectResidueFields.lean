import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section03CleanDecomposition
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import Mathlib.RingTheory.LaurentSeries

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09

open scoped BigOperators Polynomial LaurentSeries
open Ideal IsLocalRing Polynomial

noncomputable section

/-! ## Book 2, Chapter 9.4: the imperfect-residue-field obstruction -/

/-- Mathlib's formal Laurent-series model for the notation `k((t))` used in
the counterexample. -/
abbrev chapter09LaurentSeries (k : Type*) [Field k] : Type _ := LaurentSeries k

/-- The concrete coefficientwise tower behind the notation
`k((t)) ⊂ l((t))`.  Keeping the coefficient formula explicit prevents the
counterexample from degenerating into unrelated residue-field data. -/
structure Chapter09LaurentSeriesTower
    (k l : Type*) [Field k] [Field l] [Algebra k l] where
  map : chapter09LaurentSeries k →+* chapter09LaurentSeries l
  map_coeff : ∀ x : chapter09LaurentSeries k, ∀ n : ℤ,
    (map x).coeff n = algebraMap k l (x.coeff n)
  map_injective : Function.Injective map
  /-- The coefficientwise embedding is also the algebra map of the local
  Laurent-series extension. -/
  algebra : Algebra (chapter09LaurentSeries k) (chapter09LaurentSeries l)
  algebra_map_eq_map :
    letI : Algebra (chapter09LaurentSeries k) (chapter09LaurentSeries l) := algebra
    (algebraMap (chapter09LaurentSeries k) (chapter09LaurentSeries l) :
      chapter09LaurentSeries k →+* chapter09LaurentSeries l) = map

/- The valuation profile ties the displayed `e` and `f` to the actual
coefficientwise Laurent-series field extension rather than leaving them as
unrelated labels. -/
def chapter09LaurentSeriesLocalProfile
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Module.Finite k l] (tower : Chapter09LaurentSeriesTower k l)
    (e f : ℕ) : Prop :=
  letI : Algebra (chapter09LaurentSeries k) (chapter09LaurentSeries l) :=
    tower.algebra
  ∃ (vK : AddValuation (chapter09LaurentSeries k) (WithTop ℤ))
    (vL : AddValuation (chapter09LaurentSeries l) (WithTop ℤ)),
    ∃ (hExt : vK.toValuation.HasExtension vL.toValuation),
      ∃ (hdiscK : Valuation.IsRankOneDiscrete vK.toValuation)
        (hdiscL : Valuation.IsRankOneDiscrete vL.toValuation),
        ∃ (_hcompleteK : IsAdicComplete
          (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
          vK.toValuation.valuationSubring),
          ∃ (_hcompleteL : IsAdicComplete
            (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring)
            vL.toValuation.valuationSubring),
            ∃ (hfinite : FiniteDimensional
              (chapter09LaurentSeries k) (chapter09LaurentSeries l)),
              letI : vK.toValuation.HasExtension vL.toValuation := hExt
              letI : Valuation.IsRankOneDiscrete vK.toValuation := hdiscK
              letI : Valuation.IsRankOneDiscrete vL.toValuation := hdiscL
              letI : FiniteDimensional
                  (chapter09LaurentSeries k) (chapter09LaurentSeries l) := hfinite
              ∃ d : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Chapter03FiniteLocalExtensionData
                (chapter09LaurentSeries k) (chapter09LaurentSeries l) _
                vK.toValuation vL.toValuation,
                d.e = e ∧ d.f = f

/-- The coefficientwise map supplies the concrete Laurent-series tower used
in the counterexample. -/
theorem chapter09_laurent_series_tower_exists
    (k l : Type*) [Field k] [Field l] [Algebra k l] :
    Nonempty (Chapter09LaurentSeriesTower k l) := by sorry

/-- Data for the example
`k((t)) ⊂ k(a^(1/p))((t))`.  The fields `ramification_index` and
`residue_degree` expose the two numerical claims about the local extension;
the purely inseparable coefficient extension exposes why the residue growth
cannot be absorbed by an unramified stage. -/
structure Chapter09ImperfectLaurentSeriesExample
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] [Module.Finite k l] where
  p : ℕ
  prime : p.Prime
  characteristic : CharP k p
  a : k
  a_not_pth_power : a ∉ Set.range (fun x : k => x ^ p)
  alpha : l
  alpha_pow_eq : alpha ^ p = algebraMap k l a
  coefficient_generator : Algebra.adjoin k ({alpha} : Set l) = ⊤
  residue_purely_inseparable : IsPurelyInseparable k l
  residue_degree : ℕ
  residue_degree_eq : residue_degree = p
  residue_degree_eq_finrank : residue_degree = Module.finrank k l
  ramification_index : ℕ
  ramification_index_eq_one : ramification_index = 1
  local_field_tower : Chapter09LaurentSeriesTower k l
  local_profile : chapter09LaurentSeriesLocalProfile k l local_field_tower
    ramification_index residue_degree
  maximal_separable_part_eq_base :
    chapter09MaximalSeparableResidueSubfield k l = ⊥
  no_nontrivial_unramified_residue_subextension :
    ∀ s : IntermediateField k l, Algebra.IsSeparable k s → s = ⊥

/-- The counterexample's invariant predicate, with `e=1` and `f=p` made
explicit.  This is the exact obstruction to total ramification after taking
the maximal unramified subextension. -/
def chapter09ImperfectResidueCounterexample
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] [Module.Finite k l] (p e f : ℕ)
    (a : k) (alpha : l) : Prop :=
  p.Prime ∧ CharP k p ∧ a ∉ Set.range (fun x : k => x ^ p) ∧
    alpha ^ p = algebraMap k l a ∧
    Algebra.adjoin k ({alpha} : Set l) = ⊤ ∧
    IsPurelyInseparable k l ∧ e = 1 ∧ f = p ∧
    f = Module.finrank k l ∧
    ∃ tower : Chapter09LaurentSeriesTower k l,
      chapter09LaurentSeriesLocalProfile k l tower e f ∧
    chapter09MaximalSeparableResidueSubfield k l = ⊥ ∧
    ∀ s : IntermediateField k l, Algebra.IsSeparable k s → s = ⊥

/- The displayed Laurent-series example has exactly the obstruction above. -/
theorem chapter09_imperfect_laurent_series_counterexample
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l]
    (p : ℕ) (hp : p.Prime) [CharP k p]
    (a : k) (ha : a ∉ Set.range (fun x : k => x ^ p))
    (alpha : l) (halpha : alpha ^ p = algebraMap k l a)
    (hgenerator : Algebra.adjoin k ({alpha} : Set l) = ⊤)
    (hpure : IsPurelyInseparable k l)
    [Module.Finite k l]
    (hdegree : Module.finrank k l = p) :
    chapter09ImperfectResidueCounterexample k l p 1 p a alpha := by
  sorry

/-- The example has no nontrivial unramified residue subextension and its
remainder is not totally ramified, since its residue degree is `p`. -/
theorem chapter09_imperfect_example_has_no_clean_decomposition
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] [Module.Finite k l]
    (d : Chapter09ImperfectLaurentSeriesExample k l) :
    d.ramification_index = 1 ∧ d.residue_degree = d.p ∧
    d.residue_degree = Module.finrank k l ∧
      (∃ tower : Chapter09LaurentSeriesTower k l,
        chapter09LaurentSeriesLocalProfile k l tower d.ramification_index
          d.residue_degree) ∧
      chapter09MaximalSeparableResidueSubfield k l = ⊥ ∧
      d.residue_degree ≠ 1 ∧
      (∀ s : IntermediateField k l, Algebra.IsSeparable k s → s = ⊥) := by
  refine ⟨d.ramification_index_eq_one, d.residue_degree_eq,
    d.residue_degree_eq_finrank,
    ⟨d.local_field_tower, d.local_profile⟩,
    d.maximal_separable_part_eq_base, ?_,
    d.no_nontrivial_unramified_residue_subextension⟩
  simpa [d.residue_degree_eq] using d.prime.ne_one

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09
