import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section03CleanDecomposition

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09

open scoped BigOperators Polynomial LaurentSeries
open Ideal IsLocalRing Polynomial

noncomputable section

/-! ## Book 2, Chapter 9.4: the imperfect-residue-field obstruction -/

/-- Mathlib's formal Laurent-series model for the notation `k((t))` used in
the counterexample.  The residue-extension data is kept separate because the
chapter only needs the coefficient-field extension to identify the failure. -/
abbrev chapter09LaurentSeries (k : Type*) [Zero k] : Type _ := LaurentSeries k

/-- Residue-level data for the example
`k((t)) ⊂ k(a^(1/p))((t))`.  The fields `ramification_index` and
`residue_degree` expose the two numerical claims about the local extension;
the purely inseparable coefficient extension exposes why the residue growth
cannot be absorbed by an unramified stage. -/
structure Chapter09ImperfectLaurentSeriesExample
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] where
  p : ℕ
  prime : p.Prime
  characteristic : CharP k p
  a : k
  a_not_pth_power : a ∉ Set.range (fun x : k => x ^ p)
  alpha : l
  alpha_pow_eq : alpha ^ p = algebraMap k l a
  residue_purely_inseparable : IsPurelyInseparable k l
  residue_degree : ℕ
  residue_degree_eq : residue_degree = p
  ramification_index : ℕ
  ramification_index_eq_one : ramification_index = 1
  maximal_separable_part_eq_base :
    chapter09MaximalSeparableResidueSubfield k l = ⊥
  no_nontrivial_unramified_residue_subextension :
    ∀ s : IntermediateField k l, Algebra.IsSeparable k s → s = ⊥

/-- The counterexample's invariant predicate, with `e=1` and `f=p` made
explicit.  This is the exact obstruction to total ramification after taking
the maximal unramified subextension. -/
def chapter09ImperfectResidueCounterexample
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] (p e f : ℕ) : Prop :=
  p.Prime ∧ CharP k p ∧
    IsPurelyInseparable k l ∧ e = 1 ∧ f = p ∧
    chapter09MaximalSeparableResidueSubfield k l = ⊥ ∧
    ∀ s : IntermediateField k l, Algebra.IsSeparable k s → s = ⊥

/- The displayed Laurent-series example has exactly the obstruction above. -/
theorem chapter09_imperfect_laurent_series_counterexample
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l]
    (p : ℕ) (hp : p.Prime) [CharP k p]
    (a : k) (ha : a ∉ Set.range (fun x : k => x ^ p))
    (alpha : l) (halpha : alpha ^ p = algebraMap k l a)
    (hpure : IsPurelyInseparable k l)
    [Module.Finite k l]
    (hdegree : Module.finrank k l = p) :
    chapter09ImperfectResidueCounterexample k l p 1 p := by
  sorry

/-- The example has no nontrivial unramified residue subextension and its
remainder is not totally ramified, since its residue degree is `p`. -/
theorem chapter09_imperfect_example_has_no_clean_decomposition
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l]
    (d : Chapter09ImperfectLaurentSeriesExample k l) :
    d.ramification_index = 1 ∧ d.residue_degree = d.p ∧
      chapter09MaximalSeparableResidueSubfield k l = ⊥ := by
  exact ⟨d.ramification_index_eq_one, d.residue_degree_eq,
    d.maximal_separable_part_eq_base⟩

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09
