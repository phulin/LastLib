import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section03CleanDecomposition
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import Mathlib.RingTheory.LaurentSeries
import Mathlib.LinearAlgebra.Dimension.Constructions
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions

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
  let vK :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesValuation k
  let vL :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesValuation l
  ∃ (hExt : vK.IsEquiv (vL.comap
      (algebraMap (chapter09LaurentSeries k) (chapter09LaurentSeries l)))),
      ∃ (_hdiscK : Valuation.IsRankOneDiscrete vK)
        (_hdiscL : Valuation.IsRankOneDiscrete vL),
        ∃ (_hcompleteK : IsAdicComplete
          (IsLocalRing.maximalIdeal vK.valuationSubring)
          vK.valuationSubring),
          ∃ (_hcompleteL : IsAdicComplete
            (IsLocalRing.maximalIdeal vL.valuationSubring)
            vL.valuationSubring),
            ∃ (hfinite : FiniteDimensional
              (chapter09LaurentSeries k) (chapter09LaurentSeries l)),
              letI : FiniteDimensional
                  (chapter09LaurentSeries k) (chapter09LaurentSeries l) := hfinite
              ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
                    vK vL hExt,
                ∃ p : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
                LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData
                  d p ∧ p.ramificationIndex = e ∧ p.residueDegree = f

/-- The coefficientwise map supplies the concrete Laurent-series tower used
in the counterexample. -/
theorem chapter09_laurent_series_tower_exists
    (k l : Type*) [Field k] [Field l] [Algebra k l] :
    Nonempty (Chapter09LaurentSeriesTower k l) := by
  let f : chapter09LaurentSeries k →+* chapter09LaurentSeries l :=
    { toFun := fun x => x.map (algebraMap k l)
      map_one' := HahnSeries.map_one (algebraMap k l).toMonoidWithZeroHom
      map_mul' := fun _ _ => HahnSeries.map_mul (algebraMap k l).toNonUnitalRingHom
      map_zero' := HahnSeries.map_zero (algebraMap k l).toZeroHom
      map_add' := fun _ _ => HahnSeries.map_add (algebraMap k l).toAddMonoidHom }
  let alg : Algebra (chapter09LaurentSeries k) (chapter09LaurentSeries l) :=
    f.toAlgebra
  refine ⟨⟨f, ?_, ?_, alg, ?_⟩⟩
  · intro x n
    rfl
  · intro x y hxy
    apply HahnSeries.ext
    funext n
    apply (RingHom.injective (algebraMap k l))
    exact congrArg (fun z : chapter09LaurentSeries l => z.coeff n) hxy
  · rfl

/-- The coefficient-field basis, applied coefficientwise, spans the induced
Laurent-series extension. -/
theorem chapter09_laurent_series_module_finite
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Module.Finite k l] (tower : Chapter09LaurentSeriesTower k l) :
    letI : Algebra (chapter09LaurentSeries k) (chapter09LaurentSeries l) :=
      tower.algebra
    Module.Finite (chapter09LaurentSeries k) (chapter09LaurentSeries l) := by
  let _ : Algebra (chapter09LaurentSeries k) (chapter09LaurentSeries l) := tower.algebra
  let b := Module.finBasis k l
  let coord (i : Fin (Module.finrank k l)) : l →ₗ[k] k :=
    (Finsupp.lapply i).comp b.repr.toLinearMap
  let g : (Fin (Module.finrank k l) → chapter09LaurentSeries k) →ₗ[chapter09LaurentSeries k]
      chapter09LaurentSeries l :=
    { toFun := fun z => ∑ i, z i • HahnSeries.C (b i)
      map_add' := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c z
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [RingHom.id_apply]
        rw [mul_smul] }
  apply Module.Finite.of_surjective g
  intro x
  let z : Fin (Module.finrank k l) → chapter09LaurentSeries k :=
    fun i => x.map (coord i)
  refine ⟨z, ?_⟩
  change (∑ i, z i • HahnSeries.C (b i)) = x
  simp_rw [show ∀ i, z i • HahnSeries.C (b i) =
      tower.map (z i) * HahnSeries.C (b i) by
    intro i
    rw [Algebra.smul_def, tower.algebra_map_eq_map]]
  apply HahnSeries.ext
  funext n
  simp only [HahnSeries.coeff_sum]
  simpa [z, coord, tower.map_coeff, Algebra.smul_def] using
    b.sum_repr (x.coeff n)

/-- The canonical Laurent-series valuation is unchanged by an injective
coefficientwise field map. -/
theorem chapter09_laurent_series_valuation_map
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    (tower : Chapter09LaurentSeriesTower k l) (x : chapter09LaurentSeries k) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesValuation l
        (tower.map x) =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesValuation k x := by
  by_cases hx : x = 0
  · simp [hx]
  have hmap : tower.map x ≠ 0 := by
    simpa using tower.map_injective.ne hx
  apply le_antisymm
  · apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero l
      ((Valuation.ne_zero_iff _).2 hx)).2
    intro n hn
    rw [tower.map_coeff, map_eq_zero]
    exact (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero k
      ((Valuation.ne_zero_iff _).2 hx)).1 le_rfl n hn
  · apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero k
      ((Valuation.ne_zero_iff _).2 hmap)).2
    intro n hn
    apply (RingHom.injective (algebraMap k l))
    rw [map_zero, ← tower.map_coeff]
    exact (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero l
      ((Valuation.ne_zero_iff _).2 hmap)).1 le_rfl n hn

/-- The valuation ring of a Laurent-series field is complete for its maximal
ideal topology. -/
theorem chapter09_laurent_series_valuation_ring_complete
    (k : Type*) [Field k] : IsAdicComplete
      (IsLocalRing.maximalIdeal
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesValuation k).valuationSubring)
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesValuation k).valuationSubring := by
  let e :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesValuationRingEquiv k
  have hps : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k))
      (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  change IsAdicComplete
    (IsLocalRing.maximalIdeal
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.valuationRingOf
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesValuation k)))
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.valuationRingOf
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter03.laurentSeriesValuation k))
  rw [← IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective]
  exact (IsAdicComplete.congr_ringEquiv _ e).mpr hps

/-- The canonical Laurent-series valuation is rank-one discrete. -/
theorem chapter09_laurent_series_valuation_discrete
    (k : Type*) [Field k] : Valuation.IsRankOneDiscrete
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesValuation k) := by
  change Valuation.IsRankOneDiscrete
    ((PowerSeries.idealX k).valuation (LaurentSeries k))
  infer_instance

/-- A finite coefficient-field extension gives the canonical constant-field
Laurent-series profile, with ramification index one and residue degree equal
to the coefficient-field degree. -/
theorem chapter09_laurent_series_local_profile
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Module.Finite k l] (tower : Chapter09LaurentSeriesTower k l) :
    chapter09LaurentSeriesLocalProfile k l tower 1 (Module.finrank k l) := by
  let _ : Algebra (chapter09LaurentSeries k) (chapter09LaurentSeries l) := tower.algebra
  have hfinite : Module.Finite (chapter09LaurentSeries k)
      (chapter09LaurentSeries l) :=
    chapter09_laurent_series_module_finite k l tower
  let _ : Module.Finite (chapter09LaurentSeries k)
      (chapter09LaurentSeries l) := hfinite
  have hscalar : IsScalarTower k (chapter09LaurentSeries k)
      (chapter09LaurentSeries l) := by
    constructor
    intro a x y
    have hax : tower.map (a • x) = a • tower.map x := by
      apply HahnSeries.ext
      funext n
      simp [tower.map_coeff, Algebra.smul_def]
    simp only [Algebra.smul_def, tower.algebra_map_eq_map]
    rw [hax]
    have hsmul (z : chapter09LaurentSeries l) :
        a • z = algebraMap l (chapter09LaurentSeries l) (algebraMap k l a) * z := by
      rw [HahnSeries.algebraMap_apply' ℤ, PowerSeries.algebraMap_apply,
        HahnSeries.ofPowerSeries_C]
      calc
        a • z = (algebraMap k l a) • z := by
          apply HahnSeries.ext
          funext n
          simp [Algebra.smul_def]
        _ = HahnSeries.C (algebraMap k l a) * z :=
          (@HahnSeries.C_mul_eq_smul ℤ l _ _ _ _
            (r := algebraMap k l a) (x := z)).symm
    rw [hsmul (tower.map x), hsmul (tower.map x * y)]
    exact mul_assoc _ _ _
  let _ : IsScalarTower k (chapter09LaurentSeries k)
      (chapter09LaurentSeries l) := hscalar
  let vK :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesValuation k
  let vL :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesValuation l
  have hvaleq : vK = vL.comap
      (algebraMap (chapter09LaurentSeries k) (chapter09LaurentSeries l)) := by
    ext x
    change vK x = vL (algebraMap (chapter09LaurentSeries k)
      (chapter09LaurentSeries l) x)
    rw [tower.algebra_map_eq_map]
    exact (chapter09_laurent_series_valuation_map k l tower x).symm
  have hExt : vK.IsEquiv (vL.comap
      (algebraMap (chapter09LaurentSeries k) (chapter09LaurentSeries l))) :=
    Valuation.IsEquiv.of_eq hvaleq
  refine ⟨hExt, chapter09_laurent_series_valuation_discrete k,
    chapter09_laurent_series_valuation_discrete l,
    chapter09_laurent_series_valuation_ring_complete k,
    chapter09_laurent_series_valuation_ring_complete l, hfinite, ?_⟩
  have hparameter :
      algebraMap (LaurentSeries k) (LaurentSeries l)
          (((PowerSeries.X : PowerSeries k) : LaurentSeries k)) =
        ((PowerSeries.X : PowerSeries l) : LaurentSeries l) := by
    apply HahnSeries.ext
    funext n
    rw [tower.algebra_map_eq_map, tower.map_coeff]
    by_cases hn : n = 1
    · subst n
      simp
    · simp [hn]
  have hcoeff : ∀ (x : LaurentSeries k) (n : ℤ),
      (algebraMap (LaurentSeries k) (LaurentSeries l) x).coeff n =
        algebraMap k l (x.coeff n) := by
    intro x n
    rw [tower.algebra_map_eq_map]
    exact tower.map_coeff x n
  obtain ⟨d, p, hprofile, _hdegree, hram, hres, _hunram⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_constant_field_extension_numerical_profile
      hparameter hcoeff hExt
  exact ⟨d, p, hprofile, hram, hres⟩

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
  obtain ⟨tower⟩ := chapter09_laurent_series_tower_exists k l
  have hprofile : chapter09LaurentSeriesLocalProfile k l tower 1 p := by
    simpa [hdegree] using chapter09_laurent_series_local_profile k l tower
  let pureInst : IsPurelyInseparable k l := hpure
  have hsepbot : chapter09MaximalSeparableResidueSubfield k l = ⊥ := by
    let _ : IsPurelyInseparable k l := pureInst
    exact separableClosure.eq_bot_of_isPurelyInseparable k l
  have hsub : ∀ s : IntermediateField k l, Algebra.IsSeparable k s → s = ⊥ := by
    intro s hsep
    let _ : IsPurelyInseparable k l := pureInst
    let _ : Algebra.IsSeparable k s := hsep
    let _ : IsPurelyInseparable k s :=
      IsPurelyInseparable.tower_bot k s l
    exact IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable s
  exact ⟨hp, inferInstance, ha, halpha, hgenerator, hpure, rfl, rfl,
    hdegree.symm, tower, hprofile, hsepbot, hsub⟩

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
