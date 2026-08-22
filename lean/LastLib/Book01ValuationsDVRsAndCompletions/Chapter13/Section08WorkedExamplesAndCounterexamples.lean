import LastLib.Book01ValuationsDVRsAndCompletions.Chapter13.Section07TheStructureTheorem
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.Section03ArithmeticAndExamples
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter07.Section05SeparatedCompletionOfRings
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter13

open Ideal IsLocalRing
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable section

/-! # Book 1, Chapter 13, Section 13.8: Worked examples and counterexamples -/

universe u

/-- Two distinct coefficient fields in one complete power-series ring. -/
structure Chapter13TwoCoefficientFieldExample
    (k : Type u) [Field k] (u₀ : k) where
  first : Chapter13Subfield (PowerSeries k)
  second : Chapter13Subfield (PowerSeries k)
  first_is_coefficient : Chapter13IsCoefficientField first
  second_is_coefficient : Chapter13IsCoefficientField second
  constants_mem_first : ∀ a : k, PowerSeries.C a ∈ first.carrier
  translated_generator : PowerSeries.C u₀ + PowerSeries.X ∈ second.carrier
  distinct : first.carrier ≠ second.carrier

/-- A power-series lift of a chosen `p`-basis family by elements of the maximal ideal. -/
def Chapter13PowerSeriesPBasisLift
    {k : Type u} [Field k] {B : Set k}
    (g : B → PowerSeries k) : B → PowerSeries k :=
  fun b => PowerSeries.C b.1 + g b

theorem chapter13_nonunique_coefficient_fields
    (k : Type u) [Field k] [Algebra ℚ k] (u₀ : k)
    (hu₀ : Transcendental ℚ u₀) :
    Nonempty (Chapter13TwoCoefficientFieldExample k u₀) := by
  let f : k →+* PowerSeries k := PowerSeries.C
  have hf : Function.Injective f := by
    simpa [f] using PowerSeries.C_injective
  let e : k ≃+* f.range :=
    RingEquiv.ofBijective f.rangeRestrict
      ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hfield : IsField f.range :=
    e.symm.toMulEquiv.isField (Field.toIsField k)
  let first : Chapter13Subfield (PowerSeries k) :=
    ⟨f.range, hfield⟩
  have hconst := chapter13_power_series_constants_are_coefficients k
  have hfirst : Chapter13IsCoefficientField first := by
    constructor
    · intro x y hxy
      obtain ⟨a, ha⟩ := x.property
      obtain ⟨b, hb⟩ := y.property
      have hab : a = b := hconst.1 (by
        simpa [f, ha, hb] using hxy)
      exact Subtype.ext (ha.symm.trans (congrArg f hab) |>.trans hb)
    · intro z
      obtain ⟨a, ha⟩ := hconst.2 z
      refine ⟨f.rangeRestrict a, ?_⟩
      simpa [f] using ha
  let ρ : PowerSeries k →+* k := PowerSeries.constantCoeff
  let σ : ℚ →+* PowerSeries k :=
    (PowerSeries.C : k →+* PowerSeries k).comp (algebraMap ℚ k)
  have hρ : RingHom.ker ρ = IsLocalRing.maximalIdeal (PowerSeries k) := by
    exact PowerSeries.ker_coeff_eq_max_ideal (k := k)
  have hσ : ρ.comp σ = algebraMap ℚ k := by
    ext q
    simp [ρ, σ]
  have haρ : ρ (PowerSeries.C u₀ + PowerSeries.X) = u₀ := by
    simp [ρ]
  have hdata : Chapter13TranscendentalLiftData
      (PowerSeries k) ℚ k σ ρ u₀ (PowerSeries.C u₀ + PowerSeries.X) :=
    ⟨hρ, hσ, haρ, hu₀⟩
  obtain ⟨ι, hι⟩ := chapter13_transcendental_fraction_field_lift hdata
  let er : FractionRing (Polynomial ℚ) ≃+* ι.range :=
    RingEquiv.ofBijective ι.rangeRestrict
      ⟨fun x y h => by
          exact (RingHom.injective ι) (congrArg Subtype.val h),
        ι.rangeRestrict_surjective⟩
  have herfield : IsField ι.range :=
    er.symm.toMulEquiv.isField (Field.toIsField (FractionRing (Polynomial ℚ)))
  let second₀ : Chapter13Subfield (PowerSeries k) :=
    ⟨ι.range, herfield⟩
  have hcontains : Chapter13ContainsField (PowerSeries k) := ⟨first⟩
  have hcharK : CharP k 0 := by
    exact ((algebraMap ℚ k).charP_iff_charP 0).mp inferInstance
  have hchar : CharP (Chapter13ResidueRing (PowerSeries k)) 0 := by
    exact ((Chapter13ResidueMap (PowerSeries k)).comp f
      |>.charP_iff_charP 0).mp hcharK
  have hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hcoeff := chapter13_coefficient_field_exists_equal_characteristic_zero
    (A := PowerSeries k) hcomplete hchar hcontains
  obtain ⟨second, hsecond_ext, hsecond⟩ := hcoeff.2.2 second₀
  have htranslated : PowerSeries.C u₀ + PowerSeries.X ∈ second₀.carrier := by
    change PowerSeries.C u₀ + PowerSeries.X ∈ ι.range
    refine ⟨algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))
      Polynomial.X, ?_⟩
    have hx := congrArg (fun g => g Polynomial.X) hι
    simpa [σ, Polynomial.eval₂RingHom] using hx
  have htranslated' : PowerSeries.C u₀ + PowerSeries.X ∈ second.carrier :=
    hsecond_ext htranslated
  have hdistinct : first.carrier ≠ second.carrier := by
    intro heq
    have hx : PowerSeries.C u₀ + PowerSeries.X ∈ first.carrier := by
      rw [heq]
      exact htranslated'
    obtain ⟨a, ha⟩ := hx
    have ha' : PowerSeries.C a = PowerSeries.C u₀ + PowerSeries.X := by
      simpa [f] using ha
    have ha'' := congrArg (fun z : PowerSeries k => z.coeff 1) ha'
    simp at ha''
  exact ⟨⟨first, second, hfirst, hsecond, fun a => ⟨a, rfl⟩,
    htranslated', hdistinct⟩⟩

theorem chapter13_p_basis_lift_family_power_series
    (k : Type u) [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (B : Set k)
    (_hB : Chapter13PBasis (Chapter13PthPowerSubfield k p) B p)
    (g : B → PowerSeries k)
    (_hg : ∀ b : B, g b ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) :
    ∃ K : Chapter13Subfield (PowerSeries k),
      Chapter13IsCoefficientField K := by
  let f : k →+* PowerSeries k := PowerSeries.C
  have hf : Function.Injective f := by
    simpa [f] using PowerSeries.C_injective
  let e : k ≃+* f.range :=
    RingEquiv.ofBijective f.rangeRestrict
      ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hfield : IsField f.range :=
    e.symm.toMulEquiv.isField (Field.toIsField k)
  refine ⟨⟨f.range, hfield⟩, ?_⟩
  have hconst := chapter13_power_series_constants_are_coefficients k
  constructor
  · intro x y hxy
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    have hab : a = b := hconst.1 (by
      simpa [f, ha, hb] using hxy)
    exact Subtype.ext (ha.symm.trans (congrArg f hab) |>.trans hb)
  · intro z
    obtain ⟨a, ha⟩ := hconst.2 z
    refine ⟨f.rangeRestrict a, ?_⟩
    simpa [f] using ha

/-! ### A maximal subfield can miss part of the residue field -/

theorem chapter13_maximal_subfield_not_coefficient
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ K : Chapter13Subfield
        (PowerSeries (FractionRing (Polynomial (ZMod p)))),
      Chapter13IsMaximalSubfield K ∧ ¬Chapter13IsCoefficientField K := by
  let k := FractionRing (Polynomial (ZMod p))
  let u : k := algebraMap (Polynomial (ZMod p)) k Polynomial.X
  have hu : Transcendental (ZMod p) u := by
    exact (transcendental_algebraMap_iff (IsFractionRing.injective
      (R := Polynomial (ZMod p)) (K := k))).mpr
      (Polynomial.transcendental_X (ZMod p))
  have hpu : Transcendental (ZMod p) (u ^ p) :=
    hu.pow ((Fact.out : Nat.Prime p).pos)
  let ρ : PowerSeries k →+* k := PowerSeries.constantCoeff
  let σ : ZMod p →+* PowerSeries k :=
    (PowerSeries.C : k →+* PowerSeries k).comp (algebraMap (ZMod p) k)
  have hρ : RingHom.ker ρ = IsLocalRing.maximalIdeal (PowerSeries k) := by
    exact PowerSeries.ker_coeff_eq_max_ideal (k := k)
  have hσ : ρ.comp σ = algebraMap (ZMod p) k := by
    ext q
    simp [ρ, σ]
  let a : PowerSeries k := PowerSeries.C (u ^ p) + PowerSeries.X
  have haρ : ρ a = u ^ p := by
    simp [a, ρ]
  have hdata : Chapter13TranscendentalLiftData
      (PowerSeries k) (ZMod p) k σ ρ (u ^ p) a :=
    ⟨hρ, hσ, haρ, hpu⟩
  obtain ⟨ι, hι⟩ := chapter13_transcendental_fraction_field_lift hdata
  let er : FractionRing (Polynomial (ZMod p)) ≃+* ι.range :=
    RingEquiv.ofBijective ι.rangeRestrict
      ⟨fun x y h => by
          exact (RingHom.injective ι) (congrArg Subtype.val h),
        ι.rangeRestrict_surjective⟩
  have herfield : IsField ι.range :=
    er.symm.toMulEquiv.isField
      (Field.toIsField (FractionRing (Polynomial (ZMod p))))
  let K₀ : Chapter13Subfield (PowerSeries k) := ⟨ι.range, herfield⟩
  let : Preorder (Chapter13Subfield (PowerSeries k)) :=
    { le := fun K L => K.carrier ≤ L.carrier
      le_refl := fun K => le_rfl
      le_trans := fun _ _ _ hKL hLM => hKL.trans hLM }
  have hmaximal_extension : ∀ K₀ : Chapter13Subfield (PowerSeries k),
      ∃ K : Chapter13Subfield (PowerSeries k),
        K₀.carrier ≤ K.carrier ∧ Chapter13IsMaximalSubfield K := by
    intro K₀
    obtain ⟨K, hK, hKmax⟩ := zorn_le_nonempty_Ici₀ K₀
      (fun c hc hchain y hy => by
        let U : Set (PowerSeries k) := ⋃ K : Chapter13Subfield (PowerSeries k),
          ⋃ (_ : K ∈ c), (K.carrier : Set (PowerSeries k))
        have memU : ∀ {x : PowerSeries k}, x ∈ U →
            ∃ K ∈ c, x ∈ K.carrier := by
          intro x hx
          change x ∈ ⋃ K : Chapter13Subfield (PowerSeries k),
            ⋃ (_ : K ∈ c), (K.carrier : Set (PowerSeries k)) at hx
          rcases Set.mem_iUnion.mp hx with ⟨K, hx⟩
          rcases Set.mem_iUnion.mp hx with ⟨hK, hx⟩
          exact ⟨K, hK, hx⟩
        have memU' : ∀ {K : Chapter13Subfield (PowerSeries k)}, K ∈ c →
            ∀ {x : PowerSeries k}, x ∈ K.carrier → x ∈ U := by
          intro K hK x hx
          change x ∈ ⋃ K : Chapter13Subfield (PowerSeries k),
            ⋃ (_ : K ∈ c), (K.carrier : Set (PowerSeries k))
          exact Set.mem_iUnion.2 ⟨K, Set.mem_iUnion.2 ⟨hK, hx⟩⟩
        let Ucarrier : Subring (PowerSeries k) :=
          { carrier := U
            zero_mem' := memU' hy (zero_mem y.carrier)
            add_mem' := by
              intro x z hx hz
              obtain ⟨Kx, hKx, hx⟩ := memU hx
              obtain ⟨Kz, hKz, hz⟩ := memU hz
              have hcomp : Kx ≤ Kz ∨ Kz ≤ Kx := by
                by_cases heq : Kx = Kz
                · subst Kz
                  exact Or.inl le_rfl
                · exact hchain hKx hKz heq
              rcases hcomp with hle | hle
              · exact memU' hKz (Kz.carrier.add_mem (hle hx) hz)
              · exact memU' hKx (Kx.carrier.add_mem hx (hle hz))
            one_mem' := memU' hy (one_mem y.carrier)
            mul_mem' := by
              intro x z hx hz
              obtain ⟨Kx, hKx, hx⟩ := memU hx
              obtain ⟨Kz, hKz, hz⟩ := memU hz
              have hcomp : Kx ≤ Kz ∨ Kz ≤ Kx := by
                by_cases heq : Kx = Kz
                · subst Kz
                  exact Or.inl le_rfl
                · exact hchain hKx hKz heq
              rcases hcomp with hle | hle
              · exact memU' hKz (Kz.carrier.mul_mem (hle hx) hz)
              · exact memU' hKx (Kx.carrier.mul_mem hx (hle hz))
            neg_mem' := by
              intro x hx
              obtain ⟨Kx, hKx, hx⟩ := memU hx
              exact memU' hKx (Kx.carrier.neg_mem hx) }
        let : Field y.carrier := y.field_carrier.toField
        have hUfield : IsField Ucarrier :=
          { exists_pair_ne := by
              obtain ⟨x, z, hxz⟩ := y.field_carrier.exists_pair_ne
              refine ⟨⟨x, memU' hy x.property⟩,
                ⟨z, memU' hy z.property⟩, ?_⟩
              intro heq
              apply hxz
              apply Subtype.ext
              exact congrArg (fun w : Ucarrier => w.1) heq
            mul_comm := by
              intro x z
              apply Subtype.ext
              exact mul_comm x.1 z.1
            mul_inv_cancel := by
              intro x hx
              obtain ⟨Kx, hKx, hxK⟩ := memU x.property
              let xK : Kx.carrier := ⟨x.1, hxK⟩
              have hxK0 : xK ≠ 0 := by
                intro hzero
                apply hx
                apply Subtype.ext
                exact congrArg (fun w : Kx.carrier => w.1) hzero
              obtain ⟨z, hz⟩ := Kx.field_carrier.mul_inv_cancel hxK0
              refine ⟨⟨z.1, memU' hKx z.property⟩, ?_⟩
              apply Subtype.ext
              simpa using congrArg Subtype.val hz }
        let Usub : Chapter13Subfield (PowerSeries k) :=
          ⟨Ucarrier, hUfield⟩
        refine ⟨Usub, ?_⟩
        intro z hz
        exact fun x hx => memU' hz hx) K₀ le_rfl
    refine ⟨K, hK, ?_⟩
    intro L hKL
    exact hKmax hKL
  obtain ⟨K, hK₀, hKmax⟩ := hmaximal_extension K₀
  refine ⟨K, hKmax, ?_⟩
  intro hcoeff
  obtain ⟨z, hz⟩ := hcoeff.2
    (Chapter13ResidueMap (PowerSeries k) (PowerSeries.C u))
  have haK : a ∈ K.carrier := hK₀ (show a ∈ K₀.carrier by
    change a ∈ RingHom.range ι
    refine ⟨algebraMap (Polynomial (ZMod p))
      (FractionRing (Polynomial (ZMod p))) Polynomial.X, ?_⟩
    have hx := congrArg (fun g => g Polynomial.X) hι
    simpa [a, σ, Polynomial.eval₂RingHom] using hx)
  let zA : PowerSeries k := K.carrier.subtype z
  have hmem : zA ^ p - a ∈ IsLocalRing.maximalIdeal (PowerSeries k) := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change Chapter13ResidueMap (PowerSeries k) (zA ^ p - a) = 0
    rw [map_sub, map_pow]
    have hzA : Chapter13ResidueMap (PowerSeries k) zA =
        Chapter13ResidueMap (PowerSeries k) (PowerSeries.C u) := by
      simpa [zA] using hz
    rw [hzA]
    have hresX : Chapter13ResidueMap (PowerSeries k) PowerSeries.X = 0 := by
      change Ideal.Quotient.mk _ PowerSeries.X = 0
      apply (Ideal.Quotient.eq_zero_iff_mem).mpr
      rw [PowerSeries.maximalIdeal_eq_span_X]
      exact Ideal.subset_span (by simp)
    have hres_a : (Chapter13ResidueMap (PowerSeries k)) a =
        (Chapter13ResidueMap (PowerSeries k)) (PowerSeries.C u) ^ p := by
      simp [a, map_pow, hresX]
    rw [hres_a, sub_self]
  have hzero : zA ^ p - a = 0 := by
    by_contra hne
    let : Field K.carrier := K.field_carrier.toField
    let aK : K.carrier := ⟨a, haK⟩
    have hneK : z ^ p - aK ≠ 0 := by
      intro hzK
      apply hne
      exact congrArg K.carrier.subtype hzK
    have huK : IsUnit (z ^ p - aK) := isUnit_iff_ne_zero.mpr hneK
    have huA := IsUnit.map K.carrier.subtype huK
    exact (IsLocalRing.notMem_maximalIdeal.mpr (by
      simpa [zA, aK, map_sub, map_pow] using huA)) hmem
  have hcoeffeq := congrArg (fun w : PowerSeries k => w.coeff 1) hzero
  have hleft : (zA ^ p).coeff 1 = 0 := by
    rw [PowerSeries.coeff_one_pow]
    have hp0 : (p : k) = 0 := CharP.cast_eq_zero (R := k) p
    rw [hp0]
    simp
  have hright : a.coeff 1 = 1 := by
    rw [show a = PowerSeries.C (u ^ p) + PowerSeries.X by rfl,
      map_add, PowerSeries.coeff_C, PowerSeries.coeff_X]
    norm_num
  have hcoeffeq' : (zA ^ p).coeff 1 - a.coeff 1 = 0 := by
    simpa using hcoeffeq
  rw [hleft, hright] at hcoeffeq'
  exact zero_ne_one (sub_eq_zero.mp hcoeffeq')

/-! ### The cusp -/

abbrev Chapter13CuspPowerSeriesSubring (k : Type u) [CommRing k] :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04CuspPowerSeriesSubring k

abbrev Chapter13CuspPowerSeriesMaximalIdeal (k : Type u) [Field k] :
    Ideal (Chapter13CuspPowerSeriesSubring k) :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04CuspPowerSeriesMaximalIdeal k

def Chapter13CuspRelation (k : Type u) [CommRing k] :
    MvPowerSeries (Fin 2) k :=
  (MvPowerSeries.X (1 : Fin 2)) ^ 2 - (MvPowerSeries.X (0 : Fin 2)) ^ 3

theorem chapter13_cusp_presentation
    (k : Type u) [Field k] :
    Nonempty
        ((MvPowerSeries (Fin 2) k ⧸
            Ideal.span {Chapter13CuspRelation k}) ≃+*
          Chapter13CuspPowerSeriesSubring k) ∧
      ¬IsRegularLocalRing (Chapter13CuspPowerSeriesSubring k) := by
  constructor
  · let _ : TopologicalSpace k := ⊥
    let _ : UniformSpace k := ⊥
    let _ : DiscreteTopology k := discreteTopology_bot k
    have hX : IsTopologicallyNilpotent (PowerSeries.X : PowerSeries k) :=
      PowerSeries.HasEval.X
    have hpow : ∀ i : Fin 2,
        IsTopologicallyNilpotent
          (if i = 0 then (PowerSeries.X : PowerSeries k) ^ 2 else PowerSeries.X ^ 3) := by
      intro i
      fin_cases i
      · change IsTopologicallyNilpotent ((PowerSeries.X : PowerSeries k) ^ 2)
        simpa only [pow_two] using hX.mul_right (PowerSeries.X : PowerSeries k)
      · change IsTopologicallyNilpotent ((PowerSeries.X : PowerSeries k) ^ 3)
        change IsTopologicallyNilpotent
          ((PowerSeries.X : PowerSeries k) ^ 2 * PowerSeries.X)
        exact hX.mul_left ((PowerSeries.X : PowerSeries k) ^ 2)
    have hzero : Filter.Tendsto
        (fun i : Fin 2 =>
          if i = 0 then (PowerSeries.X : PowerSeries k) ^ 2 else PowerSeries.X ^ 3)
        Filter.cofinite (nhds 0) := by
      rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
    have ha : MvPowerSeries.HasEval (fun i : Fin 2 =>
        if i = 0 then (PowerSeries.X : PowerSeries k) ^ 2 else PowerSeries.X ^ 3) :=
      ⟨hpow, hzero⟩
    let a : Fin 2 → PowerSeries k := fun i =>
      if i = 0 then (PowerSeries.X : PowerSeries k) ^ 2 else PowerSeries.X ^ 3
    let E : MvPowerSeries (Fin 2) k →+* PowerSeries k :=
      MvPowerSeries.eval₂Hom (continuous_algebraMap k (PowerSeries k)) ha
    have hpoly : ∀ p : MvPolynomial (Fin 2) k,
        PowerSeries.coeff 1 (MvPolynomial.eval₂Hom (PowerSeries.C : k →+* PowerSeries k)
          a p) = 0 := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C c => simp [a]
      | add p q hp hq =>
          have hp' : PowerSeries.coeff 1 (MvPolynomial.eval₂
              (PowerSeries.C : k →+* PowerSeries k) a p) = 0 := by
            simpa only [MvPolynomial.coe_eval₂Hom] using hp
          have hq' : PowerSeries.coeff 1 (MvPolynomial.eval₂
              (PowerSeries.C : k →+* PowerSeries k) a q) = 0 := by
            simpa only [MvPolynomial.coe_eval₂Hom] using hq
          simp [map_add, hp', hq']
      | mul_X p i hp =>
          have hp' : PowerSeries.coeff 1 (MvPolynomial.eval₂
              (PowerSeries.C : k →+* PowerSeries k) a p) = 0 := by
            simpa only [MvPolynomial.coe_eval₂Hom] using hp
          rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_mul,
            MvPolynomial.eval₂_X]
          fin_cases i
          · simp [a, PowerSeries.coeff_one_mul, hp']
          · simp [a, PowerSeries.coeff_one_mul, hp']
    have hEcont : Continuous (E : MvPowerSeries (Fin 2) k → PowerSeries k) := by
      simpa only [E, MvPowerSeries.coe_eval₂Hom] using
        (MvPowerSeries.continuous_eval₂
          (continuous_algebraMap k (PowerSeries k)) ha)
    have hcoeffcont : Continuous (fun f : MvPowerSeries (Fin 2) k =>
        PowerSeries.coeff 1 (E f)) :=
      (PowerSeries.WithPiTopology.continuous_coeff k 1).comp hEcont
    have hrestrict : ∀ p : MvPolynomial (Fin 2) k,
        (fun f : MvPowerSeries (Fin 2) k => PowerSeries.coeff 1 (E f))
            (p : MvPowerSeries (Fin 2) k) = 0 := by
      intro p
      simpa [E, MvPowerSeries.coe_eval₂Hom] using hpoly p
    have hext :
        MvPolynomial.toMvPowerSeries_isDenseInducing.extend
            (fun _ : MvPolynomial (Fin 2) k => (0 : k)) =
          (fun f : MvPowerSeries (Fin 2) k => PowerSeries.coeff 1 (E f)) := by
      apply MvPolynomial.toMvPowerSeries_isDenseInducing.extend_unique
      · exact hrestrict
      · exact hcoeffcont
    have hzeroext :
        MvPolynomial.toMvPowerSeries_isDenseInducing.extend
            (fun _ : MvPolynomial (Fin 2) k => (0 : k)) =
          (fun _ : MvPowerSeries (Fin 2) k => (0 : k)) := by
      apply MvPolynomial.toMvPowerSeries_isDenseInducing.extend_unique
      · intro p
        rfl
      · exact continuous_const
    have hcoeff : ∀ f : MvPowerSeries (Fin 2) k,
        PowerSeries.coeff 1 (E f) = 0 := by
      intro f
      have := congrFun (hzeroext.symm.trans hext) f
      exact this.symm
    have hX0 : PowerSeries.HasSubst
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) k) :=
      PowerSeries.HasSubst.X (0 : Fin 2)
    let J : PowerSeries k →ₐ[k] MvPowerSeries (Fin 2) k :=
      PowerSeries.substAlgHom hX0
    have hX2 : PowerSeries.HasSubst (PowerSeries.X ^ 2 : PowerSeries k) :=
      PowerSeries.HasSubst.X_pow (by decide)
    let K2 : PowerSeries k →ₐ[k] PowerSeries k :=
      PowerSeries.substAlgHom hX2
    let Ealg : MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k :=
      MvPowerSeries.aeval ha
    have hEalg : Ealg.toRingHom = E := by
      ext f
      rfl
    have hJcont : Continuous (J : PowerSeries k → MvPowerSeries (Fin 2) k) := by
      rw [show J = PowerSeries.aeval hX0.hasEval by
        simpa [J] using (PowerSeries.substAlgHom_eq_aeval hX0)]
      exact PowerSeries.continuous_aeval hX0.hasEval
    have hEalgcont : Continuous (Ealg : MvPowerSeries (Fin 2) k → PowerSeries k) := by
      exact MvPowerSeries.continuous_aeval ha
    have hcomp : Ealg.comp J = K2 := by
      have hcompcont : Continuous ((Ealg.comp J).toRingHom :
          PowerSeries k → PowerSeries k) := hEalgcont.comp hJcont
      have hXcomp : (Ealg.comp J) PowerSeries.X = PowerSeries.X ^ 2 := by
        simp [Ealg, J, PowerSeries.substAlgHom_X, MvPowerSeries.coe_aeval]
      have hpoint0 : PowerSeries.HasEval ((Ealg.comp J) PowerSeries.X) :=
        PowerSeries.HasEval.map hcompcont PowerSeries.HasEval.X
      have hpoint : PowerSeries.HasEval ((PowerSeries.X : PowerSeries k) ^ 2) := by
        rw [← hXcomp]
        exact hpoint0
      have hu0 : PowerSeries.aeval hpoint0 = Ealg.comp J :=
        PowerSeries.aeval_unique (ε := Ealg.comp J) hcompcont
      have hu : PowerSeries.aeval hpoint = Ealg.comp J := by
        simpa only [hXcomp] using hu0
      change Ealg.comp J = PowerSeries.substAlgHom hX2
      rw [PowerSeries.substAlgHom_eq_aeval hX2]
      have hproof : hpoint = hX2.hasEval := Subsingleton.elim _ _
      rw [hproof] at hu
      exact hu.symm
    have hEJ : ∀ f : PowerSeries k, E (J f) = K2 f := by
      intro f
      have hf := congrArg (fun h : PowerSeries k →ₐ[k] PowerSeries k => h f) hcomp
      rw [← hEalg]
      exact hf
    let S : Subring (PowerSeries k) := Chapter13CuspPowerSeriesSubring k
    have hrange : ∀ f : MvPowerSeries (Fin 2) k, E f ∈ S := by
      intro f
      change PowerSeries.coeff 1 (E f) = 0
      exact hcoeff f
    let F : MvPowerSeries (Fin 2) k →+* S := E.codRestrict S hrange
    have hK2coeff : ∀ q : PowerSeries k, ∀ n : ℕ,
        PowerSeries.coeff n (K2 q) =
          if 2 ∣ n then PowerSeries.coeff (n / 2) q else 0 := by
      intro q n
      rw [show K2 q = PowerSeries.subst (PowerSeries.X ^ 2) q by
        simpa [K2] using congrFun (PowerSeries.coe_substAlgHom hX2) q]
      exact PowerSeries.coeff_subst_X_pow (R := k) (S := k) (k := 2)
        (by decide) q n
    have hsurj : Function.Surjective F := by
      intro z
      rcases z with ⟨s, hs⟩
      let even : PowerSeries k := PowerSeries.mk (fun n =>
        PowerSeries.coeff (2 * n) s)
      let odd : PowerSeries k := PowerSeries.mk (fun n =>
        PowerSeries.coeff (2 * n + 3) s)
      have hs1 : PowerSeries.coeff 1 s = 0 := by
        change PowerSeries.coeff 1 s = 0 at hs
        exact hs
      let f : MvPowerSeries (Fin 2) k :=
        J even + MvPowerSeries.X (1 : Fin 2) * J odd
      refine ⟨f, ?_⟩
      apply Subtype.ext
      change E f = s
      have hEX1 : E (MvPowerSeries.X (1 : Fin 2)) =
          (PowerSeries.X : PowerSeries k) ^ 3 := by
        simp [E, MvPowerSeries.coe_eval₂Hom]
      rw [show E f = E (J even) + E (MvPowerSeries.X (1 : Fin 2)) * E (J odd) by
        simp [f]]
      rw [hEJ, hEJ, hEX1]
      have hevenK : ∀ m : ℕ,
          PowerSeries.coeff m (K2 even) =
            if 2 ∣ m then PowerSeries.coeff m s else 0 := by
        intro m
        rw [hK2coeff even m]
        split_ifs with hm
        · obtain ⟨r, rfl⟩ := hm
          simp [even]
        · rfl
      apply PowerSeries.ext
      intro n
      rw [map_add, hevenK, PowerSeries.coeff_X_pow_mul']
      by_cases h2 : 2 ∣ n
      · obtain ⟨m, rfl⟩ := h2
        simp only [dvd_mul_right, if_true]
        by_cases h3 : 3 ≤ 2 * m
        · rw [if_pos h3]
          have hodd : ¬2 ∣ 2 * m - 3 := by
            intro hodd
            obtain ⟨r, hr⟩ := hodd
            omega
          rw [hK2coeff odd (2 * m - 3), if_neg hodd]
          simp
        · simp [h3]
      · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := by
          refine ⟨n / 2, ?_⟩
          omega
        have hodd : ¬2 ∣ 2 * m + 1 := by
          intro hodd
          obtain ⟨r, hr⟩ := hodd
          omega
        simp only [hodd, if_false, zero_add]
        by_cases hm : 3 ≤ 2 * m + 1
        · rw [if_pos hm]
          have hidx : 2 * m + 1 - 3 = 2 * m - 2 := by omega
          rw [hidx, hK2coeff odd (2 * m - 2)]
          have hdiv : 2 ∣ 2 * m - 2 := by
            refine ⟨m - 1, ?_⟩
            omega
          rw [if_pos hdiv]
          simp [odd]
          have hquot : (2 * m - 2) / 2 = m - 1 := by
            apply Nat.div_eq_of_eq_mul_left (by decide)
            omega
          congr 1
          rw [hquot]
          have hm1 : 1 ≤ m := by omega
          have hidx2 : 2 * (m - 1) + 3 = 2 * m + 1 := by
            calc
              2 * (m - 1) + 3 = 2 * (m - 1) + 2 + 1 := by ring
              _ = 2 * ((m - 1) + 1) + 1 := by ring
              _ = 2 * m + 1 := by rw [Nat.sub_add_cancel hm1]
          rw [hidx2]
        · have hm0 : m = 0 := by omega
          subst m
          exact hs1.symm
    let A := MvPowerSeries (Fin 1) k
    let e : MvPowerSeries (Fin 2) k ≃ₐ[k] PowerSeries A :=
      (MvPowerSeries.renameEquiv k (Equiv.swap (0 : Fin 2) 1)).trans
        (MvPowerSeries.finSuccEquiv k 1)
    have hecont : Continuous (e : MvPowerSeries (Fin 2) k → PowerSeries A) := by
      apply continuous_pi_iff.2
      intro n
      apply continuous_pi_iff.2
      intro x
      let d : Fin 2 →₀ ℕ :=
        Finsupp.mapDomain (Equiv.swap (0 : Fin 2) 1) (x.cons (n ()))
      have hcoeffe :
          (fun a : MvPowerSeries (Fin 2) k => e a n x) =
            MvPowerSeries.coeff d := by
        funext a
        have hn : n = Finsupp.single () (n ()) := Finsupp.unique_single n
        rw [hn]
        simp only [e, AlgEquiv.trans_apply]
        change MvPowerSeries.coeff x
            (MvPowerSeries.coeff (Finsupp.single () (n ()))
              ((MvPowerSeries.finSuccEquiv k 1)
                ((MvPowerSeries.renameEquiv k (Equiv.swap (0 : Fin 2) 1)) a))) =
          MvPowerSeries.coeff d a
        rw [← PowerSeries.coeff_def (R := A) (n := n ()) (by simp)]
        rw [MvPowerSeries.coeff_coeff_finSuccEquiv]
        have hd : Finsupp.embDomain
            (Equiv.swap (0 : Fin 2) 1).toEmbedding d = x.cons (n ()) := by
          rw [Finsupp.embDomain_eq_mapDomain]
          rw [← Finsupp.mapDomain_comp]
          have hswap :
              ((Equiv.swap (0 : Fin 2) 1).toEmbedding ∘
                Equiv.swap (0 : Fin 2) 1) = id := by
            funext i
            fin_cases i <;> rfl
          rw [hswap]
          simp
        have hrename := MvPowerSeries.coeff_embDomain_rename
          (Equiv.swap (0 : Fin 2) 1).toEmbedding a d
        rw [hd] at hrename
        simpa [MvPowerSeries.renameEquiv] using hrename
      rw [hcoeffe]
      exact MvPowerSeries.WithPiTopology.continuous_coeff k d
    let g : PowerSeries A :=
      (PowerSeries.X : PowerSeries A) ^ 2 -
        PowerSeries.C ((MvPowerSeries.X (0 : Fin 1) : A) ^ 3)
    have he_relation : e (Chapter13CuspRelation k) = g := by
      simp [e, g, Chapter13CuspRelation, MvPowerSeries.finSuccEquiv]
      rw [show (finSuccEquiv 1) (1 : Fin 2) = some (0 : Fin 1) by rfl,
        MvPowerSeries.optionEquivLeft_X_some]
    let _ : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
      have hlocal := chapter13_power_series_complete_local k (by infer_instance) 1
      simpa [A] using hlocal.1.2
    have hgmap : g.map (IsLocalRing.residue A) ≠ 0 := by
      intro hgzero
      have hcoeff := congrArg (PowerSeries.coeff 2) hgzero
      simp [g] at hcoeff
      have hCpow :
          (PowerSeries.C ((IsLocalRing.residue A) (MvPowerSeries.X (0 : Fin 1))) :
              PowerSeries (IsLocalRing.ResidueField A)) ^ 3 =
            PowerSeries.C (((IsLocalRing.residue A) (MvPowerSeries.X (0 : Fin 1))) ^ 3) := by
        exact ((PowerSeries.C : IsLocalRing.ResidueField A →+*
          PowerSeries (IsLocalRing.ResidueField A)).map_pow _ _).symm
      rw [hCpow, PowerSeries.coeff_C] at hcoeff
      norm_num at hcoeff
    let H : PowerSeries.IsWeierstrassDivisor g :=
      PowerSeries.IsWeierstrassDivisor.of_map_ne_zero hgmap
    let hLsub : MvPowerSeries.HasSubst
        (fun _ : Fin 1 => (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) k)) :=
      MvPowerSeries.HasSubst.X_comp (f := fun _ : Fin 1 => (0 : Fin 2))
    let L : A →ₐ[k] MvPowerSeries (Fin 2) k :=
      MvPowerSeries.substAlgHom hLsub
    have hLcont : Continuous (L : A → MvPowerSeries (Fin 2) k) := by
      change Continuous (MvPowerSeries.substAlgHom hLsub :
        A → MvPowerSeries (Fin 2) k)
      rw [MvPowerSeries.coe_substAlgHom (R := k) (S := k)
        (σ := Fin 1) (τ := Fin 2) hLsub]
      exact MvPowerSeries.continuous_subst (R := k) (S := k)
        (σ := Fin 1) (τ := Fin 2) hLsub
    let φ : A →+* PowerSeries k := E.comp L.toRingHom
    have hφcont : Continuous (φ : A → PowerSeries k) := by
      exact hEcont.comp hLcont
    have hX3 : PowerSeries.HasEval (PowerSeries.X ^ 3 : PowerSeries k) :=
      (PowerSeries.HasSubst.X_pow (by decide)).hasEval
    let E' : PowerSeries A →+* PowerSeries k :=
      PowerSeries.eval₂Hom hφcont hX3
    have hE'cont : Continuous (E' : PowerSeries A → PowerSeries k) := by
      simpa only [E', PowerSeries.coe_eval₂Hom] using
        (PowerSeries.continuous_eval₂ hφcont hX3)
    have hLX0 : L (MvPowerSeries.X (0 : Fin 1) : A) =
        MvPowerSeries.X (0 : Fin 2) := by
      change (MvPowerSeries.substAlgHom hLsub)
          (MvPowerSeries.X (0 : Fin 1)) = _
      rw [MvPowerSeries.substAlgHom_X]
    have heX0 : e (MvPowerSeries.X (0 : Fin 2)) =
        PowerSeries.C (MvPowerSeries.X (0 : Fin 1) : A) := by
      simpa [e] using
        (MvPowerSeries.finSuccEquiv_X_succ (R := k) (n := 1) (j := 0))
    have heX1 : e (MvPowerSeries.X (1 : Fin 2)) =
        (PowerSeries.X : PowerSeries A) := by
      simp only [e, AlgEquiv.trans_apply]
      have hrename :
          MvPowerSeries.renameEquiv k (Equiv.swap (0 : Fin 2) 1)
              (MvPowerSeries.X (1 : Fin 2)) = MvPowerSeries.X 0 := by
        change MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1)
            (MvPowerSeries.X (1 : Fin 2)) = _
        rw [MvPowerSeries.rename_X]
        rfl
      rw [hrename]
      exact MvPowerSeries.finSuccEquiv_X_zero
    have hE'eX0 : E' (e (MvPowerSeries.X (0 : Fin 2))) =
        (PowerSeries.X : PowerSeries k) ^ 2 := by
      rw [heX0]
      rw [show E' (PowerSeries.C (MvPowerSeries.X (0 : Fin 1) : A)) =
          φ (MvPowerSeries.X (0 : Fin 1) : A) by
            simp [E', PowerSeries.coe_eval₂Hom]]
      change E (L (MvPowerSeries.X (0 : Fin 1) : A)) = _
      rw [hLX0]
      simp [E, MvPowerSeries.coe_eval₂Hom]
    have hE'eX1 : E' (e (MvPowerSeries.X (1 : Fin 2))) =
        (PowerSeries.X : PowerSeries k) ^ 3 := by
      rw [heX1]
      simp [E', PowerSeries.coe_eval₂Hom]
    let Cmp : MvPowerSeries (Fin 2) k →+* PowerSeries k :=
      E'.comp e.toRingEquiv.toRingHom
    have hCmpX0 : Cmp (MvPowerSeries.X (0 : Fin 2)) =
        (PowerSeries.X : PowerSeries k) ^ 2 := by
      exact hE'eX0
    have hCmpX1 : Cmp (MvPowerSeries.X (1 : Fin 2)) =
        (PowerSeries.X : PowerSeries k) ^ 3 := by
      exact hE'eX1
    have hCmpcont : Continuous (Cmp : MvPowerSeries (Fin 2) k → PowerSeries k) := by
      exact hE'cont.comp hecont
    have hCmpEq : Cmp = E := by
      have huniq : (Cmp : MvPowerSeries (Fin 2) k → PowerSeries k) =
          MvPowerSeries.eval₂ (algebraMap k (PowerSeries k)) a := by
        apply MvPowerSeries.eval₂_unique (continuous_algebraMap k (PowerSeries k)) ha
          hCmpcont
        intro p
        induction p using MvPolynomial.induction_on with
        | C c =>
            simp [Cmp, e, E', PowerSeries.coe_eval₂Hom]
            rw [MvPowerSeries.finSuccEquiv_C, PowerSeries.eval₂_C]
            have hL_C :
                (MvPowerSeries.substAlgHom hLsub) (MvPowerSeries.C c) =
                  MvPowerSeries.C c := by
              simp
            change E (L (MvPowerSeries.C c)) = PowerSeries.C c
            rw [hL_C]
            simp [E, MvPowerSeries.coe_eval₂Hom]
        | add p q hp hq =>
            rw [MvPolynomial.coe_add, map_add, hp, hq]
            simp
        | mul_X p i hp =>
            rw [MvPolynomial.coe_mul, map_mul, MvPolynomial.coe_X,
              MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
            fin_cases i <;> simp [hCmpX0, hCmpX1, hp]
      apply RingHom.ext
      intro f
      have hf := congrFun huniq f
      simpa [E, MvPowerSeries.coe_eval₂Hom] using hf
    have hE'e : ∀ f : MvPowerSeries (Fin 2) k, E' (e f) = E f := by
      intro f
      change Cmp f = E f
      exact congrArg (fun h : MvPowerSeries (Fin 2) k →+* PowerSeries k => h f) hCmpEq
    have hrel : E (Chapter13CuspRelation k) = 0 := by
      simp only [Chapter13CuspRelation]
      rw [map_sub, map_pow, map_pow]
      simp [E, MvPowerSeries.coe_eval₂Hom]
      ring
    have hspan : Ideal.span {Chapter13CuspRelation k} ≤ RingHom.ker F := by
      apply Ideal.span_le.2
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      change F (Chapter13CuspRelation k) = 0
      apply Subtype.ext
      change E (Chapter13CuspRelation k) = 0
      exact hrel
    have hker : RingHom.ker F ≤ Ideal.span {Chapter13CuspRelation k} := by
      intro f hf
      rw [RingHom.mem_ker] at hf
      have hEf : E f = 0 := congrArg Subtype.val hf
      have hE'f : E' (e f) = 0 := by rw [hE'e, hEf]
      have hEg : E' g = 0 := by
        rw [← he_relation, hE'e]
        exact hrel
      obtain ⟨hrdeg, hdiv⟩ := H.isWeierstrassDivisionAt_div_mod (e f)
      have hdiv' := congrArg E' hdiv
      rw [map_add, map_mul, hEg, zero_mul, hE'f] at hdiv'
      have hEr : E' (H.mod (e f) : PowerSeries A) = 0 := by simpa using hdiv'.symm
      have hX0nonunit : ¬IsUnit (MvPowerSeries.X (0 : Fin 1) : A) := by
        intro hu
        simpa using (MvPowerSeries.isUnit_iff_constantCoeff.mp hu)
      have hX0mem : (MvPowerSeries.X (0 : Fin 1) : A) ∈
          IsLocalRing.maximalIdeal A := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact hX0nonunit
      have hresX0 :
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
              (MvPowerSeries.X (0 : Fin 1) : A) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hX0mem
      have horder :
          (PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) g).order.toNat = 2 := by
        rw [show PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) g =
            (PowerSeries.X : PowerSeries (A ⧸ IsLocalRing.maximalIdeal A)) ^ 2 by
              simp [g, hresX0]]
        rw [PowerSeries.order_X_pow]
        simp
      have hrdeg2 : (H.mod (e f)).degree < 2 := by
        rw [horder] at hrdeg
        exact hrdeg
      let e0 : A →+* PowerSeries k :=
        (PowerSeries.map (MvPowerSeries.isEmptyEquiv (Fin 0) k).toRingHom).comp
          (MvPowerSeries.finSuccEquiv k 0).toRingEquiv.toRingHom
      have he0coeff : ∀ (b : A) (n : ℕ),
          PowerSeries.coeff n (e0 b) =
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) b := by
        intro b n
        simp only [e0, RingHom.coe_comp, Function.comp_apply, PowerSeries.coeff_map]
        change MvPowerSeries.coeff (0 : Fin 0 →₀ ℕ)
            (PowerSeries.coeff n (MvPowerSeries.finSuccEquiv k 0 b)) = _
        rw [MvPowerSeries.coeff_coeff_finSuccEquiv]
        have hcons : Finsupp.cons n 0 = Finsupp.single (0 : Fin 1) n := by
          ext i
          fin_cases i
          simp
        rw [hcons]
      have he0cont : Continuous (e0 : A → PowerSeries k) := by
        apply continuous_pi_iff.2
        intro n
        rw [show (fun b : A => e0 b n) =
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) (n ())) by
              funext b
              have hn : n = Finsupp.single () (n ()) := Finsupp.unique_single n
              rw [hn]
              change PowerSeries.coeff (n ()) (e0 b) = _
              simpa using he0coeff b (n ())]
        exact MvPowerSeries.WithPiTopology.continuous_coeff k
          (Finsupp.single (0 : Fin 1) (n ()))
      have he0X : e0 (MvPowerSeries.X (0 : Fin 1) : A) = PowerSeries.X := by
        change PowerSeries.map (MvPowerSeries.isEmptyEquiv (Fin 0) k).toRingHom
            (MvPowerSeries.finSuccEquiv k 0 (MvPowerSeries.X (0 : Fin 1))) =
          PowerSeries.X
        rw [MvPowerSeries.finSuccEquiv_X_zero, PowerSeries.map_X]
      have he0inj : Function.Injective e0 := by
        intro b c hbc
        apply (MvPowerSeries.finSuccEquiv k 0).injective
        apply PowerSeries.map_injective
          (MvPowerSeries.isEmptyEquiv (Fin 0) k).toRingHom
          (MvPowerSeries.isEmptyEquiv (Fin 0) k).injective
        exact hbc
      have hK2cont : Continuous (K2 : PowerSeries k → PowerSeries k) := by
        rw [← hcomp]
        exact hEalgcont.comp hJcont
      let e2 : A →+* PowerSeries k := K2.toRingHom.comp e0
      have he2cont : Continuous (e2 : A → PowerSeries k) :=
        hK2cont.comp he0cont
      have ha0 : MvPowerSeries.HasEval
          (fun _ : Fin 1 => (PowerSeries.X : PowerSeries k) ^ 2) := by
        refine ⟨?_, ?_⟩
        · intro i
          fin_cases i
          exact hX2.hasEval
        · rw [Filter.cofinite_eq_bot]
          exact Filter.tendsto_bot
      have hφX : φ (MvPowerSeries.X (0 : Fin 1) : A) =
          (PowerSeries.X : PowerSeries k) ^ 2 := by
        change E (L (MvPowerSeries.X (0 : Fin 1) : A)) = _
        rw [hLX0]
        simp [E, MvPowerSeries.coe_eval₂Hom]
      have he2X : e2 (MvPowerSeries.X (0 : Fin 1) : A) =
          (PowerSeries.X : PowerSeries k) ^ 2 := by
        change K2 (e0 (MvPowerSeries.X (0 : Fin 1) : A)) = _
        rw [he0X]
        simpa [K2] using (PowerSeries.substAlgHom_X hX2)
      have hφC : ∀ c : k,
          φ (MvPowerSeries.C c : A) = PowerSeries.C c := by
        intro c
        change E (L (MvPowerSeries.C c : A)) = PowerSeries.C c
        have hL_C : L (MvPowerSeries.C c : A) = MvPowerSeries.C c := by
          simpa [A, MvPowerSeries.algebraMap_apply] using L.commutes c
        rw [hL_C]
        simp [E, MvPowerSeries.coe_eval₂Hom]
      have he0C : ∀ c : k,
          e0 (MvPowerSeries.C c : A) = PowerSeries.C c := by
        intro c
        apply PowerSeries.ext
        intro n
        rw [he0coeff]
        by_cases hn : n = 0
        · subst n
          simp [MvPowerSeries.coeff_C, PowerSeries.coeff_C]
        · simp [hn, MvPowerSeries.coeff_C, PowerSeries.coeff_C]
      have he2C : ∀ c : k,
          e2 (MvPowerSeries.C c : A) = PowerSeries.C c := by
        intro c
        change K2 (e0 (MvPowerSeries.C c : A)) = PowerSeries.C c
        rw [he0C]
        rw [show K2 (PowerSeries.C c) =
            PowerSeries.subst ((PowerSeries.X : PowerSeries k) ^ 2)
              (PowerSeries.C c) by
                simp [K2, PowerSeries.coe_substAlgHom]]
        change (PowerSeries.C c : PowerSeries k).subst
            ((PowerSeries.X : PowerSeries k) ^ 2) = PowerSeries.C c
        rw [PowerSeries.subst_C]
        exact PowerSeries.C_apply.symm
      have hφeval : (φ : A → PowerSeries k) =
          MvPowerSeries.eval₂ (algebraMap k (PowerSeries k))
            (fun _ : Fin 1 => (PowerSeries.X : PowerSeries k) ^ 2) := by
        apply MvPowerSeries.eval₂_unique (continuous_algebraMap k (PowerSeries k))
          ha0 hφcont
        intro p
        induction p using MvPolynomial.induction_on with
        | C c =>
            rw [MvPolynomial.coe_C]
            simpa only [MvPolynomial.eval₂_C, PowerSeries.C_eq_algebraMap] using hφC c
        | add p q hp hq =>
            rw [MvPolynomial.coe_add, map_add, hp, hq]
            simp
        | mul_X p i hp =>
            rw [MvPolynomial.coe_mul, map_mul, MvPolynomial.coe_X,
              MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
            fin_cases i; simp [hφX, hp]
      have he2eval : (e2 : A → PowerSeries k) =
          MvPowerSeries.eval₂ (algebraMap k (PowerSeries k))
            (fun _ : Fin 1 => (PowerSeries.X : PowerSeries k) ^ 2) := by
        apply MvPowerSeries.eval₂_unique (continuous_algebraMap k (PowerSeries k))
          ha0 he2cont
        intro p
        induction p using MvPolynomial.induction_on with
        | C c =>
            rw [MvPolynomial.coe_C]
            simpa only [MvPolynomial.eval₂_C, PowerSeries.C_eq_algebraMap] using he2C c
        | add p q hp hq =>
            rw [MvPolynomial.coe_add, map_add, hp, hq]
            simp
        | mul_X p i hp =>
            rw [MvPolynomial.coe_mul, map_mul, MvPolynomial.coe_X,
              MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
            fin_cases i; simp [he2X, hp]
      have hφe2 : φ = e2 := by
        apply RingHom.ext
        intro b
        exact (congrFun hφeval b).trans (congrFun he2eval b).symm
      have hK2inj : Function.Injective (K2 : PowerSeries k → PowerSeries k) := by
        intro q q' hqq'
        apply PowerSeries.ext
        intro n
        have hcoeff := congrArg (PowerSeries.coeff (2 * n)) hqq'
        simpa [hK2coeff] using hcoeff
      have he2inj : Function.Injective (e2 : A → PowerSeries k) :=
        hK2inj.comp he0inj
      have hφinj : Function.Injective (φ : A → PowerSeries k) := by
        rw [hφe2]
        exact he2inj
      have hφcoeff : ∀ b : A, ∀ n : ℕ,
          PowerSeries.coeff n (φ b) =
            if 2 ∣ n then PowerSeries.coeff (n / 2) (e0 b) else 0 := by
        intro b n
        have hb : φ b = K2 (e0 b) := by
          rw [hφe2]
          rfl
        rw [hb, hK2coeff]
      let r : Polynomial A := H.mod (e f)
      have hrdeg' : r.degree < 2 := by
        simpa [r] using hrdeg2
      have hrdeg1 : r.degree ≤ (1 : WithBot ℕ) := by
        rw [Polynomial.degree_le_iff_coeff_zero]
        intro n hn
        have hn' : 1 < n := by exact_mod_cast hn
        exact (Polynomial.degree_lt_iff_coeff_zero r 2).mp hrdeg' n (by omega)
      have hrpoly : r = Polynomial.C (r.coeff 1) * Polynomial.X +
          Polynomial.C (r.coeff 0) :=
        Polynomial.eq_X_add_C_of_degree_le_one hrdeg1
      have hEr' : E' (r : PowerSeries A) = 0 := by
        simpa [r] using hEr
      have hErpoly : Polynomial.eval₂ φ (PowerSeries.X ^ 3) r = 0 := by
        simpa [E', PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_coe] using hEr'
      rw [hrpoly] at hErpoly
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_X] at hErpoly
      have he0r0 : e0 (r.coeff 0) = 0 := by
        apply PowerSeries.ext
        intro n
        have hc := congrArg (PowerSeries.coeff (2 * n)) hErpoly
        rw [map_add, PowerSeries.coeff_mul_X_pow'] at hc
        by_cases h3 : 3 ≤ 2 * n
        · have hodd : ¬2 ∣ (2 * n - 3) := by
            intro hd
            obtain ⟨m, hm⟩ := hd
            omega
          simpa [h3, hodd, hφcoeff] using hc
        · simpa [h3, hφcoeff] using hc
      have he0r1 : e0 (r.coeff 1) = 0 := by
        apply PowerSeries.ext
        intro n
        have hc := congrArg (PowerSeries.coeff (2 * n + 3)) hErpoly
        rw [map_add, PowerSeries.coeff_mul_X_pow'] at hc
        have hodd : ¬2 ∣ (2 * n + 3) := by
          intro hd
          obtain ⟨m, hm⟩ := hd
          omega
        simpa [hφcoeff, hodd] using hc
      have hr0 : r.coeff 0 = 0 := by
        apply he0inj
        simpa using he0r0
      have hr1 : r.coeff 1 = 0 := by
        apply he0inj
        simpa using he0r1
      have hrzero : r = 0 := by
        rw [hrpoly, hr0, hr1]
        simp
      have hediv : e f = g * PowerSeries.IsWeierstrassDivisorAt.div H (e f) := by
        simpa [r, hrzero] using hdiv
      apply Ideal.mem_span_singleton.mpr
      refine ⟨e.symm (PowerSeries.IsWeierstrassDivisorAt.div H (e f)), ?_⟩
      have hf_eq : f = Chapter13CuspRelation k *
          e.symm (PowerSeries.IsWeierstrassDivisorAt.div H (e f)) := by
        apply e.injective
        rw [map_mul, he_relation, e.apply_symm_apply]
        exact hediv
      exact hf_eq
    have hquot : RingHom.ker F = Ideal.span {Chapter13CuspRelation k} :=
      le_antisymm hker hspan
    exact ⟨(Ideal.quotEquivOfEq hquot.symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)⟩
  · intro hreg
    let S := Chapter13CuspPowerSeriesSubring k
    let : IsLocalRing S := hreg.toIsLocalRing
    let : IsNoetherianRing S := hreg.toIsNoetherian
    let : IsDomain S :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.cusp_power_series_is_complete_one_dimensional_non_normal k |>.1
    have hdim : ringKrullDim S = 1 :=
      by simpa [S] using
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.cusp_power_series_is_complete_one_dimensional_non_normal k |>.2.2.2.1
    have hspan' :
        (↑(IsLocalRing.maximalIdeal S).spanFinrank : WithBot ℕ∞) = 1 := by
      calc
        (↑(IsLocalRing.maximalIdeal S).spanFinrank : WithBot ℕ∞) = ringKrullDim S :=
          hreg.spanFinrank_maximalIdeal
        _ = 1 := hdim
    have hspan : (IsLocalRing.maximalIdeal S).spanFinrank = 1 := by
      exact_mod_cast hspan'
    have hcot : Module.finrank (ResidueField S) (CotangentSpace S) = 1 := by
      rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
        hspan]
    exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.cusp_power_series_is_not_a_dvr k
      ((IsLocalRing.finrank_CotangentSpace_eq_one_iff).mp hcot)

/-! ### Mixed-characteristic examples -/

abbrev Chapter13PrimeSquareRing (p : ℕ) := ZMod (p ^ 2)

instance chapter13PrimeSquareLocalRing
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalRing (Chapter13PrimeSquareRing p) := by
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp2 : 1 < p ^ 2 := by
    calc
      1 < 2 * 2 := by decide
      _ ≤ p * p := Nat.mul_le_mul hp hp
      _ = p ^ 2 := by simp [pow_two]
  let : Fact (1 < p ^ 2) := ⟨hp2⟩
  exact @IsLocalRing.of_surjective' (PadicInt p) (ZMod (p ^ 2)) _ _ _
    inferInstance (PadicInt.toZModPow 2) (ZMod.ringHom_surjective _)

theorem chapter13_prime_square_has_no_coefficient_field
    (p : ℕ) [Fact (Nat.Prime p)] :
    Chapter13CompleteNoetherianLocalRing (Chapter13PrimeSquareRing p) ∧
      Chapter13MixedCharacteristic (Chapter13PrimeSquareRing p) p ∧
      ¬Chapter13ContainsField (Chapter13PrimeSquareRing p) ∧
      Chapter13IsCohenRing (PadicInt p) (ZMod p) p ∧
      Function.Surjective (@PadicInt.toZModPow p _ 2) := by
  let A := Chapter13PrimeSquareRing p
  have hp : Nat.Prime p := Fact.out
  have hp2 : 1 < p ^ 2 := by
    calc
      1 < 2 * 2 := by decide
      _ ≤ p * p := Nat.mul_le_mul hp.two_le hp.two_le
      _ = p ^ 2 := by simp [pow_two]
  have hdiv : p ∣ p ^ 2 := by
    refine ⟨p, ?_⟩
    simp [pow_two]
  let q : A →+* ZMod p := ZMod.castHom hdiv (ZMod p)
  have hqsurj : Function.Surjective q := by
    simpa [q] using (ZMod.castHom_surjective hdiv)
  have hker : RingHom.ker q = IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal q hqsurj
  let e : Chapter13ResidueRing A ≃+* ZMod p :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hqsurj)
  have hres : CharP (Chapter13ResidueRing A) p := by
    exact (e.symm.toRingHom.charP_iff_charP p).mp (ZMod.charP p)
  have hnonzero : (p : A) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hlt : p < p ^ 2 := by
      rw [pow_two]
      simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt
        (Nat.zero_lt_of_lt hp.two_le)
    exact (Nat.not_dvd_of_pos_of_lt (Nat.zero_lt_of_lt hp.two_le) hlt) h
  have hnonunit : ¬IsUnit (p : A) := by
    intro hu
    have hq : IsUnit (q (p : A)) := IsUnit.map q hu
    have hqp : q (p : A) = 0 := by
      change ZMod.castHom hdiv (ZMod p) (p : ZMod (p ^ 2)) = 0
      rw [map_natCast]
      simp
    exact hq.ne_zero hqp
  have hnotchar : ¬CharP A p := by
    intro hchar
    exact hnonzero (@CharP.cast_eq_zero A _ p hchar)
  have hcontains : ¬Chapter13ContainsField A := by
    rintro ⟨K⟩
    have hpK : (p : K.carrier) ≠ 0 := by
      intro hpK
      apply hnonzero
      exact congrArg K.carrier.subtype hpK
    have huK : IsUnit (p : K.carrier) :=
      (@isUnit_iff_ne_zero K.carrier
        (@Field.toSemifield K.carrier K.field_carrier.toField).toCommGroupWithZero.toGroupWithZero).mpr hpK
    have huA : IsUnit (p : A) := by
      simpa using IsUnit.map K.carrier.subtype huK
    exact hnonunit huA
  refine ⟨?_, ⟨hp, hres, hnotchar⟩, hcontains, ?_, ?_⟩
  · exact ⟨inferInstance, inferInstance⟩
  · exact chapter13_padic_integers_are_cohen p
  · exact ZMod.ringHom_surjective _

theorem chapter13_padic_integers_have_no_subfield
    (p : ℕ) [Fact (Nat.Prime p)] :
    ¬Chapter13ContainsField (PadicInt p) := by
  rintro ⟨K⟩
  let : Field K.carrier := K.field_carrier.toField
  have hp0 : (p : K.carrier) ≠ 0 := by
    intro hp
    have hp' : (p : PadicInt p) = 0 := congrArg K.carrier.subtype hp
    have hpne : (p : PadicInt p) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    exact hpne hp'
  have hu : IsUnit (p : K.carrier) := isUnit_iff_ne_zero.mpr hp0
  have hu' : IsUnit (p : PadicInt p) := by
    simpa using IsUnit.map K.carrier.subtype hu
  apply (IsLocalRing.notMem_maximalIdeal.mpr hu')
  exact (IsLocalRing.mem_maximalIdeal _).mpr PadicInt.p_nonunit

abbrev Chapter13PadicPowerSeries (p : ℕ) [Fact (Nat.Prime p)] :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04PadicPowerSeries p

abbrev Chapter13PadicPowerSeriesMaximalIdeal
    (p : ℕ) [Fact (Nat.Prime p)] : Ideal (Chapter13PadicPowerSeries p) :=
  LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.chapter04PadicPowerSeriesMaximalIdeal p

theorem chapter13_padic_power_series_is_unramified_regular
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsAdicComplete (Chapter13PadicPowerSeriesMaximalIdeal p)
        (Chapter13PadicPowerSeries p) ∧
      IsRegularLocalRing (Chapter13PadicPowerSeries p) ∧
      ringKrullDim (Chapter13PadicPowerSeries p) = 2 ∧
      (p : Chapter13PadicPowerSeries p) ∉
        (IsLocalRing.maximalIdeal (Chapter13PadicPowerSeries p)) ^ 2 ∧
      Chapter13MixedCharacteristic (Chapter13PadicPowerSeries p) p ∧
      ¬Chapter13ContainsField (Chapter13PadicPowerSeries p) := by
  let A := Chapter13PadicPowerSeries p
  let M := Chapter13PadicPowerSeriesMaximalIdeal p
  have h04 :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.padic_power_series_is_complete_regular_local_two_dimensional p
  have hM : M = Ideal.span
      ({PowerSeries.C (p : PadicInt p), PowerSeries.X} : Set A) := by
    rfl
  have hp0 : (p : PadicInt p) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hnotpow : (p : PadicInt p) ∉
      (Ideal.span {(p : PadicInt p)}) ^ 2 := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨a, ha⟩
    have hpa : (p : PadicInt p) * a = 1 := by
      apply (mul_left_cancel₀ hp0)
      simpa [pow_two, mul_assoc] using ha.symm
    exact (mem_nonunits_iff.mp PadicInt.p_nonunit)
      (IsUnit.of_mul_eq_one a hpa)
  have hnotm : (p : A) ∉ M ^ 2 := by
    intro hpM
    let c : A →+* PadicInt p := PowerSeries.constantCoeff
    have hc : Ideal.map c (M ^ 2) ≤
        (Ideal.span {(p : PadicInt p)}) ^ 2 := by
      rw [Ideal.map_pow]
      apply Ideal.pow_right_mono
      rw [hM, Ideal.map_span]
      apply Ideal.span_le.2
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases Set.mem_insert_iff.mp hz with hz | hz
      · rw [Set.mem_singleton_iff.mp hz]
        simp [c]
      · rw [Set.mem_singleton_iff.mp hz]
        rw [PowerSeries.constantCoeff_X]
        exact Ideal.zero_mem _
    apply hnotpow
    apply hc
    exact Ideal.mem_map_of_mem c hpM
  have hker : RingHom.ker (PadicInt.toZMod.comp
      (PowerSeries.constantCoeff : A →+* PadicInt p)) = M := by
    apply le_antisymm
    · intro f hf
      change PadicInt.toZMod (PowerSeries.constantCoeff f) = 0 at hf
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod] at hf
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hf
      obtain ⟨a, ha⟩ := hf
      rw [hM, PowerSeries.eq_X_mul_shift_add_const f, ha]
      apply Ideal.add_mem
      · exact M.mul_mem_right _ (Ideal.subset_span (by simp))
      · rw [map_mul]
        exact M.mul_mem_right _ (Ideal.subset_span (by simp))
    · rw [hM]
      apply Ideal.span_le.2
      intro y hy
      rcases hy with rfl | rfl
      · simp [RingHom.mem_ker]
      · change PadicInt.toZMod (PowerSeries.constantCoeff PowerSeries.X) = 0
        rw [PowerSeries.constantCoeff_X, map_zero]
  have hsurj : Function.Surjective
      (PadicInt.toZMod.comp
        (PowerSeries.constantCoeff : A →+* PadicInt p)) := by
    intro y
    obtain ⟨z, hz⟩ := ZMod.ringHom_surjective (PadicInt.toZMod :
      PadicInt p →+* ZMod p) y
    refine ⟨PowerSeries.C z, ?_⟩
    change PadicInt.toZMod z = y
    exact hz
  have hmax : IsLocalRing.maximalIdeal A = M := h04.2.2.2.1
  let e : Chapter13ResidueRing A ≃+* ZMod p :=
    (Ideal.quotEquivOfEq (hmax.trans hker.symm)).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)
  have hreschar : CharP (Chapter13ResidueRing A) p := by
    exact (e.symm.toRingHom.charP_iff_charP p).mp (ZMod.charP p)
  have hcharA : ¬CharP A p := by
    intro h
    let : CharP A p := h
    have hz : (p : A) = 0 := CharP.cast_eq_zero A p
    have hz' : (p : PadicInt p) = 0 := by
      simpa only [map_natCast, map_zero] using
        congrArg PowerSeries.constantCoeff hz
    exact hp0 hz'
  have hcontains : ¬Chapter13ContainsField A := by
    rintro ⟨K⟩
    let : Field K.carrier := K.field_carrier.toField
    have hpa0 : (p : A) ≠ 0 := by
      intro h
      have h' := congrArg PowerSeries.constantCoeff h
      exact hp0 (by simpa only [map_natCast, map_zero] using h')
    have hpK : (p : K.carrier) ≠ 0 := by
      intro h
      exact hpa0 (congrArg K.carrier.subtype h)
    have hu : IsUnit (p : A) := by
      simpa using IsUnit.map K.carrier.subtype
        (isUnit_iff_ne_zero.mpr hpK)
    exact (mem_nonunits_iff.mp PadicInt.p_nonunit)
      (by simpa using PowerSeries.isUnit_iff_constantCoeff.mp hu)
  have hnotmax : (p : A) ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
    rw [hmax]
    exact hnotm
  refine ⟨h04.1, h04.2.1, h04.2.2.1, hnotmax,
    ⟨(Fact.out : Nat.Prime p), hreschar, hcharA⟩, hcontains⟩

/-- The Eisenstein polynomial obtained from `((1 + X)^p - 1) / X`. -/
def Chapter13CyclotomicEisensteinPolynomial
    (p : ℕ) [Fact (Nat.Prime p)] : Polynomial (PadicInt p) :=
  ((Polynomial.X + 1) ^ p - 1) /ₘ Polynomial.X

abbrev Chapter13CyclotomicOrder
    (p : ℕ) [Fact (Nat.Prime p)] :=
  Polynomial (PadicInt p) ⧸
    Ideal.span {Chapter13CyclotomicEisensteinPolynomial p}

instance chapter13CyclotomicOrderLocalRing
    (p : ℕ) [Fact (Nat.Prime p)] : IsLocalRing (Chapter13CyclotomicOrder p) := by
  let f : Polynomial (PadicInt p) :=
    ((Polynomial.cyclotomic p (PadicInt p)).comp (Polynomial.X + 1))
  have hmonic : f.Monic := by
    simpa [f] using (Polynomial.cyclotomic.monic p (PadicInt p)).comp
      (Polynomial.monic_X_add_C 1) (by
        rw [Polynomial.natDegree_X_add_C]
        exact Nat.one_ne_zero)
  have hE0 := (cyclotomic_comp_X_add_one_isEisensteinAt p).isWeaklyEisensteinAt.map
    (Int.castRingHom (PadicInt p))
  have hE : f.IsWeaklyEisensteinAt
      (Ideal.span {(p : PadicInt p)}) := by
    simpa [f, Ideal.map_span, Polynomial.map_comp,
      Polynomial.map_cyclotomic_int] using hE0
  let : Module.Finite (PadicInt p) (AdjoinRoot f) :=
    hmonic.finite_adjoinRoot
  let : Algebra.IsIntegral (PadicInt p) (AdjoinRoot f) :=
    Algebra.IsIntegral.of_finite (R := PadicInt p) (B := AdjoinRoot f)
  have hqroot :
      f.eval₂ (PadicInt.toZMod : PadicInt p →+* ZMod p) 0 = 0 := by
    simp [f, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.cyclotomic_prime, Polynomial.eval_finsetSum]
  let q : AdjoinRoot f →+* ZMod p :=
    AdjoinRoot.lift (f := f) (PadicInt.toZMod : PadicInt p →+* ZMod p) 0 hqroot
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨a, ha⟩ := ZMod.ringHom_surjective
      (PadicInt.toZMod : PadicInt p →+* ZMod p) y
    refine ⟨AdjoinRoot.of f a, ?_⟩
    simpa [q] using ha
  let : Nontrivial (AdjoinRoot f) := hqsurj.nontrivial
  let N : Ideal (AdjoinRoot f) :=
    Ideal.map (AdjoinRoot.of f : PadicInt p →+* AdjoinRoot f)
        (Ideal.span {(p : PadicInt p)}) ⊔
      Ideal.span {AdjoinRoot.root f}
  have hker : RingHom.ker q = N := by
    apply le_antisymm
    · intro z hz
      induction z using AdjoinRoot.induction_on with
      | ih g =>
          have hqg : PadicInt.toZMod (g.coeff 0) = 0 := by
            simpa [q, AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero] using hz
          have hcg : g.coeff 0 ∈ Ideal.span {(p : PadicInt p)} := by
            rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
            exact RingHom.mem_ker.mpr hqg
          have hmap :
              Ideal.map (AdjoinRoot.of f : PadicInt p →+*
                AdjoinRoot f) (Ideal.span {(p : PadicInt p)}) ≤ N := by
            exact le_sup_left
          have hdiv := Polynomial.divX_mul_X_add g
          rw [← hdiv, map_add]
          apply N.add_mem
          · have hmul := (AdjoinRoot.mk f).map_mul
                (Polynomial.divX g) Polynomial.X
            rw [hmul, AdjoinRoot.mk_X]
            have hrootN : AdjoinRoot.root f ∈ N := by
              change AdjoinRoot.root f ∈
                Ideal.map (AdjoinRoot.of f : PadicInt p →+* AdjoinRoot f)
                    (Ideal.span {(p : PadicInt p)}) ⊔
                  Ideal.span {AdjoinRoot.root f}
              exact (le_sup_right : Ideal.span
                ({AdjoinRoot.root f} : Set (AdjoinRoot f)) ≤
                  Ideal.map (AdjoinRoot.of f : PadicInt p →+* AdjoinRoot f)
                      (Ideal.span {(p : PadicInt p)}) ⊔
                    Ideal.span {AdjoinRoot.root f})
                (Ideal.subset_span (Set.mem_singleton _))
            exact N.mul_mem_left _ hrootN
          · change AdjoinRoot.of f (g.coeff 0) ∈ N
            exact hmap (Ideal.mem_map_of_mem _ hcg)
    · rw [show N =
        Ideal.map (AdjoinRoot.of f : PadicInt p →+* AdjoinRoot f)
          (Ideal.span {(p : PadicInt p)}) ⊔
          Ideal.span {AdjoinRoot.root f} by rfl]
      apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker]
        have ha0 : PadicInt.toZMod a = 0 := by
          rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
            PadicInt.maximalIdeal_eq_span_p]
          exact ha
        simpa [q] using ha0
      · apply Ideal.span_le.2
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        simp [q, AdjoinRoot.lift_root]
  have hNmax : N.IsMaximal := by
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective q hqsurj
  have hlocal : IsLocalRing (AdjoinRoot f) := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨N, hNmax, ?_⟩
    intro Q hQ
    let : Q.IsMaximal := hQ
    have hQbase :
        (Q.comap (algebraMap (PadicInt p) (AdjoinRoot f))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
    have hQbaseeq :
        Q.comap (algebraMap (PadicInt p) (AdjoinRoot f)) =
          IsLocalRing.maximalIdeal (PadicInt p) :=
      IsLocalRing.eq_maximalIdeal hQbase
    have hmapP :
        Ideal.map (algebraMap (PadicInt p) (AdjoinRoot f))
            (Ideal.span {(p : PadicInt p)}) ≤ Q := by
      rw [Ideal.map_le_iff_le_comap, hQbaseeq,
        PadicInt.maximalIdeal_eq_span_p]
    have hx : Polynomial.aeval (AdjoinRoot.root f) f = 0 := by
      change f.eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) = 0
      exact AdjoinRoot.eval₂_root f
    have hrootpow :
        (AdjoinRoot.root f) ^ f.natDegree ∈
          Ideal.map (algebraMap (PadicInt p) (AdjoinRoot f))
            (Ideal.span {(p : PadicInt p)}) := by
      have h := hE.pow_natDegree_le_of_aeval_zero_of_monic_mem_map
        hx hmonic f.natDegree (by
          rw [hmonic.natDegree_map])
      exact h
    have hrootQ : AdjoinRoot.root f ∈ Q :=
      hQ.isPrime.mem_of_pow_mem _ (hmapP hrootpow)
    have hNQ : N ≤ Q := by
      apply sup_le
      · simpa [AdjoinRoot.algebraMap_eq] using hmapP
      · exact Ideal.span_le.2 (by
          intro z hz
          rw [Set.mem_singleton_iff.mp hz]
          exact hrootQ)
    exact (hNmax.eq_of_le hQ.ne_top hNQ).symm
  have hf : f = Chapter13CyclotomicEisensteinPolynomial p := by
    have hdiv : Polynomial.X * Chapter13CyclotomicEisensteinPolynomial p =
        (Polynomial.X + 1) ^ p - 1 := by
      simpa [Chapter13CyclotomicEisensteinPolynomial] using
        (Polynomial.mul_divByMonic_eq_iff_isRoot
        (p := (Polynomial.X + 1) ^ p - 1) (a := (0 : PadicInt p))).2 (by simp)
    have hcomp : Polynomial.X * f = (Polynomial.X + 1) ^ p - 1 := by
      have h := congrArg (fun q : Polynomial (PadicInt p) =>
          q.comp (Polynomial.X + 1))
        (Polynomial.cyclotomic_prime_mul_X_sub_one (PadicInt p) p)
      simpa [f, mul_comm] using h
    apply (mul_left_cancel₀ Polynomial.X_ne_zero)
    exact hcomp.trans hdiv.symm
  have hcoeff : f.coeff 0 = (p : PadicInt p) := by
    simp [f, Polynomial.coeff_zero_eq_eval_zero, Polynomial.cyclotomic_prime,
      Polynomial.eval_finsetSum]
  let e : AdjoinRoot f ≃+* Chapter13CyclotomicOrder p :=
    Ideal.quotEquivOfEq (congrArg (fun q : Polynomial (PadicInt p) =>
      Ideal.span ({q} : Set (Polynomial (PadicInt p)))) hf)
  let : IsLocalRing (AdjoinRoot f) := hlocal
  exact e.isLocalRing

instance chapter13CyclotomicOrderDomain
    (p : ℕ) [Fact (Nat.Prime p)] : IsDomain (Chapter13CyclotomicOrder p) := by
  let f : Polynomial (PadicInt p) :=
    ((Polynomial.cyclotomic p (PadicInt p)).comp (Polynomial.X + 1))
  have hf : f = Chapter13CyclotomicEisensteinPolynomial p := by
    have hdiv : Polynomial.X * Chapter13CyclotomicEisensteinPolynomial p =
        (Polynomial.X + 1) ^ p - 1 := by
      simpa [Chapter13CyclotomicEisensteinPolynomial] using
        (Polynomial.mul_divByMonic_eq_iff_isRoot
        (p := (Polynomial.X + 1) ^ p - 1) (a := (0 : PadicInt p))).2 (by simp)
    have hcomp : Polynomial.X * f = (Polynomial.X + 1) ^ p - 1 := by
      have h := congrArg (fun q : Polynomial (PadicInt p) =>
          q.comp (Polynomial.X + 1))
        (Polynomial.cyclotomic_prime_mul_X_sub_one (PadicInt p) p)
      simpa [f, mul_comm] using h
    apply (mul_left_cancel₀ Polynomial.X_ne_zero)
    exact hcomp.trans hdiv.symm
  have hE : f.IsEisensteinAt (Ideal.span {(p : PadicInt p)}) := by
    have hE0 := (cyclotomic_comp_X_add_one_isEisensteinAt p).isWeaklyEisensteinAt.map
      (Int.castRingHom (PadicInt p))
    have hweak : f.IsWeaklyEisensteinAt
        (Ideal.span {(p : PadicInt p)}) := by
      simpa [f, Ideal.map_span, Polynomial.map_comp,
        Polynomial.map_cyclotomic_int] using hE0
    refine Polynomial.Monic.isEisensteinAt_of_mem_of_notMem ?_ ?_ hweak.mem ?_
    · simpa [f] using (Polynomial.cyclotomic.monic p (PadicInt p)).comp
        (Polynomial.monic_X_add_C 1) (by
          rw [Polynomial.natDegree_X_add_C]
          exact Nat.one_ne_zero)
    · exact Ideal.span_singleton_ne_top (mem_nonunits_iff.mp PadicInt.p_nonunit)
    · have hcoeff : f.coeff 0 = (p : PadicInt p) := by
        simp [f, Polynomial.coeff_zero_eq_eval_zero, Polynomial.cyclotomic_prime,
          Polynomial.eval_finsetSum]
      rw [hcoeff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨a, ha⟩
      have hp0 : (p : PadicInt p) ≠ 0 := by
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      have hpa : (p : PadicInt p) * a = 1 := by
        apply (mul_left_cancel₀ hp0)
        simpa [pow_two, mul_assoc] using ha.symm
      exact (mem_nonunits_iff.mp PadicInt.p_nonunit)
        (IsUnit.of_mul_eq_one a hpa)
  have hprime : Prime f := by
    have hmonic : f.Monic := by
      simpa [f] using (Polynomial.cyclotomic.monic p (PadicInt p)).comp
        (Polynomial.monic_X_add_C 1) (by
          rw [Polynomial.natDegree_X_add_C]
          exact Nat.one_ne_zero)
    have hcoeff : f.coeff 0 = (p : PadicInt p) := by
      simp [f, Polynomial.coeff_zero_eq_eval_zero, Polynomial.cyclotomic_prime,
        Polynomial.eval_finsetSum]
    have hdegree : 0 < f.natDegree := hmonic.natDegree_pos.mpr (by
      intro h
      have hc := congrArg (fun q : Polynomial (PadicInt p) => q.coeff 0) h
      rw [hcoeff] at hc
      have hu : IsUnit (p : PadicInt p) := by
        rw [show (p : PadicInt p) = 1 by simpa using hc]
        exact isUnit_one
      exact (mem_nonunits_iff.mp PadicInt.p_nonunit) hu)
    have hP : (Ideal.span {(p : PadicInt p)}).IsPrime := by
      apply (Ideal.span_singleton_prime (by
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)).2
      exact PadicInt.prime_p
    exact (hE.irreducible hP hmonic.isPrimitive hdegree).prime
  have : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hprime
  let e : AdjoinRoot f ≃+* Chapter13CyclotomicOrder p :=
    Ideal.quotEquivOfEq (congrArg (fun q : Polynomial (PadicInt p) =>
      Ideal.span ({q} : Set (Polynomial (PadicInt p)))) hf)
  exact e.symm.toMulEquiv.isDomain

theorem chapter13_cyclotomic_order_is_ramified
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 2 < p) :
    IsAdicComplete (IsLocalRing.maximalIdeal (Chapter13CyclotomicOrder p))
        (Chapter13CyclotomicOrder p) ∧
      IsRegularLocalRing (Chapter13CyclotomicOrder p) ∧
      IsDiscreteValuationRing (Chapter13CyclotomicOrder p) ∧
      ringKrullDim (Chapter13CyclotomicOrder p) = 1 ∧
      (p : Chapter13CyclotomicOrder p) ∈
        (IsLocalRing.maximalIdeal (Chapter13CyclotomicOrder p)) ^ 2 ∧
      ¬Chapter13IsCohenRing (Chapter13CyclotomicOrder p) (ZMod p) p := by
  classical
  let f : Polynomial (PadicInt p) :=
    ((Polynomial.cyclotomic p (PadicInt p)).comp (Polynomial.X + 1))
  have hmonic : f.Monic := by
    simpa [f] using (Polynomial.cyclotomic.monic p (PadicInt p)).comp
      (Polynomial.monic_X_add_C 1) (by
        rw [Polynomial.natDegree_X_add_C]
        exact Nat.one_ne_zero)
  have hE0 := (cyclotomic_comp_X_add_one_isEisensteinAt p).isWeaklyEisensteinAt.map
    (Int.castRingHom (PadicInt p))
  have hweak : f.IsWeaklyEisensteinAt
      (Ideal.span {(p : PadicInt p)}) := by
    simpa [f, Ideal.map_span, Polynomial.map_comp,
      Polynomial.map_cyclotomic_int] using hE0
  have hE : f.IsEisensteinAt (Ideal.span {(p : PadicInt p)}) := by
    refine Polynomial.Monic.isEisensteinAt_of_mem_of_notMem hmonic ?_ hweak.mem ?_
    · exact Ideal.span_singleton_ne_top (mem_nonunits_iff.mp PadicInt.p_nonunit)
    · have hcoeff : f.coeff 0 = (p : PadicInt p) := by
        simp [f, Polynomial.coeff_zero_eq_eval_zero, Polynomial.cyclotomic_prime,
          Polynomial.eval_finsetSum]
      rw [hcoeff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨a, ha⟩
      have hp0 : (p : PadicInt p) ≠ 0 := by
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      have hpa : (p : PadicInt p) * a = 1 := by
        apply (mul_left_cancel₀ hp0)
        simpa [pow_two, mul_assoc] using ha.symm
      exact (mem_nonunits_iff.mp PadicInt.p_nonunit)
        (IsUnit.of_mul_eq_one a hpa)
  have hf : f = Chapter13CyclotomicEisensteinPolynomial p := by
    have hdiv : Polynomial.X * Chapter13CyclotomicEisensteinPolynomial p =
        (Polynomial.X + 1) ^ p - 1 := by
      simpa [Chapter13CyclotomicEisensteinPolynomial] using
        (Polynomial.mul_divByMonic_eq_iff_isRoot
        (p := (Polynomial.X + 1) ^ p - 1) (a := (0 : PadicInt p))).2 (by simp)
    have hcomp : Polynomial.X * f = (Polynomial.X + 1) ^ p - 1 := by
      have h := congrArg (fun q : Polynomial (PadicInt p) =>
          q.comp (Polynomial.X + 1))
        (Polynomial.cyclotomic_prime_mul_X_sub_one (PadicInt p) p)
      simpa [f, mul_comm] using h
    apply (mul_left_cancel₀ Polynomial.X_ne_zero)
    exact hcomp.trans hdiv.symm
  have hcoeff : f.coeff 0 = (p : PadicInt p) := by
    simp [f, Polynomial.coeff_zero_eq_eval_zero, Polynomial.cyclotomic_prime,
      Polynomial.eval_finsetSum]
  let e : AdjoinRoot f ≃+* Chapter13CyclotomicOrder p :=
    Ideal.quotEquivOfEq (congrArg (fun q : Polynomial (PadicInt p) =>
      Ideal.span ({q} : Set (Polynomial (PadicInt p)))) hf)
  let : IsLocalRing (AdjoinRoot f) := e.symm.isLocalRing
  let : IsDomain (AdjoinRoot f) := e.toMulEquiv.isDomain
  have hdist : f.IsDistinguishedAt (Ideal.span {(p : PadicInt p)}) :=
    ⟨hweak, hmonic⟩
  let H : (f : PowerSeries (PadicInt p)).IsWeierstrassFactorizationAt f 1
      (Ideal.span {(p : PadicInt p)}) :=
    ⟨hdist, isUnit_one, by simp⟩
  let : IsAdicComplete (Ideal.span {(p : PadicInt p)}) (PadicInt p) := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have h04 :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter04.padic_power_series_is_complete_regular_local_two_dimensional p
  have hQne : Ideal.span ({(f : PowerSeries (PadicInt p))} :
      Set (PowerSeries (PadicInt p))) ≠ ⊤ := by
    intro htop
    have hunit : IsUnit (f : PowerSeries (PadicInt p)) :=
      Ideal.span_singleton_eq_top.mp htop
    have hc := PowerSeries.isUnit_iff_constantCoeff.mp hunit
    change IsUnit (f.coeff 0) at hc
    rw [hcoeff] at hc
    exact (mem_nonunits_iff.mp PadicInt.p_nonunit) hc
  let : IsLocalRing
      (PowerSeries (PadicInt p) ⧸
        Ideal.span ({(f : PowerSeries (PadicInt p))} : Set (PowerSeries (PadicInt p)))) :=
    @IsLocalRing.of_surjective' (PowerSeries (PadicInt p)) _ _ _ _
      (Ideal.Quotient.nontrivial_iff.mpr hQne) (Ideal.Quotient.mk _)
      Ideal.Quotient.mk_surjective
  have hquot : Chapter13CompleteNoetherianLocalRing
      (PowerSeries (PadicInt p) ⧸
        Ideal.span ({(f : PowerSeries (PadicInt p))} : Set (PowerSeries (PadicInt p)))) := by
    apply chapter13_quotient_complete_noetherian_local
      (R := PowerSeries (PadicInt p))
    · rw [h04.2.2.2.1]
      exact h04.1
    · exact hQne
  have hW : AdjoinRoot f ≃+*
      (PowerSeries (PadicInt p) ⧸
        Ideal.span ({(f : PowerSeries (PadicInt p))} : Set (PowerSeries (PadicInt p)))) :=
    H.algEquivQuotient.toRingEquiv
  have hcompleteB : IsAdicComplete (IsLocalRing.maximalIdeal (AdjoinRoot f))
      (AdjoinRoot f) := by
    apply (IsAdicComplete.congr_ringEquiv
      (IsLocalRing.maximalIdeal (AdjoinRoot f)) hW).mp
    rw [IsLocalRing.map_ringEquiv_maximalIdeal hW]
    exact hquot.2
  have hqroot :
      f.eval₂ (PadicInt.toZMod : PadicInt p →+* ZMod p) 0 = 0 := by
    simp [f, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.cyclotomic_prime, Polynomial.eval_finsetSum]
  let q : AdjoinRoot f →+* ZMod p :=
    AdjoinRoot.lift (f := f) (PadicInt.toZMod : PadicInt p →+* ZMod p) 0 hqroot
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨a, ha⟩ := ZMod.ringHom_surjective
      (PadicInt.toZMod : PadicInt p →+* ZMod p) y
    refine ⟨AdjoinRoot.of f a, ?_⟩
    simpa [q] using ha
  let N : Ideal (AdjoinRoot f) :=
    Ideal.map (AdjoinRoot.of f : PadicInt p →+* AdjoinRoot f)
        (Ideal.span {(p : PadicInt p)}) ⊔
      Ideal.span {AdjoinRoot.root f}
  have hker : RingHom.ker q = N := by
    apply le_antisymm
    · intro z hz
      induction z using AdjoinRoot.induction_on with
      | ih g =>
          have hqg : PadicInt.toZMod (g.coeff 0) = 0 := by
            simpa [q, AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero] using hz
          have hcg : g.coeff 0 ∈ Ideal.span {(p : PadicInt p)} := by
            rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
            exact RingHom.mem_ker.mpr hqg
          have hmap :
              Ideal.map (AdjoinRoot.of f : PadicInt p →+* AdjoinRoot f)
                (Ideal.span {(p : PadicInt p)}) ≤ N := le_sup_left
          have hdiv := Polynomial.divX_mul_X_add g
          rw [← hdiv, map_add]
          apply N.add_mem
          · have hmul := (AdjoinRoot.mk f).map_mul
                (Polynomial.divX g) Polynomial.X
            rw [hmul, AdjoinRoot.mk_X]
            have hrootN : AdjoinRoot.root f ∈ N := by
              change AdjoinRoot.root f ∈
                Ideal.map (AdjoinRoot.of f : PadicInt p →+* AdjoinRoot f)
                    (Ideal.span {(p : PadicInt p)}) ⊔
                  Ideal.span {AdjoinRoot.root f}
              exact (le_sup_right : Ideal.span
                ({AdjoinRoot.root f} : Set (AdjoinRoot f)) ≤
                  Ideal.map (AdjoinRoot.of f : PadicInt p →+* AdjoinRoot f)
                      (Ideal.span {(p : PadicInt p)}) ⊔
                    Ideal.span {AdjoinRoot.root f})
                (Ideal.subset_span (Set.mem_singleton _))
            exact N.mul_mem_left _ hrootN
          · change AdjoinRoot.of f (g.coeff 0) ∈ N
            exact hmap (Ideal.mem_map_of_mem _ hcg)
    · rw [show N =
        Ideal.map (AdjoinRoot.of f : PadicInt p →+* AdjoinRoot f)
          (Ideal.span {(p : PadicInt p)}) ⊔
          Ideal.span {AdjoinRoot.root f} by rfl]
      apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker]
        have ha0 : PadicInt.toZMod a = 0 := by
          rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
            PadicInt.maximalIdeal_eq_span_p]
          exact ha
        simpa [q] using ha0
      · apply Ideal.span_le.2
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        simp [q, AdjoinRoot.lift_root]
  have hmax : IsLocalRing.maximalIdeal (AdjoinRoot f) = N := by
    exact (IsLocalRing.ker_eq_maximalIdeal q hqsurj).symm.trans hker
  have hproot : (p : AdjoinRoot f) ∈ Ideal.span {AdjoinRoot.root f} := by
    have h := congrArg (fun g : Polynomial (PadicInt p) =>
        g.eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f))
      (Polynomial.divX_mul_X_add f)
    rw [AdjoinRoot.eval₂_root, hcoeff] at h
    exact Ideal.mem_span_singleton'.2 ⟨-
      (Polynomial.divX f).eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f), by
        have h' : (0 : AdjoinRoot f) = (p : AdjoinRoot f) +
            AdjoinRoot.root f *
              (Polynomial.divX f).eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) := by
          simpa [map_add, map_mul, mul_comm, add_comm] using h.symm
        linear_combination h'⟩
  have hmaproot :
      Ideal.map (AdjoinRoot.of f : PadicInt p →+* AdjoinRoot f)
          (Ideal.span {(p : PadicInt p)}) ≤ Ideal.span {AdjoinRoot.root f} := by
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.2
    intro a ha
    rw [Set.mem_singleton_iff.mp ha]
    exact hproot
  have hNroot : N = Ideal.span {AdjoinRoot.root f} := by
    dsimp [N]
    apply le_antisymm
    · exact sup_le hmaproot le_rfl
    · exact le_sup_right
  have hmaxroot : IsLocalRing.maximalIdeal (AdjoinRoot f) =
      Ideal.span {AdjoinRoot.root f} := hmax.trans hNroot
  have hdeg : f.degree ≠ 0 := by
    have hdegree : 0 < f.natDegree := hmonic.natDegree_pos.mpr (by
      intro h
      have hc := congrArg (fun q : Polynomial (PadicInt p) => q.coeff 0) h
      rw [hcoeff] at hc
      have hu : IsUnit (p : PadicInt p) := by
        rw [show (p : PadicInt p) = 1 by simpa using hc]
        exact isUnit_one
      exact (mem_nonunits_iff.mp PadicInt.p_nonunit) hu)
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero]
    exact_mod_cast (Nat.ne_of_gt hdegree)
  have hofinj : Function.Injective (AdjoinRoot.of f) :=
    AdjoinRoot.of.injective_of_degree_ne_zero hdeg
  have hp0 : (p : AdjoinRoot f) ≠ 0 := by
    intro hpzero
    apply (show (p : PadicInt p) ≠ 0 by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
    apply hofinj
    simpa [hcoeff] using hpzero
  have hroot0 : AdjoinRoot.root f ≠ 0 := by
    intro hroot
    have h := AdjoinRoot.eval₂_root f
    rw [hroot, Polynomial.eval₂_at_zero, hcoeff] at h
    apply (show (p : PadicInt p) ≠ 0 by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
    apply hofinj
    simpa using h
  have hnotfield : ¬IsField (AdjoinRoot f) := by
    intro hfield
    have hbot : IsLocalRing.maximalIdeal (AdjoinRoot f) = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    have hspan : Ideal.span ({AdjoinRoot.root f} : Set (AdjoinRoot f)) = ⊥ :=
      hmaxroot.symm.trans hbot
    exact hroot0 (Ideal.span_singleton_eq_bot.mp hspan)
  have hprincipal : (IsLocalRing.maximalIdeal (AdjoinRoot f)).IsPrincipal :=
    ⟨AdjoinRoot.root f, hmaxroot⟩
  let : IsDiscreteValuationRing (AdjoinRoot f) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnotfield).out 4 0).mp hprincipal
  have hdimB : ringKrullDim (AdjoinRoot f) = 1 :=
    IsDiscreteValuationRing.ringKrullDim_eq_one (AdjoinRoot f)
  have hregularB : IsRegularLocalRing (AdjoinRoot f) := by
    have hspan :
        (↑(IsLocalRing.maximalIdeal (AdjoinRoot f)).spanFinrank : WithBot ℕ∞) = 1 := by
      rw [hmaxroot]
      exact_mod_cast Submodule.spanFinrank_singleton hroot0
    exact ⟨hspan.trans (by exact_mod_cast hdimB.symm)⟩
  have hdegree_eq : f.natDegree = p - 1 := by
    have hX : (Polynomial.X + 1 : Polynomial (PadicInt p)).natDegree = 1 := by
      rw [show (Polynomial.X + 1 : Polynomial (PadicInt p)) =
        Polynomial.X + Polynomial.C 1 by simp, Polynomial.natDegree_X_add_C]
    change ((Polynomial.cyclotomic p (PadicInt p)).comp
      (Polynomial.X + 1)).natDegree = p - 1
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_cyclotomic,
      Nat.totient_prime (Fact.out : Nat.Prime p), hX, Nat.mul_one]
  have hdegree_two : 2 ≤ f.natDegree := by
    rw [hdegree_eq]
    omega
  have hdiveval :
      (Polynomial.divX f).eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) ∈
        Ideal.span {AdjoinRoot.root f} := by
    rw [Polynomial.eval₂_eq_sum_range]
    apply Submodule.sum_mem
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      have hcoef : (Polynomial.divX f).coeff 0 ∈
          Ideal.span {(p : PadicInt p)} := by
        rw [Polynomial.coeff_divX]
        exact hweak.mem (by omega)
      simpa using hmaproot (Ideal.mem_map_of_mem _ hcoef)
    · have hpowmem : (AdjoinRoot.root f) ^ i ∈
          Ideal.span {AdjoinRoot.root f} := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        rw [pow_succ]
        exact (Ideal.span {AdjoinRoot.root f}).mul_mem_left _
          (Ideal.subset_span (Set.mem_singleton _))
      exact (Ideal.span {AdjoinRoot.root f}).mul_mem_left _ hpowmem
  have hpow : (p : AdjoinRoot f) ∈
      (IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ 2 := by
    rw [hmaxroot, Ideal.span_singleton_pow]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hdiveval
    have hrel : -((AdjoinRoot.root f) *
        (Polynomial.divX f).eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f)) =
        (p : AdjoinRoot f) := by
      have h := congrArg (fun g : Polynomial (PadicInt p) =>
          g.eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f))
        (Polynomial.divX_mul_X_add f)
      rw [AdjoinRoot.eval₂_root, hcoeff] at h
      have h' : (AdjoinRoot.root f) *
          (Polynomial.divX f).eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) +
            (p : AdjoinRoot f) = 0 := by
        simpa [map_add, map_mul, mul_comm] using h
      linear_combination -h'
    refine Ideal.mem_span_singleton'.2 ⟨-b, ?_⟩
    calc
      -b * (AdjoinRoot.root f) ^ 2 =
          -((AdjoinRoot.root f) * (b * AdjoinRoot.root f)) := by ring
      _ = -((AdjoinRoot.root f) *
          (Polynomial.divX f).eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f)) := by
        rw [hb]
      _ = (p : AdjoinRoot f) := hrel
  have hcompleteOrder : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter13CyclotomicOrder p))
        (Chapter13CyclotomicOrder p) := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact (IsAdicComplete.congr_ringEquiv
      (IsLocalRing.maximalIdeal (AdjoinRoot f)) e).mpr hcompleteB
  have hregularOrder : IsRegularLocalRing (Chapter13CyclotomicOrder p) :=
    hregularB.of_ringEquiv e
  have hdimOrder : ringKrullDim (Chapter13CyclotomicOrder p) = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv e]
    exact hdimB
  have hpowOrder : (p : Chapter13CyclotomicOrder p) ∈
      (IsLocalRing.maximalIdeal (Chapter13CyclotomicOrder p)) ^ 2 := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← Ideal.map_pow]
    change (p : Chapter13CyclotomicOrder p) ∈
      Ideal.map e.toRingHom ((IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ 2)
    exact Ideal.mem_map_of_mem e.toRingHom hpow
  have hpOrder : (p : Chapter13CyclotomicOrder p) ≠ 0 := by
    intro hz
    apply hp0
    apply e.injective
    simpa using hz
  have hramified : IsLocalRing.maximalIdeal (Chapter13CyclotomicOrder p) ≠
      Ideal.span {(p : Chapter13CyclotomicOrder p)} := by
    intro heq
    have hp2 : (p : Chapter13CyclotomicOrder p) ∈
        (Ideal.span {(p : Chapter13CyclotomicOrder p)}) ^ 2 := by
      rw [← heq]
      exact hpowOrder
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hp2
    obtain ⟨a, ha⟩ := hp2
    have hpa : (p : Chapter13CyclotomicOrder p) * a = 1 := by
      apply (mul_left_cancel₀ hpOrder)
      simpa [pow_two, mul_assoc] using ha.symm
    exact (IsLocalRing.notMem_maximalIdeal.mpr (IsUnit.of_mul_eq_one a hpa))
      (Ideal.pow_le_self (by omega) hpowOrder)
  exact ⟨hcompleteOrder, hregularOrder,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    hdimOrder, hpowOrder,
    chapter13_ramified_dvr_is_not_cohen p hramified⟩

/-! ### Formal local coordinates -/

theorem chapter13_formal_local_coordinates
    {R k : Type u} [CommRing R] [IsLocalRing R] [Field k] (d : ℕ)
    (hR : IsNoetherianRing R)
    (hregular : IsRegularLocalRing R)
    (hdim : ringKrullDim R = d)
    (hcontains : Chapter13ContainsField R)
    (e : Chapter13ResidueRing R ≃+* k) :
    Nonempty
      (MvPowerSeries (Fin d) k ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  let : IsNoetherianRing R := hR
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let : IsNoetherianRing A :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter07.chapter07_adic_completion_isNoetherianRing
      (IsLocalRing.maximalIdeal R)
  let hfg : (IsLocalRing.maximalIdeal R).FG :=
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  have hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    exact AdicCompletion.isAdicComplete_of_fg hfg
  have hspan : (IsLocalRing.maximalIdeal A).spanFinrank =
      (IsLocalRing.maximalIdeal R).spanFinrank := by
    exact AdicCompletion.spanFinrank_maximalIdeal_eq
  let : Module.FaithfullyFlat R A :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hdimle : ringKrullDim R ≤ ringKrullDim A := by
    exact chapter13_ringKrullDim_le_of_faithfullyFlat (R := R) (S := A)
  have hspanle : (IsLocalRing.maximalIdeal A).spanFinrank ≤ ringKrullDim A := by
    rw [hspan]
    calc
      (IsLocalRing.maximalIdeal R).spanFinrank = ringKrullDim R :=
        hregular.spanFinrank_maximalIdeal
      _ ≤ ringKrullDim A := hdimle
  have hregularA : IsRegularLocalRing A := by
    exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A hspanle
  have hdimA : ringKrullDim A = d := by
    apply le_antisymm
    · calc
        ringKrullDim A ≤ (IsLocalRing.maximalIdeal A).spanFinrank :=
          ringKrullDim_le_spanFinrank_maximalIdeal A
        _ = (IsLocalRing.maximalIdeal R).spanFinrank := by
          exact_mod_cast hspan
        _ = ringKrullDim R := hregular.spanFinrank_maximalIdeal
        _ = d := by exact_mod_cast hdim
    · calc
        (d : WithBot ℕ∞) = ringKrullDim R := by
          exact_mod_cast hdim.symm
        _ ≤ ringKrullDim A := hdimle
  have hcontainsA : Chapter13ContainsField A := by
    obtain ⟨K⟩ := hcontains
    let f : K.carrier →+* A :=
      (algebraMap R A).comp K.carrier.subtype
    have hf : Function.Injective f := by
      exact (FaithfulSMul.algebraMap_injective R A).comp
        (fun x y h => Subtype.ext h)
    let ef : K.carrier ≃+* f.range :=
      RingEquiv.ofBijective f.rangeRestrict
        ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
    have hfield : IsField f.range :=
      ef.symm.toMulEquiv.isField K.field_carrier
    exact ⟨⟨f.range, hfield⟩⟩
  obtain ⟨K, hK, _⟩ :=
    chapter13_coefficient_field_exists_when_contains_field hcomplete hcontainsA
  let ρ : K.carrier →+* Chapter13ResidueRing A :=
    (Chapter13ResidueMap A).comp K.carrier.subtype
  let eK : K.carrier ≃+* Chapter13ResidueRing A :=
    RingEquiv.ofBijective ρ hK
  let eA : Chapter13ResidueRing A ≃+* k := by
    let r : Chapter13ResidueRing R →+* Chapter13ResidueRing A :=
      IsLocalRing.ResidueField.map (algebraMap R A)
    have hr : Function.Bijective r := by
      exact AdicCompletion.residueField_map_bijective R
    exact (RingEquiv.ofBijective r hr).symm.trans e
  let σ : k →+* A :=
    K.carrier.subtype.comp (eK.trans eA).symm.toRingHom
  have hσ : IsLocalHom σ := by
    apply ((IsLocalRing.local_hom_TFAE σ).out 3 0).mp
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact bot_le
  have hres : Function.Bijective ((Chapter13ResidueMap A).comp σ) := by
    have hcomp : (Chapter13ResidueMap A).comp σ = eA.symm.toRingHom := by
      ext x
      change eK ((eK.trans eA).symm x) = eA.symm x
      simp
    rw [hcomp]
    exact eA.symm.bijective
  exact chapter13_equal_characteristic_complete_regular_is_power_series d
    ⟨inferInstance, hcomplete⟩ hregularA hdimA hcontainsA σ hσ hres

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter13
