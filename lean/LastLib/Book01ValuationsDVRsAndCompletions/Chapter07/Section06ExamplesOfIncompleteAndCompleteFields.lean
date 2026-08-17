import LastLib.Book01ValuationsDVRsAndCompletions.Chapter07.Section05SeparatedCompletionOfRings
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.Algebra.Module.Cardinality

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter07

open Filter Set Function MonoidWithZeroHom
open scoped Topology

noncomputable section

/-!
  Chapter 7 develops completion from the metric point of view and compares it with
  valuation rings and ideal-adic completion. Proofs are deferred to a later pass.
-/

/-! # Book 1, Chapter 7, Section 7.6: Examples of Incomplete and Complete Fields
-/

/-! ### 7.6. Examples: p-adic completions -/

abbrev chapter07PAdicField (p : ℕ) [Fact p.Prime] : Type _ :=
  ℚ_[p]

abbrev chapter07PAdicIntegerRing (p : ℕ) [Fact p.Prime] : Type _ :=
  ℤ_[p]

-- The uniform structure used for the p-adic completion of ℚ.  Pulling back the
-- normed-field uniformity along the canonical map into ℚ_[p] makes the
-- comparison with Mathlib's concrete completion explicit.
abbrev chapter07PAdicUniformSpace (p : ℕ) [Fact p.Prime] : UniformSpace ℚ :=
  UniformSpace.comap ((↑) : ℚ → chapter07PAdicField p)
    (inferInstance : UniformSpace (chapter07PAdicField p))

-- Section 7.6: the rationals are incomplete for the p-adic uniformity.
theorem chapter07_rationals_are_padic_incomplete
    (p : ℕ) [Fact p.Prime] :
    ¬ @CompleteSpace ℚ (chapter07PAdicUniformSpace p) := by
  intro hcomplete
  let : UniformSpace ℚ := chapter07PAdicUniformSpace p
  let : CompleteSpace ℚ := hcomplete
  have hinducing : @IsUniformInducing ℚ (chapter07PAdicField p)
      (chapter07PAdicUniformSpace p)
      (inferInstance : UniformSpace (chapter07PAdicField p))
      ((↑) : ℚ → chapter07PAdicField p) := by
    exact (isUniformInducing_iff_uniformSpace).2 rfl
  have hclosed : IsClosed (Set.range ((↑) : ℚ → chapter07PAdicField p)) := by
    have hemb : IsUniformEmbedding ((↑) : ℚ → chapter07PAdicField p) :=
      ⟨hinducing, Rat.cast_injective⟩
    exact hemb.isClosedEmbedding.isClosed_range
  have hdense : DenseRange ((↑) : ℚ → chapter07PAdicField p) :=
    Padic.denseRange_ratCast p
  have hrange : Set.range ((↑) : ℚ → chapter07PAdicField p) = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_range]
  have hsurj : Function.Surjective ((↑) : ℚ → chapter07PAdicField p) :=
    Set.range_eq_univ.mp hrange
  have hunc : Uncountable (chapter07PAdicField p) := by
    rw [← Cardinal.aleph0_lt_mk_iff]
    exact lt_of_lt_of_le Cardinal.aleph0_lt_continuum
      (continuum_le_cardinal_of_nontriviallyNormedField (chapter07PAdicField p))
  let : Uncountable (chapter07PAdicField p) := hunc
  exact (hsurj.uncountable).not_countable inferInstance

-- The p-adic field is complete.
theorem chapter07_padic_field_is_complete
    (p : ℕ) [Fact p.Prime] :
    CompleteSpace (chapter07PAdicField p) := by
  infer_instance

-- The rationals are dense in the p-adic field.
theorem chapter07_rationals_are_dense_in_padic_field
    (p : ℕ) [Fact p.Prime] :
    DenseRange ((↑) : ℚ → chapter07PAdicField p) := by
  exact Padic.denseRange_ratCast p

-- The completion of ℚ for the p-adic absolute value is ℚ_[p].
theorem chapter07_padic_field_is_the_padic_completion
    (p : ℕ) [Fact p.Prime] :
    ∃ e : @UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p) ≃ᵤ
        chapter07PAdicField p,
      ∀ q : ℚ,
        e (q : @UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p)) =
          (q : chapter07PAdicField p) := by
  let : UniformSpace ℚ := chapter07PAdicUniformSpace p
  have hinducing : @IsUniformInducing ℚ (chapter07PAdicField p)
      (chapter07PAdicUniformSpace p)
      (inferInstance : UniformSpace (chapter07PAdicField p))
      ((↑) : ℚ → chapter07PAdicField p) := by
    exact (isUniformInducing_iff_uniformSpace).2 rfl
  let B : @AbstractCompletion ℚ (chapter07PAdicUniformSpace p) :=
    { space := chapter07PAdicField p
      coe := fun q : ℚ => (q : chapter07PAdicField p)
      uniformStruct := (inferInstance : UniformSpace (chapter07PAdicField p))
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hinducing
      dense := chapter07_rationals_are_dense_in_padic_field p }
  let e := (@UniformSpace.Completion.cPkg ℚ (chapter07PAdicUniformSpace p)).compareEquiv B
  refine ⟨e, ?_⟩
  intro q
  exact AbstractCompletion.compare_coe
    (@UniformSpace.Completion.cPkg ℚ (chapter07PAdicUniformSpace p)) B q

-- The p-adic integers form the complete valuation ring inside ℚ_[p].
theorem chapter07_padic_integer_ring_is_complete
    (p : ℕ) [Fact p.Prime] :
    CompleteSpace (chapter07PAdicIntegerRing p) := by
  infer_instance

-- The localization at (p) carries its canonical map into the fraction field ℚ.
noncomputable def chapter07LocalizedIntegersToRationals
    (p : ℕ) [Fact p.Prime] :
    chapter07LocalizedIntegers p →+* ℚ := by
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  refine IsLocalization.lift (M := P.primeCompl) (g := algebraMap ℤ ℚ) ?_
  intro y
  apply isUnit_iff_ne_zero.mpr
  norm_cast
  intro hy
  have hy0 : ((y : ℤ) : ℚ) = 0 := by simpa using hy
  have hy' : (y : ℤ) = 0 := by exact_mod_cast hy0
  apply y.property
  simp [P, hy']

-- The same localization maps into the p-adic integer subring.  The
-- denominators in the prime complement are precisely the p-adic units.
noncomputable def chapter07LocalizedIntegersToPAdicIntegers
    (p : ℕ) [Fact p.Prime] :
    chapter07LocalizedIntegers p →+* chapter07PAdicIntegerRing p := by
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hp : Prime (p : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using Fact.out)
  refine IsLocalization.lift (M := P.primeCompl)
    (g := algebraMap ℤ (chapter07PAdicIntegerRing p)) ?_
  intro y
  apply (PadicInt.isUnit_iff).2
  apply (PadicInt.norm_intCast_eq_one_iff).2
  apply IsCoprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hy
  apply y.property
  exact Ideal.mem_span_singleton.mpr hy

abbrev chapter07LocalizedIntegersPAdicUniformSpace (p : ℕ) [Fact p.Prime] :
    UniformSpace (chapter07LocalizedIntegers p) :=
  UniformSpace.comap (chapter07LocalizedIntegersToPAdicIntegers p)
    (inferInstance : UniformSpace (chapter07PAdicIntegerRing p))

-- The canonical p-adic uniformity on the localization is pulled back from ℚ.
theorem chapter07_localized_integers_padic_completion
    (p : ℕ) [Fact p.Prime] :
    ∃ e : @UniformSpace.Completion (chapter07LocalizedIntegers p)
        (chapter07LocalizedIntegersPAdicUniformSpace p) ≃ᵤ
          chapter07PAdicIntegerRing p,
      ∀ a : chapter07LocalizedIntegers p,
        e (a : @UniformSpace.Completion (chapter07LocalizedIntegers p)
          (chapter07LocalizedIntegersPAdicUniformSpace p)) =
          chapter07LocalizedIntegersToPAdicIntegers p a := by
  let : UniformSpace (chapter07LocalizedIntegers p) :=
    chapter07LocalizedIntegersPAdicUniformSpace p
  let f : chapter07LocalizedIntegers p →+* chapter07PAdicIntegerRing p :=
    chapter07LocalizedIntegersToPAdicIntegers p
  have hdf : DenseRange f := by
    refine DenseRange.of_comp (f := (f : chapter07LocalizedIntegers p →
      chapter07PAdicIntegerRing p))
      (g := (algebraMap ℤ (chapter07LocalizedIntegers p) :
        ℤ → chapter07LocalizedIntegers p)) ?_
    have hdense : DenseRange
        ((Int.cast) : ℤ → chapter07PAdicIntegerRing p) :=
      PadicInt.denseRange_intCast
    simpa [Function.comp_def, f, chapter07LocalizedIntegersToPAdicIntegers] using hdense
  have hinducing : @IsUniformInducing (chapter07LocalizedIntegers p)
      (chapter07PAdicIntegerRing p) (chapter07LocalizedIntegersPAdicUniformSpace p)
      (inferInstance : UniformSpace (chapter07PAdicIntegerRing p))
      (f : chapter07LocalizedIntegers p → chapter07PAdicIntegerRing p) := by
    exact (isUniformInducing_iff_uniformSpace).2 rfl
  let B : @AbstractCompletion (chapter07LocalizedIntegers p)
      (chapter07LocalizedIntegersPAdicUniformSpace p) :=
    { space := chapter07PAdicIntegerRing p
      coe := f
      uniformStruct := (inferInstance : UniformSpace (chapter07PAdicIntegerRing p))
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := hinducing
      dense := hdf }
  let e := (@UniformSpace.Completion.cPkg (chapter07LocalizedIntegers p)
    (chapter07LocalizedIntegersPAdicUniformSpace p)).compareEquiv B
  refine ⟨e, ?_⟩
  intro a
  exact AbstractCompletion.compare_coe
    (@UniformSpace.Completion.cPkg (chapter07LocalizedIntegers p)
      (chapter07LocalizedIntegersPAdicUniformSpace p)) B a

lemma chapter07_padic_digit_truncation_succ
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) (i : ℕ) :
    chapter07DigitTruncation p (i + 1) a =
      chapter07DigitTruncation p i a + (a i).val * p ^ i := by
  simp [chapter07DigitTruncation, Finset.sum_range_succ]

lemma chapter07_padic_digit_truncation_divisibility
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) :
    ∀ i : ℕ,
      (p : ℤ) ^ i ∣
        (chapter07DigitTruncation p (i + 1) a : ℤ) -
          chapter07DigitTruncation p i a := by
  intro i
  rw [chapter07_padic_digit_truncation_succ]
  refine ⟨(a i).val, ?_⟩
  push_cast
  ring

-- The p-adic truncation sequence attached to an infinite digit string.
def chapter07PAdicDigitLimit
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) :
    chapter07PAdicIntegerRing p :=
  PadicInt.ofIntSeq (p := p)
    (fun n => (chapter07DigitTruncation p n a : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (fun n => (chapter07DigitTruncation p n a : ℤ)) p
      (chapter07_padic_digit_truncation_divisibility p a))

-- Rational truncations converge to the digit-string limit in the p-adic integers.
theorem chapter07_padic_digit_truncations_converge
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) :
    Tendsto
      (fun n => ((chapter07DigitTruncation p n a : ℕ) :
        chapter07PAdicField p))
      (atTop : Filter ℕ)
      (𝓝 ((chapter07PAdicDigitLimit p a : chapter07PAdicIntegerRing p) :
        chapter07PAdicField p)) := by
  let f : PadicSeq p :=
    ⟨fun n => (chapter07DigitTruncation p n a : ℚ), by
      simpa using
        (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
          (fun n => (chapter07DigitTruncation p n a : ℤ)) p
          (chapter07_padic_digit_truncation_divisibility p a))⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨εq, hεq⟩ := exists_rat_btwn hε
  have hεq0 : (0 : ℚ) < εq := by exact_mod_cast hεq.1
  obtain ⟨N, hN⟩ := padicNormE.defn f hεq0
  refine ⟨N, ?_⟩
  intro n hn
  have hN' := hN n hn
  have hNreal :
      (↑(padicNormE (Padic.mk f - (f n : chapter07PAdicField p))) : ℝ) < ε := by
    exact lt_trans (by exact_mod_cast hN') hεq.2
  have hlim : (Padic.mk f : chapter07PAdicField p) =
      (chapter07PAdicDigitLimit p a : chapter07PAdicField p) := by
    rfl
  have hfn : (f n : chapter07PAdicField p) =
      (chapter07DigitTruncation p n a : chapter07PAdicField p) := by
    rfl
  have htarget :
      ‖(Padic.mk f : chapter07PAdicField p) - (f n : chapter07PAdicField p)‖ < ε := by
    simpa only [Padic.padicNormE.is_norm] using hNreal
  rw [← hlim, dist_eq_norm, norm_sub_rev]
  simpa only [hfn] using htarget

-- A digit string is rationally represented if its p-adic limit comes from ℚ.
def chapter07DigitStringRationallyRepresented
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) : Prop :=
  ∃ q : ℚ,
    (q : chapter07PAdicField p) =
      (chapter07PAdicDigitLimit p a : chapter07PAdicField p)

lemma chapter07_padic_digit_limit_injective
    (p : ℕ) [Fact p.Prime] :
    Function.Injective (chapter07PAdicDigitLimit p) := by
  intro a b hab
  have htrunc : ∀ n : ℕ,
      chapter07DigitTruncation p n a = chapter07DigitTruncation p n b := by
    intro n
    have hmod :
        ((chapter07DigitTruncation p n a : ℕ) : ZMod (p ^ n)) =
          ((chapter07DigitTruncation p n b : ℕ) : ZMod (p ^ n)) := by
      calc
        ((chapter07DigitTruncation p n a : ℕ) : ZMod (p ^ n)) =
            PadicInt.toZModPow n (chapter07PAdicDigitLimit p a) := by
              symm
              simpa [chapter07PAdicDigitLimit] using
                (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
                  (fun m => (chapter07DigitTruncation p m a : ℤ)) p
                  (chapter07_padic_digit_truncation_divisibility p a) n)
        _ = PadicInt.toZModPow n (chapter07PAdicDigitLimit p b) :=
          congrArg (PadicInt.toZModPow (p := p) n) hab
        _ = ((chapter07DigitTruncation p n b : ℕ) : ZMod (p ^ n)) := by
              simpa [chapter07PAdicDigitLimit] using
                (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
                  (fun m => (chapter07DigitTruncation p m b : ℤ)) p
                  (chapter07_padic_digit_truncation_divisibility p b) n)
    have hmod' :
        chapter07DigitTruncation p n a ≡ chapter07DigitTruncation p n b [MOD p ^ n] := by
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hmod
    have hbound : ∀ c : chapter07DigitString p, ∀ m : ℕ,
        chapter07DigitTruncation p m c < p ^ m := by
      intro c m
      induction m with
      | zero => simp [chapter07DigitTruncation]
      | succ m ih =>
          rw [chapter07_padic_digit_truncation_succ]
          have hd : (c m).val < p := (c m).isLt
          have hpow : 0 < p ^ m := pow_pos (Nat.Prime.pos Fact.out) _
          have hsum : (c m).val + 1 ≤ p := Nat.succ_le_of_lt hd
          have hadd : chapter07DigitTruncation p m c + (c m).val * p ^ m <
              p ^ m + (c m).val * p ^ m := by
            exact Nat.add_lt_add_right ih ((c m).val * p ^ m)
          have hle : p ^ m + (c m).val * p ^ m ≤ p * p ^ m := by
            calc
              p ^ m + (c m).val * p ^ m = ((c m).val + 1) * p ^ m := by ring
              _ ≤ p * p ^ m := Nat.mul_le_mul_right _ hsum
          calc
            chapter07DigitTruncation p m c + (c m).val * p ^ m <
                p ^ m + (c m).val * p ^ m := hadd
            _ = ((c m).val + 1) * p ^ m := by ring
            _ ≤ p * p ^ m := Nat.mul_le_mul_right _ hsum
            _ = p ^ (m + 1) := by simp [pow_succ, Nat.mul_comm]
    have ha := hbound a n
    have hb := hbound b n
    have hrem :
        chapter07DigitTruncation p n a % p ^ n =
          chapter07DigitTruncation p n b % p ^ n := hmod'
    calc
      chapter07DigitTruncation p n a =
          chapter07DigitTruncation p n a % p ^ n :=
        (Nat.mod_eq_of_lt ha).symm
      _ = chapter07DigitTruncation p n b % p ^ n := hrem
      _ = chapter07DigitTruncation p n b := Nat.mod_eq_of_lt hb
  apply funext
  intro i
  have hi := htrunc (i + 1)
  rw [chapter07_padic_digit_truncation_succ,
    chapter07_padic_digit_truncation_succ, htrunc i] at hi
  have hmul : (a i).val * p ^ i = (b i).val * p ^ i :=
    Nat.add_left_cancel hi
  apply Fin.ext
  exact Nat.mul_right_cancel
    (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hmul

-- The compatible infinite digit strings with no rational representative are uncountable.
theorem chapter07_nonrational_padic_digit_strings_uncountable
    (p : ℕ) [Fact p.Prime] :
    ¬ Set.Countable
      {a : chapter07DigitString p |
        ¬ chapter07DigitStringRationallyRepresented p a} := by
  classical
  let T : Set (chapter07DigitString p) :=
    {a | chapter07DigitStringRationallyRepresented p a}
  let S : Set (chapter07DigitString p) :=
    {a | ¬chapter07DigitStringRationallyRepresented p a}
  let qOf : chapter07DigitString p → ℚ := fun a =>
    if ha : chapter07DigitStringRationallyRepresented p a then
      Classical.choose ha
    else 0
  have hq_spec {a : chapter07DigitString p} (ha : a ∈ T) :
      (qOf a : chapter07PAdicField p) =
        (chapter07PAdicDigitLimit p a : chapter07PAdicField p) := by
    change chapter07DigitStringRationallyRepresented p a at ha
    simp only [qOf, dif_pos ha]
    exact Classical.choose_spec ha
  have hq_inj : Set.InjOn qOf T := by
    intro a ha b hb hab
    have hlim :
        (chapter07PAdicDigitLimit p a : chapter07PAdicField p) =
          (chapter07PAdicDigitLimit p b : chapter07PAdicField p) := by
      calc
        (chapter07PAdicDigitLimit p a : chapter07PAdicField p) = qOf a :=
          (hq_spec ha).symm
        _ = qOf b := congrArg (fun q : ℚ => (q : chapter07PAdicField p)) hab
        _ = (chapter07PAdicDigitLimit p b : chapter07PAdicField p) := hq_spec hb
    apply chapter07_padic_digit_limit_injective p
    exact Subtype.ext hlim
  have hT : T.Countable := by
    apply Set.countable_of_injective_of_countable_image hq_inj
    exact Set.countable_univ.mono (Set.image_subset_iff.2 fun _ _ => Set.mem_univ _)
  have hbool_uncountable : Uncountable (ℕ → Bool) := by
    rw [← not_countable_iff]
    intro hc
    let : Countable (ℕ → Bool) := hc
    obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
    let g : ℕ → Bool := fun n => !(f n n)
    obtain ⟨m, hm⟩ := hf g
    have hdiag := congrFun hm m
    cases hfm : f m m <;> simp [g, hfm] at hdiag
  have hp2 : 2 ≤ p := Nat.Prime.two_le Fact.out
  let emb : (ℕ → Bool) → chapter07DigitString p := fun b n =>
    if b n then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hemb : Function.Injective emb := by
    intro x y hxy
    funext n
    have hn := congrArg (fun z : Fin p => z.val)
      (congrFun hxy n)
    cases hxn : x n <;> cases hyn : y n <;>
      simp [emb, hxn, hyn] at hn ⊢
  let : Uncountable (ℕ → Bool) := hbool_uncountable
  have hdigit_uncountable : Uncountable (chapter07DigitString p) :=
    hemb.uncountable
  let : Uncountable (chapter07DigitString p) := hdigit_uncountable
  intro hSfin
  have hU : (Set.univ : Set (chapter07DigitString p)) ⊆ T ∪ S := by
    intro a ha
    by_cases hrep : chapter07DigitStringRationallyRepresented p a
    · exact Or.inl hrep
    · exact Or.inr hrep
  have hcount : (Set.univ : Set (chapter07DigitString p)).Countable :=
    (hT.union hSfin).mono hU
  exact (not_countable_univ (α := chapter07DigitString p)) hcount

/-! ### 7.6. Examples: Laurent and power series -/

abbrev chapter07RationalFunctionField (k : Type*) [Field k] : Type _ :=
  RatFunc k

abbrev chapter07LaurentSeriesField (k : Type*) [Field k] : Type _ :=
  LaurentSeries k

abbrev chapter07PowerSeriesRing (k : Type*) [Field k] : Type _ :=
  PowerSeries k

-- The X-adic completion of the rational-function field in the Laurent-series API.
abbrev chapter07RationalFunctionAdicCompletion (k : Type*) [Field k] : Type _ :=
  LaurentSeries.RatFuncAdicCompl k

-- The local ring `k[t]_(t)` at the prime generated by `t`.
noncomputable instance chapter07PolynomialOriginPrime (k : Type*) [Field k] :
    (Ideal.span ({(Polynomial.X : Polynomial k)} : Set (Polynomial k))).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

abbrev chapter07PolynomialLocalRing (k : Type*) [Field k] : Type _ :=
  Localization ((Ideal.span ({(Polynomial.X : Polynomial k)} : Set (Polynomial k))).primeCompl)

-- The extension of `(t)` to the localized polynomial ring.
abbrev chapter07PolynomialLocalIdeal (k : Type*) [Field k] :
    Ideal (chapter07PolynomialLocalRing k) :=
  Ideal.map (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k))
    (Ideal.span ({(Polynomial.X : Polynomial k)} : Set (Polynomial k)))

theorem chapter07_polynomial_local_ideal_eq_maximalIdeal
    (k : Type*) [Field k] :
    chapter07PolynomialLocalIdeal k =
      IsLocalRing.maximalIdeal (chapter07PolynomialLocalRing k) := by
  exact Localization.AtPrime.map_eq_maximalIdeal

-- The completed local ring, using the `(t)`-adic topology.
abbrev chapter07PolynomialLocalCompletion (k : Type*) [Field k] : Type _ :=
  AdicCompletion (chapter07PolynomialLocalIdeal k)
    (chapter07PolynomialLocalRing k)

-- Laurent series are complete for the X-adic valuation.
theorem chapter07_laurent_series_are_complete
    (k : Type*) [Field k] :
    CompleteSpace (chapter07LaurentSeriesField k) := by
  infer_instance

-- Rational functions are dense in Laurent series.
theorem chapter07_rational_functions_are_dense_in_laurent_series
    (k : Type*) [Field k] :
    DenseRange
      ((↑) : chapter07RationalFunctionField k →
        chapter07LaurentSeriesField k) := by
  exact LaurentSeries.coe_range_dense

-- The rational-function completion is identified with the Laurent-series field.
def chapter07RationalFunctionAdicToLaurentSeries
    (k : Type*) [Field k] :
    chapter07RationalFunctionAdicCompletion k ≃+*
      chapter07LaurentSeriesField k :=
  LaurentSeries.ratfuncAdicComplRingEquiv k

-- Section 7.6: completion of k(t) for the t-adic valuation gives k((t)).
theorem chapter07_rational_function_completion_is_laurent_series
    (k : Type*) [Field k] :
    Nonempty
      (chapter07RationalFunctionAdicCompletion k ≃+*
        chapter07LaurentSeriesField k) := by
  exact ⟨chapter07RationalFunctionAdicToLaurentSeries k⟩

-- The completed local valuation ring is identified with k[[t]].
def chapter07PowerSeriesToPolynomialLocalCompletion
    (k : Type*) [Field k] :
  Prop :=
  ∃ e : chapter07PowerSeriesRing k ≃+* chapter07PolynomialLocalCompletion k,

    ∀ p : Polynomial k,
      e (p : chapter07PowerSeriesRing k) =
        chapter07AdicCompletionMap (chapter07PolynomialLocalIdeal k)
          (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k) p)
-- The same local identification as an algebra equivalence.
def chapter07PowerSeriesAlgebraToPolynomialLocalCompletion
    (k : Type*) [Field k] :
  Prop :=
  ∃ e : chapter07PowerSeriesRing k ≃ₐ[k] chapter07PolynomialLocalCompletion k,
    ∀ p : Polynomial k,
      e (p : chapter07PowerSeriesRing k) =
        chapter07AdicCompletionMap (chapter07PolynomialLocalIdeal k)
          (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k) p)

-- Section 7.6: completion of k[t]_(t) gives k[[t]].
theorem chapter07_polynomial_local_completion_is_power_series
    (k : Type*) [Field k] :
    chapter07PowerSeriesToPolynomialLocalCompletion k ∧
      chapter07PowerSeriesAlgebraToPolynomialLocalCompletion k := by
  classical
  let R := Polynomial k
  let P : Ideal R := Ideal.span ({(Polynomial.X : R)} : Set R)
  let M : Submonoid R := P.primeCompl
  let L := Localization M
  let J : Ideal L := Ideal.map (algebraMap R L) P
  let PS := chapter07PowerSeriesRing k
  let Q : Ideal PS := Ideal.span ({(PowerSeries.X : PS)} : Set PS)
  let c : R →+* PS := Polynomial.coeToPowerSeries.ringHom
  let : Q.IsMaximal := by
    dsimp [Q]
    rw [← PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hcoe_mem (n : ℕ) (p : R) :
      (p : PS) ∈ Q ^ n ↔ p ∈ P ^ n := by
    change
      (p : PS) ∈ (Ideal.span ({(PowerSeries.X : PS)} : Set PS)) ^ n ↔
        p ∈ (Ideal.span ({(Polynomial.X : R)} : Set R)) ^ n
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton,
      PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
    simp only [Polynomial.coeff_coe]
  have hcunit (n : ℕ) (s : M) :
      IsUnit (((Ideal.Quotient.mk (Q ^ n)).comp c) s.1) := by
    by_cases hn : n = 0
    · subst n
      have htop : Q ^ 0 = (⊤ : Ideal PS) := by simp
      rw [htop]
      exact isUnit_of_subsingleton _
    have hsQ : (s.1 : PS) ∉ Q := by
      intro hs
      have hs0 : PowerSeries.constantCoeff (s.1 : PS) = 0 := by
        apply PowerSeries.X_dvd_iff.mp
        exact Ideal.mem_span_singleton.mp (by simpa [Q] using hs)
      have hsP0 : Polynomial.constantCoeff s.1 = 0 := by
        simpa using hs0
      have hsP : (s.1 : R) ∉ P := s.property
      apply hsP
      change (s.1 : R) ∈ Ideal.span ({(Polynomial.X : R)} : Set R)
      rw [← Polynomial.ker_constantCoeff, RingHom.mem_ker]
      exact hsP0
    change IsUnit (Ideal.Quotient.mk (Q ^ n) (s.1 : PS))
    exact Ideal.Quotient.isUnit_mk_pow_of_notMem Q (n := n) hsQ
  let g : ∀ n : ℕ, L →+* PS ⧸ Q ^ n := fun n ↦
    IsLocalization.lift (M := M)
      (g := (Ideal.Quotient.mk (Q ^ n)).comp c) (hcunit n)
  have hmap (n : ℕ) :
      Ideal.map (g n) (J ^ n) ≤ (⊥ : Ideal (PS ⧸ Q ^ n)) := by
    change Ideal.map (g n) ((Ideal.map (algebraMap R L) P) ^ n) ≤ ⊥
    rw [← Ideal.map_pow, Ideal.map_map]
    change Ideal.map ((g n).comp (algebraMap R L))
      ((Ideal.span ({(Polynomial.X : R)} : Set R)) ^ n) ≤ ⊥
    rw [Ideal.map_le_iff_le_comap, Ideal.span_singleton_pow]
    refine Ideal.span_le.2 ?_
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    change (g n) (algebraMap R L ((Polynomial.X : R) ^ n)) = 0
    simp only [g, IsLocalization.lift_eq]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hc : c ((Polynomial.X : R) ^ n) =
        (((Polynomial.X : R) ^ n : R) : PS) := by
      change Polynomial.coeToPowerSeries.ringHom ((Polynomial.X : R) ^ n) = _
      exact Polynomial.coeToPowerSeries.ringHom_apply
    rw [hc]
    apply (hcoe_mem n ((Polynomial.X : R) ^ n)).2
    change (Polynomial.X : R) ^ n ∈
      (Ideal.span ({(Polynomial.X : R)} : Set R)) ^ n
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have hJker (n : ℕ) : J ^ n ≤ RingHom.ker (g n) := by
    intro a ha
    apply RingHom.mem_ker.mpr
    have hmem : g n a ∈ Ideal.map (g n) (J ^ n) :=
      Ideal.mem_map_of_mem (g n) ha
    simpa using hmap n hmem
  let q : ∀ n : ℕ, L ⧸ J ^ n →+* PS ⧸ Q ^ n := fun n ↦
    Ideal.Quotient.lift (J ^ n) (g n) (fun a ha ↦ hJker n ha)
  have hq_bij (n : ℕ) : Function.Bijective (q n) := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
      have hgab : g n a = g n b := by
        change g n a = g n b at hxy
        exact hxy
      have hzero : g n (a - b) = 0 := by
        rw [map_sub, hgab, sub_self]
      obtain ⟨p, s, hs⟩ := IsLocalization.exists_mk'_eq M (a - b)
      rw [← hs]
      have hzero' : g n (IsLocalization.mk' L p s) = 0 := by
        simpa [hs] using hzero
      have hgp : ((Ideal.Quotient.mk (Q ^ n)).comp c) p = 0 := by
        have hspec :=
          (IsLocalization.lift_mk'_spec (M := M)
            (g := (Ideal.Quotient.mk (Q ^ n)).comp c) (hcunit n) p 0 s).mp
            (by simpa [g] using hzero')
        simpa using hspec
      have hpQ : (p : PS) ∈ Q ^ n := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hcp : c p = (p : PS) := by
          change Polynomial.coeToPowerSeries.ringHom p = (p : PS)
          exact Polynomial.coeToPowerSeries.ringHom_apply
        simpa only [RingHom.comp_apply, hcp] using hgp
      have hpP : p ∈ P ^ n := (hcoe_mem n p).mp hpQ
      have hpL : algebraMap R L p ∈ J ^ n := by
        change algebraMap R L p ∈ (Ideal.map (algebraMap R L) P) ^ n
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem (algebraMap R L) hpP
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact (J ^ n).mul_mem_right _ hpL
    · intro z
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
      let p : R := PowerSeries.trunc n f
      let t : PS := PowerSeries.mk (fun i ↦ PowerSeries.coeff (i + n) f)
      have hXn : (PowerSeries.X : PS) ^ n ∈ Q ^ n := by
        change (PowerSeries.X : PS) ^ n ∈
          (Ideal.span ({(PowerSeries.X : PS)} : Set PS)) ^ n
        rw [Ideal.span_singleton_pow]
        exact Ideal.mem_span_singleton_self _
      have hdiff : f - (p : PS) ∈ Q ^ n := by
        have hfdiff : f - (p : PS) = (PowerSeries.X : PS) ^ n * t := by
          apply sub_eq_iff_eq_add.mpr
          dsimp [p, t]
          exact PowerSeries.eq_X_pow_mul_shift_add_trunc n f
        rw [hfdiff]
        exact (Q ^ n).mul_mem_right _ hXn
      refine ⟨Ideal.Quotient.mk (J ^ n) (algebraMap R L p), ?_⟩
      change g n (algebraMap R L p) =
        Ideal.Quotient.mk (Q ^ n) f
      simp only [g, IsLocalization.lift_eq]
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
      have hcp : c p = (p : PS) := by
        change Polynomial.coeToPowerSeries.ringHom p = (p : PS)
        exact Polynomial.coeToPowerSeries.ringHom_apply
      have hdiff' : (p : PS) - f ∈ Q ^ n := by
        simpa only [neg_sub] using (Q ^ n).neg_mem hdiff
      simpa only [hcp, sub_eq_add_neg] using hdiff'
  have hg_comp {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow Q hle).comp (g n) = g m := by
    apply IsLocalization.ringHom_ext M
    apply RingHom.ext
    intro p
    simp only [g, IsLocalization.lift_eq, RingHom.comp_apply,
      Ideal.Quotient.factor_mk]
  have hq_comp {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow Q hle).comp (q n) =
        (q m).comp (Ideal.Quotient.factorPow J hle) := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (Ideal.Quotient.factorPow Q hle) (g n a) = g m a
    exact DFunLike.congr_fun (hg_comp hle) a
  let qEquiv (n : ℕ) : L ⧸ J ^ n ≃+* PS ⧸ Q ^ n :=
    RingEquiv.ofBijective (q n) (hq_bij n)
  let H : ∀ n : ℕ, PS →+* L ⧸ J ^ n := fun n ↦
    (qEquiv n).symm.toRingHom.comp (Ideal.Quotient.mk (Q ^ n))
  have hH_comp {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow J hle).comp (H n) = H m := by
    apply RingHom.ext
    intro x
    apply (qEquiv m).injective
    change q m ((Ideal.Quotient.factorPow J hle) (H n x)) = q m (H m x)
    have hq := DFunLike.congr_fun (hq_comp hle) (H n x)
    change (Ideal.Quotient.factorPow Q hle) (q n (H n x)) =
      q m ((Ideal.Quotient.factorPow J hle) (H n x)) at hq
    rw [← hq]
    change (Ideal.Quotient.factorPow Q hle)
        ((qEquiv n) ((qEquiv n).symm (Ideal.Quotient.mk (Q ^ n) x))) =
      (qEquiv m) ((qEquiv m).symm (Ideal.Quotient.mk (Q ^ m) x))
    simp
  let d : PS →+* AdicCompletion J L :=
    AdicCompletion.liftRingHom J H hH_comp
  let F : ∀ n : ℕ, AdicCompletion J L →+* PS ⧸ Q ^ n := fun n ↦
    (q n).comp (AdicCompletion.evalₐ J n).toRingHom
  have heval_comp {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion J L) :
      (Ideal.Quotient.factorPow J hle) (AdicCompletion.evalₐ J n x) =
        AdicCompletion.evalₐ J m x := by
    rw [← AdicCompletion.factor_eval_eq_evalₐ J x
      (le_of_eq (Ideal.mul_top _))]
    rw [← AdicCompletion.factor_eval_eq_evalₐ J x
      (le_of_eq (Ideal.mul_top _))]
    have htrans :=
      AdicCompletion.transitionMap_comp_eval_apply (I := J) (M := L) hle x
    have htrans' := congrArg
      (fun z ↦ Ideal.Quotient.factor (le_of_eq (Ideal.mul_top (J ^ m))) z)
      htrans
    simpa [AdicCompletion.eval, AdicCompletion.transitionMap] using htrans'
  have hF_comp {m n : ℕ} (hle : m ≤ n) :
      (Ideal.Quotient.factorPow Q hle).comp (F n) = F m := by
    apply RingHom.ext
    intro x
    change (Ideal.Quotient.factorPow Q hle)
        (q n (AdicCompletion.evalₐ J n x)) =
      q m (AdicCompletion.evalₐ J m x)
    have hq :=
      DFunLike.congr_fun (hq_comp hle) (AdicCompletion.evalₐ J n x)
    change (Ideal.Quotient.factorPow Q hle)
        (q n (AdicCompletion.evalₐ J n x)) =
      q m ((Ideal.Quotient.factorPow J hle) (AdicCompletion.evalₐ J n x)) at hq
    rw [hq]
    exact congrArg (q m) (heval_comp hle x)
  let eHom : AdicCompletion J L →+* PS :=
    IsAdicComplete.liftRingHom Q F hF_comp
  have hed : eHom.comp d = RingHom.id PS := by
    apply DFunLike.coe_injective
    apply IsHausdorff.funext' Q
    intro n x
    change Ideal.Quotient.mk (Q ^ n) (eHom (d x)) =
      Ideal.Quotient.mk (Q ^ n) x
    rw [IsAdicComplete.mk_liftRingHom Q F hF_comp]
    change q n (AdicCompletion.evalₐ J n (d x)) =
      Ideal.Quotient.mk (Q ^ n) x
    rw [show AdicCompletion.evalₐ J n (d x) = H n x by
      exact AdicCompletion.evalₐ_liftRingHom J H hH_comp n x]
    change (qEquiv n) ((qEquiv n).symm (Ideal.Quotient.mk (Q ^ n) x)) = _
    simp
  have hde : d.comp eHom = RingHom.id (AdicCompletion J L) := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    calc
      AdicCompletion.evalₐ J n (d (eHom x)) = H n (eHom x) := by
        simp [d]
      _ = (qEquiv n).symm (Ideal.Quotient.mk (Q ^ n) (eHom x)) := by
        simp [H]
      _ = (qEquiv n).symm (F n x) := by
        rw [IsAdicComplete.mk_liftRingHom Q F hF_comp]
      _ = (qEquiv n).symm (q n (AdicCompletion.evalₐ J n x)) := by
        simp [F]
      _ = AdicCompletion.evalₐ J n x := by
        change (qEquiv n).symm ((qEquiv n) (AdicCompletion.evalₐ J n x)) = _
        exact (qEquiv n).symm_apply_apply _
  have he_left : Function.LeftInverse d eHom := by
    intro x
    simpa using DFunLike.congr_fun hde x
  have he_right : Function.RightInverse d eHom := by
    intro x
    simpa using DFunLike.congr_fun hed x
  have he_bij : Function.Bijective eHom :=
    ⟨Function.LeftInverse.injective he_left, Function.RightInverse.surjective he_right⟩
  let eAC : AdicCompletion J L ≃+* PS := RingEquiv.ofBijective eHom he_bij
  have hebase (p : R) :
      eHom (AdicCompletion.of J L (algebraMap R L p)) = (p : PS) := by
    apply (IsHausdorff.eq_iff_smodEq (I := Q)).2
    intro n
    rw [SModEq.sub_mem]
    have hqval :
        Ideal.Quotient.mk (Q ^ n)
            (eHom (AdicCompletion.of J L (algebraMap R L p))) =
          Ideal.Quotient.mk (Q ^ n) (p : PS) := by
      rw [IsAdicComplete.mk_liftRingHom Q F hF_comp]
      simp only [F, RingHom.comp_apply]
      change q n (AdicCompletion.evalₐ J n
        (AdicCompletion.of J L (algebraMap R L p))) =
        Ideal.Quotient.mk (Q ^ n) (p : PS)
      rw [AdicCompletion.evalₐ_of]
      change g n (algebraMap R L p) = Ideal.Quotient.mk (Q ^ n) (p : PS)
      simp [g, c]
      congr 1
    have hmem :
        eHom (AdicCompletion.of J L (algebraMap R L p)) - (p : PS) ∈ Q ^ n :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hqval
    rw [smul_eq_mul, Ideal.mul_top]
    exact hmem
  let ePS : chapter07PowerSeriesRing k ≃+* chapter07PolynomialLocalCompletion k := by
    exact eAC.symm
  have hePS_poly (p : Polynomial k) :
      ePS (p : chapter07PowerSeriesRing k) =
        chapter07AdicCompletionMap (chapter07PolynomialLocalIdeal k)
          (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k) p) := by
    apply eAC.injective
    rw [eAC.apply_symm_apply]
    simpa [ePS, chapter07AdicCompletionMap, chapter07PolynomialLocalIdeal,
      chapter07PolynomialLocalRing, P, L, J, PS, M,
      AdicCompletion.algebraMap_apply, eAC] using (hebase p).symm
  have hePS_const (a : k) :
      ePS (algebraMap k (chapter07PowerSeriesRing k) a) =
        algebraMap k (chapter07PolynomialLocalCompletion k) a := by
    have hleft :
        algebraMap k (chapter07PowerSeriesRing k) a =
          (Polynomial.C a : chapter07PowerSeriesRing k) := by
      simp [chapter07PowerSeriesRing]
    have hright :
        chapter07AdicCompletionMap (chapter07PolynomialLocalIdeal k)
            (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k)
              (Polynomial.C a)) =
          algebraMap k (chapter07PolynomialLocalCompletion k) a := by
      change algebraMap L (AdicCompletion J L)
          (algebraMap R L (Polynomial.C a)) =
        algebraMap k (AdicCompletion J L) a
      calc
        algebraMap L (AdicCompletion J L)
              (algebraMap R L (Polynomial.C a)) =
            algebraMap L (AdicCompletion J L)
              (algebraMap R L (algebraMap k R a)) := by
                congr 2
        _ = algebraMap k (AdicCompletion J L) a := by
          exact (IsScalarTower.algebraMap_apply k L (AdicCompletion J L) a).symm
    rw [hleft]
    exact (hePS_poly (Polynomial.C a)).trans hright
  let eAlg : chapter07PowerSeriesRing k ≃ₐ[k]
      chapter07PolynomialLocalCompletion k :=
    AlgEquiv.ofRingEquiv (f := ePS) hePS_const
  exact ⟨⟨ePS, hePS_poly⟩, ⟨eAlg, hePS_poly⟩⟩

-- Truncation of a power series to a polynomial, viewed again as a power series.
def chapter07PowerSeriesTruncation
    {k : Type*} [Field k] (n : ℕ) (f : chapter07PowerSeriesRing k) :
    chapter07PowerSeriesRing k :=
  (PowerSeries.trunc n f : chapter07PowerSeriesRing k)

-- Power-series truncations stabilize each coefficient.
theorem chapter07_power_series_truncations_coefficients_stabilize
    {k : Type*} [Field k] (f : chapter07PowerSeriesRing k) :
    ∀ d : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      PowerSeries.coeff d (chapter07PowerSeriesTruncation n f) = PowerSeries.coeff d f := by
  intro d
  refine ⟨d + 1, ?_⟩
  intro n hn
  have hdn : d < n := by omega
  simp [chapter07PowerSeriesTruncation, PowerSeries.coeff_trunc, Nat.lt_of_lt_of_le
    hdn]

-- A Cauchy Laurent-series filter has an eventually fixed coefficient at each degree.
theorem chapter07_laurent_cauchy_coefficients_eventually_stabilize
    (k : Type*) [Field k] {ℱ : Filter (chapter07LaurentSeriesField k)}
    (hℱ : Cauchy ℱ) (D : ℤ) :
    ∀ᶠ f in ℱ, ∀ d : ℤ, d < D →
      LaurentSeries.Cauchy.coeff hℱ d = f.coeff d := by
  exact LaurentSeries.Cauchy.coeff_eventually_equal hℱ

-- The coefficient sequence attached to a Laurent Cauchy filter has a uniform lower bound.
theorem chapter07_laurent_cauchy_limit_has_uniform_lower_bound
    (k : Type*) [Field k] {ℱ : Filter (chapter07LaurentSeriesField k)}
    (hℱ : Cauchy ℱ) :
    ∃ N : ℤ, ∀ d : ℤ, d < N →
      (LaurentSeries.Cauchy.limit hℱ).coeff d = 0 := by
  obtain ⟨N, hN⟩ := LaurentSeries.Cauchy.exists_lb_support hℱ
  refine ⟨N, ?_⟩
  intro d hd
  exact hN d hd

-- The Laurent-series Cauchy limit is the coefficientwise limit constructed from stabilization.
theorem chapter07_laurent_cauchy_limit_is_a_laurent_series
    (k : Type*) [Field k] {ℱ : Filter (chapter07LaurentSeriesField k)}
    (hℱ : Cauchy ℱ) :
    ∀ d : ℤ,
      (LaurentSeries.Cauchy.limit hℱ).coeff d =
        LaurentSeries.Cauchy.coeff hℱ d := by
  intro d
  rfl

-- Rational truncations approximate every Laurent series in the valuation topology.
theorem chapter07_laurent_series_have_rational_approximations
    (k : Type*) [Field k] (f : chapter07LaurentSeriesField k) :
  f ∈ closure
      (Set.range ((↑) : chapter07RationalFunctionField k →
        chapter07LaurentSeriesField k)) := by
  exact LaurentSeries.coe_range_dense f

/-! ### 7.6. The chosen valuation controls the completion -/

abbrev chapter07ArchimedeanRationalCompletion : Type _ :=
  ℝ

-- The usual completion of ℚ is the real field.
theorem chapter07_rationals_have_real_completion :
    ∃ e : UniformSpace.Completion ℚ ≃ᵤ
        chapter07ArchimedeanRationalCompletion,
      ∀ q : ℚ,
        e.toFun ((@UniformSpace.Completion.cPkg ℚ inferInstance).coe q) =
        (q : chapter07ArchimedeanRationalCompletion) := by
  let B : @AbstractCompletion ℚ inferInstance :=
    { space := ℝ
      coe := (↑)
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := by
        exact Rat.isUniformEmbedding_coe_real.isUniformInducing
      dense := Rat.isDenseEmbedding_coe_real.dense }
  refine ⟨(@UniformSpace.Completion.cPkg ℚ inferInstance).compareEquiv B, ?_⟩
  intro q
  dsimp [AbstractCompletion.compareEquiv]
  have h := AbstractCompletion.compare_coe
    (@UniformSpace.Completion.cPkg ℚ inferInstance) B q
  simpa [B] using h

-- The same abstract field ℚ has the distinct p-adic completion with p-adic uniformity.
theorem chapter07_rationals_have_padic_completion
    (p : ℕ) [Fact p.Prime] :
    ∃ e : @UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p) ≃ᵤ
        chapter07PAdicField p,
      ∀ q : ℚ,
        e (q : @UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p)) =
          (q : chapter07PAdicField p) := by
  exact chapter07_padic_field_is_the_padic_completion p

-- Each chosen uniformity on an abstract field has its own standard completion;
-- the completion is complete and contains the original space densely.
theorem chapter07_completion_for_chosen_uniformity_is_complete_and_dense
    (K : Type*) (u : UniformSpace K) :
    DenseRange (@UniformSpace.Completion.coe' K u) ∧
      @CompleteSpace (@UniformSpace.Completion K u)
        (@UniformSpace.Completion.uniformSpace K u) := by
  exact ⟨UniformSpace.Completion.denseRange_coe, inferInstance⟩

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter07
