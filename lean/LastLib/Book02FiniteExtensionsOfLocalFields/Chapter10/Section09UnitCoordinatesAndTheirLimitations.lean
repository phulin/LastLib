import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section03HigherQuotientsAreAdditiveResidueFields

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10

noncomputable section

open Ideal IsLocalRing
open Filter
open scoped BigOperators
open scoped Topology Pointwise

/-! ## 10.9. Unit coordinates and their limitations -/

/-- A choice of representatives for the residue field, with zero represented by zero. -/
def Chapter10ResidueRepresentativeSection
    {L : Type*} [Field L] (A : ValuationSubring L) : Prop :=
  ∃ s : Chapter10ResidueField A → A,
    s 0 = 0 ∧ Function.RightInverse s (IsLocalRing.residue A)

/-- A chosen uniformizer and residue representatives, kept explicit because coordinates depend on them. -/
structure Chapter10UnitCoordinateChoice
    {L : Type*} [Field L] (A : ValuationSubring L) where
  representatives : Chapter10ResidueField A → A
  representatives_zero : representatives 0 = 0
  representatives_rightInverse :
    Function.RightInverse representatives (IsLocalRing.residue A)
  uniformizer : A
  uniformizer_spec : Chapter10Uniformizer A uniformizer

/-- A correction represented by one residue digit at the next uniformizer layer. -/
def Chapter10UnitCoordinateCorrection
    {L : Type*} [Field L] (A : ValuationSubring L)
    (choice : Chapter10UnitCoordinateChoice A)
    (n : ℕ) (c : Aˣ) : Prop :=
  ∃ a : Chapter10ResidueField A,
    (c : A) = 1 + choice.representatives a * choice.uniformizer ^ (n + 1)

private theorem chapter10_coordinate_correction_step
    {L : Type*} [Field L] (A : ValuationSubring L)
    (choice : Chapter10UnitCoordinateChoice A)
    (hDVR : IsDiscreteValuationRing A)
    (n : ℕ) (hn : 0 < n) (r : Aˣ)
    (hr : r ∈ chapter10UnitFiltration A n) :
    ∃ a : Chapter10ResidueField A, ∃ c : Aˣ,
      (c : A) = 1 + choice.representatives a * choice.uniformizer ^ n ∧
        r / c ∈ chapter10UnitFiltration A (n + 1) := by
  classical
  let _ : IsDiscreteValuationRing A := hDVR
  let hπ' : Irreducible choice.uniformizer :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer
      (R := A) choice.uniformizer).2 choice.uniformizer_spec.2
  have hr' : (r : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n := by
    change (r : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n at hr
    exact hr
  let q : Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n :=
    Submodule.Quotient.mk
      (p := chapter10IdealLayerDenominator A (IsLocalRing.maximalIdeal A) n)
      (⟨(r : A) - 1, hr'⟩ :
        (IsLocalRing.maximalIdeal A ^ n : Ideal A))
  obtain ⟨abar, habar⟩ :=
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap_bijective
      (A := A) choice.uniformizer hπ' n).2 q
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective abar
  let a : Chapter10ResidueField A := IsLocalRing.residue A a₀
  have hsection (b : Chapter10ResidueField A) :
      IsLocalRing.residue A (choice.representatives b) = b := by
    exact choice.representatives_rightInverse b
  have hrep : IsLocalRing.residue A (choice.representatives a) =
      IsLocalRing.residue A a₀ := by
    simpa [a] using hsection a
  have hdiff : a₀ - choice.representatives a ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa [map_sub] using sub_eq_zero.mpr hrep.symm
  have hπpow (k : ℕ) : choice.uniformizer ^ k ∈
      (IsLocalRing.maximalIdeal A) ^ k := by
    rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have hmul : (a₀ - choice.representatives a) * choice.uniformizer ^ n ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
    have hprod : (IsLocalRing.maximalIdeal A) *
        (IsLocalRing.maximalIdeal A) ^ n =
        (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
      calc
        (IsLocalRing.maximalIdeal A) *
            (IsLocalRing.maximalIdeal A) ^ n =
            (IsLocalRing.maximalIdeal A) ^ (1 + n) :=
          (by
            simpa only [pow_one] using
              (Ideal.IsTwoSided.pow_add
                (I := IsLocalRing.maximalIdeal A) 1 n).symm)
        _ = (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
          (congr 1; omega)
    have hmem := Ideal.mul_mem_mul hdiff (hπpow n)
    rw [hprod] at hmem
    exact hmem
  have hlayer :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerRepresentative
          (A := A) choice.uniformizer hπ' n a₀ =
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerRepresentative
          (A := A) choice.uniformizer hπ' n (choice.representatives a) := by
    apply (Submodule.Quotient.eq _).2
    change (a₀ * choice.uniformizer ^ n -
        choice.representatives a * choice.uniformizer ^ n) ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1)
    rw [← sub_mul]
    exact hmul
  have hmap := habar
  rw [← ha₀] at hmap
  rw [LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerMultiplicationMap_apply
    (A := A) choice.uniformizer hπ' n a₀] at hmap
  have hclass : q =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.chapterLayerRepresentative
        (A := A) choice.uniformizer hπ' n (choice.representatives a) := by
    exact hmap.symm.trans hlayer
  have hdiff_layer : (r : A) - 1 -
      choice.representatives a * choice.uniformizer ^ n ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
    have hqeq :=
      (Submodule.Quotient.eq
        (chapter10IdealLayerDenominator A (IsLocalRing.maximalIdeal A) n)).mp hclass
    change (r : A) - 1 -
        choice.representatives a * choice.uniformizer ^ n ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1) at hqeq
    exact hqeq
  have hp : (IsLocalRing.maximalIdeal A) ^ n ≤
      IsLocalRing.maximalIdeal A := by
    simpa [pow_one] using
      (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal A) hn)
  have hterm : choice.representatives a * choice.uniformizer ^ n ∈
      IsLocalRing.maximalIdeal A :=
    Ideal.mul_mem_left _ _ (hp (hπpow n))
  have hnegmax : -(choice.representatives a * choice.uniformizer ^ n) ∈
      IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).neg_mem hterm
  have hneg : -(choice.representatives a * choice.uniformizer ^ n) ∈
      nonunits A :=
    (IsLocalRing.mem_maximalIdeal _).1 hnegmax
  have hunit : IsUnit (1 + choice.representatives a * choice.uniformizer ^ n) := by
    have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      (-(choice.representatives a * choice.uniformizer ^ n)) hneg
    (convert h using 1; ring)
  let c : Aˣ := hunit.unit
  have hcval : (c : A) =
      1 + choice.representatives a * choice.uniformizer ^ n := by
    dsimp [c]
  have hrc : (r : A) - (c : A) ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
    have heq : (r : A) - (c : A) = (r : A) - 1 -
        choice.representatives a * choice.uniformizer ^ n := by
      rw [hcval]
      ring
    rw [heq]
    exact hdiff_layer
  have hinv : ((c⁻¹ : Aˣ) : A) * ((r : A) - (c : A)) ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1) :=
    Ideal.mul_mem_left _ _ hrc
  have hidentity : ((r / c : Aˣ) : A) - 1 =
      ((c⁻¹ : Aˣ) : A) * ((r : A) - (c : A)) := by
    change (r : A) * ((c⁻¹ : Aˣ) : A) - 1 =
      ((c⁻¹ : Aˣ) : A) * ((r : A) - (c : A))
    have hcinv : (c : A) * ((c⁻¹ : Aˣ) : A) = 1 := by
      have h := congrArg Units.val (show c * c⁻¹ = (1 : Aˣ) by simp)
      exact h
    rw [mul_sub, mul_comm (r : A) ((c⁻¹ : Aˣ) : A),
      mul_comm ((c⁻¹ : Aˣ) : A) (c : A), hcinv]
  refine ⟨a, c, hcval, ?_⟩
  change ((r / c : Aˣ) : A) - 1 ∈
    (IsLocalRing.maximalIdeal A) ^ (n + 1)
  rw [hidentity]
  exact hinv

/-- With chosen residue representatives and a uniformizer, corrections can be
chosen one graded digit at a time. -/
theorem chapter10_units_have_coordinatewise_successive_correction_expansions
    {L : Type*} [Field L] (A : ValuationSubring L)
    [UniformSpace Aˣ] [IsTopologicalGroup Aˣ] [CompleteSpace Aˣ]
    [T2Space Aˣ]
    (_hDVR : IsDiscreteValuationRing A)
    (_htop : Chapter10UnitFiltrationNeighborhoodBasis
      (chapter10UnitFiltration A))
    (choice : Chapter10UnitCoordinateChoice A) :
    ∀ (u s₀ : Aˣ),
      chapter10UnitReduction A s₀ = chapter10UnitReduction A u →
      ∃ c : ℕ → Aˣ,
        Chapter10SuccessiveUnitCorrectionProduct A u s₀ c ∧
          ∀ n, Chapter10UnitCoordinateCorrection A choice n (c n) := by
  classical
  let _ : IsDiscreteValuationRing A := _hDVR
  let U : ℕ → Subgroup Aˣ := chapter10UnitFiltration A
  intro u s₀ hred
  let d : Aˣ := s₀⁻¹ * u
  have hd : d ∈ U 1 := by
    change ((d : Aˣ) : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1
    rw [pow_one, ← IsLocalRing.residue_eq_zero_iff]
    have hunit : chapter10UnitReduction A d = 1 := by
      dsimp [d]
      rw [map_mul, map_inv, hred]
      simp
    have hval := congrArg Units.val hunit
    simpa [chapter10UnitReduction, map_sub] using sub_eq_zero.mpr hval
  have hstep (n : ℕ) (z : {r : Aˣ // r ∈ U (n + 1)}) :
      ∃ a : Chapter10ResidueField A, ∃ c : Aˣ,
        (c : A) = 1 + choice.representatives a * choice.uniformizer ^ (n + 1) ∧
          z.1 / c ∈ U (n + 2) := by
    simpa [U] using
      (chapter10_coordinate_correction_step A choice _hDVR (n + 1)
        (Nat.succ_pos n) z.1 z.2)
  let correction : ∀ n : ℕ, {r : Aˣ // r ∈ U (n + 1)} → Aˣ := fun n z =>
    Classical.choose (Classical.choose_spec (hstep n z))
  have hcorrection (n : ℕ) (z : {r : Aˣ // r ∈ U (n + 1)}) :
      ∃ a : Chapter10ResidueField A,
        (correction n z : A) =
            1 + choice.representatives a * choice.uniformizer ^ (n + 1) ∧
          z.1 / correction n z ∈ U (n + 2) := by
    refine ⟨Classical.choose (hstep n z), ?_⟩
    change
      ((Classical.choose (Classical.choose_spec (hstep n z)) : Aˣ) : A) =
          1 + choice.representatives (Classical.choose (hstep n z)) *
            choice.uniformizer ^ (n + 1) ∧
        z.1 / (Classical.choose (Classical.choose_spec (hstep n z)) : Aˣ) ∈
          U (n + 2)
    exact Classical.choose_spec (Classical.choose_spec (hstep n z))
  have hcorrection_residual (n : ℕ)
      (z : {r : Aˣ // r ∈ U (n + 1)}) :
      z.1 / correction n z ∈ U (n + 2) := by
    have hs := Classical.choose_spec (Classical.choose_spec (hstep n z))
    simpa [correction] using hs.2
  let R : ∀ n : ℕ, {r : Aˣ // r ∈ U (n + 1)} :=
    Nat.rec ⟨d, hd⟩ (fun n z =>
      ⟨z.1 / correction n z, hcorrection_residual n z⟩)
  let c : ℕ → Aˣ := fun n => correction n (R n)
  let digit : ℕ → Chapter10ResidueField A := fun n =>
    Classical.choose (hstep n (R n))
  have hc (n : ℕ) :
      (c n : A) = 1 + choice.representatives (digit n) *
          choice.uniformizer ^ (n + 1) ∧
        (R n).1 / c n ∈ U (n + 2) := by
    change
      ((Classical.choose (Classical.choose_spec (hstep n (R n))) : Aˣ) : A) =
          1 + choice.representatives (Classical.choose (hstep n (R n))) *
            choice.uniformizer ^ (n + 1) ∧
        (R n).1 /
            (Classical.choose (Classical.choose_spec (hstep n (R n))) : Aˣ) ∈
          U (n + 2)
    exact Classical.choose_spec (Classical.choose_spec (hstep n (R n)))
  have hR_zero : (R 0).1 = d := by
    rfl
  have hR_succ (n : ℕ) : (R (n + 1)).1 = (R n).1 / c n := by
    simp [R, c]
  have hprod (N : ℕ) :
      (R N).1 = d / Finset.prod (Finset.range N) c := by
    induction N with
    | zero => simp [hR_zero]
    | succ N ih =>
        rw [hR_succ N, ih, Finset.prod_range_succ]
        exact div_div _ _ _
  let hπ' : Irreducible choice.uniformizer :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer
      (R := A) choice.uniformizer).2 choice.uniformizer_spec.2
  have hπpow (n : ℕ) : choice.uniformizer ^ n ∈
      (IsLocalRing.maximalIdeal A) ^ n := by
    rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have hcmem (n : ℕ) : c n ∈ U (n + 1) := by
    change (c n : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1)
    rw [(hc n).1]
    simpa only [add_sub_cancel_left] using
      (Ideal.mul_mem_left ((IsLocalRing.maximalIdeal A) ^ (n + 1))
        (choice.representatives (digit n)) (hπpow (n + 1)))
  have hdesc {a b : ℕ} (hab : a ≤ b) : U b ≤ U a := by
    intro x hx
    change (x : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ b at hx
    change (x : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ a
    exact (Ideal.pow_le_pow_right hab) hx
  have happrox (N : ℕ) :
      u * (s₀ * Finset.prod (Finset.range N) c)⁻¹ ∈ U (N + 1) := by
    have heq : u * (s₀ * Finset.prod (Finset.range N) c)⁻¹ = (R N).1 := by
      rw [hprod N]
      simp [d, div_eq_mul_inv, mul_assoc, mul_comm]
    rw [heq]
    exact (R N).property
  have hconv :
      Filter.Tendsto (fun N : ℕ => s₀ * Finset.prod (Finset.range N) c)
        Filter.atTop (𝓝 u) := by
    rw [Filter.tendsto_def]
    intro s hs
    have hpre : (fun z : Aˣ => u * z) ⁻¹' s ∈ 𝓝 (1 : Aˣ) := by
      have hs' : s ∈ 𝓝 ((Homeomorph.mulLeft u) (1 : Aˣ)) := by
        simpa using hs
      simpa using
        ((Homeomorph.mulLeft u).continuous.continuousAt (x := (1 : Aˣ))).preimage_mem_nhds hs'
    have htranslate : u⁻¹ • s ∈ 𝓝 (1 : Aˣ) := by
      have heq : (fun z : Aˣ => u * z) ⁻¹' s = u⁻¹ • s := by
        ext z
        constructor
        · intro hz
          change u * z ∈ s at hz
          exact Set.mem_smul_set.mpr ⟨u * z, hz, by simp⟩
        · intro hz
          rcases Set.mem_smul_set.mp hz with ⟨y, hy, hyz⟩
          change u * z ∈ s
          change u⁻¹ * y = z at hyz
          rw [← hyz]
          simpa using hy
      rw [← heq]
      exact hpre
    obtain ⟨n, hn⟩ := _htop.2 (u⁻¹ • s) htranslate
    filter_upwards [Filter.eventually_atTop.2 ⟨n, fun N hN => hN⟩] with N hN
    have hratio :
        (s₀ * Finset.prod (Finset.range N) c) / u ∈ U (N + 1) := by
      have hi := (U (N + 1)).inv_mem (happrox N)
      simpa [div_eq_mul_inv, mul_comm] using hi
    have hratio' :
        (s₀ * Finset.prod (Finset.range N) c) / u ∈ U n :=
      hdesc (by omega) hratio
    rcases Set.mem_smul_set.mp (hn hratio') with ⟨y, hy, hyz⟩
    have hyz' : u⁻¹ * y =
        u⁻¹ * (s₀ * Finset.prod (Finset.range N) c) := by
      change u⁻¹ * y =
        (s₀ * Finset.prod (Finset.range N) c) / u at hyz
      simpa [div_eq_mul_inv, mul_comm] using hyz
    have hyeq : y = s₀ * Finset.prod (Finset.range N) c := by
      calc
        y = u * (u⁻¹ * y) := by simp
        _ = u * (u⁻¹ * (s₀ * Finset.prod (Finset.range N) c)) := by
          rw [hyz']
        _ = s₀ * Finset.prod (Finset.range N) c := by simp
    change s₀ * Finset.prod (Finset.range N) c ∈ s
    rw [← hyeq]
    exact hy
  refine ⟨c, ?_, ?_⟩
  · exact ⟨hcmem, happrox, hconv⟩
  · intro n
    exact ⟨digit n, (hc n).1⟩

/-- The coefficientwise logarithm terms `(-1)ⁿ xⁿ⁺¹/(n+1)`. -/
def chapter10LogTerm {L : Type*} [Field L] (x : L) (n : ℕ) : L :=
  (-1 : L) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : L)

/-- The coefficientwise exponential terms `xⁿ/n!`. -/
def chapter10ExpTerm {L : Type*} [Field L] (x : L) (n : ℕ) : L :=
  x ^ n / ((Nat.factorial n : ℕ) : L)

/-- Convergence predicates for the two formal series. -/
def Chapter10LogSeriesConverges {L : Type*} [Field L] [TopologicalSpace L]
    (x : L) : Prop := Summable (chapter10LogTerm x)

def Chapter10ExpSeriesConverges {L : Type*} [Field L] [TopologicalSpace L]
    (x : L) : Prop := Summable (chapter10ExpTerm x)

/-- The abstract group equivalence supplied by convergent logarithm and exponential series. -/
structure Chapter10LogExpLinearization
    {L : Type*} [Field L] [TopologicalSpace L]
    (U : Subgroup Lˣ) (I : AddSubgroup L) where
  log : Additive U →+ I
  exp : Multiplicative I →* U
  log_converges : ∀ u : U,
    Chapter10LogSeriesConverges (((u : Lˣ) : L) - 1)
  exp_converges : ∀ x : I,
    Chapter10ExpSeriesConverges (x : L)
  log_eq_series : ∀ u : U,
    ((log (Additive.ofMul u) : I) : L) =
      ∑' n, chapter10LogTerm (((u : Lˣ) : L) - 1) n
  exp_eq_series : ∀ x : I,
    (((exp (Multiplicative.ofAdd x) : U) : Lˣ) : L) =
      ∑' n, chapter10ExpTerm (x : L) n
  exp_log : ∀ u, exp (Multiplicative.ofAdd (log (Additive.ofMul u))) = u
  log_exp : ∀ x, log (Additive.ofMul (exp (Multiplicative.ofAdd x))) = x

/-- Deep enough principal units provide a log/exp identification once convergence is established. -/
theorem chapter10_deep_principal_units_log_exp
    {L : Type*} [Field L] [TopologicalSpace L]
    (U : Subgroup Lˣ) (I : AddSubgroup L)
    (hseries : ∃ log : Additive U →+ I, ∃ exp : Multiplicative I →* U,
      (∀ u : U, Chapter10LogSeriesConverges (((u : Lˣ) : L) - 1)) ∧
        (∀ x : I, Chapter10ExpSeriesConverges (x : L)) ∧
        (∀ u : U, ((log (Additive.ofMul u) : I) : L) =
          ∑' n, chapter10LogTerm (((u : Lˣ) : L) - 1) n) ∧
        (∀ x : I, (((exp (Multiplicative.ofAdd x) : U) : Lˣ) : L) =
          ∑' n, chapter10ExpTerm (x : L) n) ∧
        (∀ u, exp (Multiplicative.ofAdd (log (Additive.ofMul u))) = u) ∧
        (∀ x, log (Additive.ofMul (exp (Multiplicative.ofAdd x))) = x)) :
    Nonempty (Chapter10LogExpLinearization U I) := by
  rcases hseries with
    ⟨log, exp, hlog_converges, hexp_converges, hlog_eq_series,
      hexp_eq_series, hexp_log, hlog_exp⟩
  exact ⟨{
    log := log
    exp := exp
    log_converges := hlog_converges
    exp_converges := hexp_converges
    log_eq_series := hlog_eq_series
    exp_eq_series := hexp_eq_series
    exp_log := hexp_log
    log_exp := hlog_exp }⟩

/-- The characteristic-free linear part is already the map `1+x ↦ x` on each layer. -/
theorem chapter10_first_order_principal_unit_linearization
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (hn : 0 < n) :
    Nonempty
      (Multiplicative
          (Chapter10IdealLayer A (IsLocalRing.maximalIdeal A) n) ≃*
        Chapter10UnitLayerQuotient A n) :=
  ⟨Classical.choose (chapter10_higher_unit_layer_is_additive A n hn)⟩

/-- An additive coefficient-field section of reduction. -/
def Chapter10CoefficientFieldSection
    {L : Type*} [Field L] (A : ValuationSubring L) : Prop :=
  ∃ s : Chapter10ResidueField A →+* A,
    ∀ a, IsLocalRing.residue A (s a) = a

/-- In mixed characteristic, reduction need not have an additive coefficient-field section. -/
theorem chapter10_mixed_characteristic_no_coefficient_field_section
    {L : Type*} [Field L] (A : ValuationSubring L) [CharZero A]
    (p : ℕ) [Fact p.Prime] [CharP (Chapter10ResidueField A) p] :
    ¬ Chapter10CoefficientFieldSection A := by
  rintro ⟨s, hs⟩
  have hpzero : (p : Chapter10ResidueField A) = 0 :=
    CharP.cast_eq_zero (Chapter10ResidueField A) p
  have hpA : (p : A) = 0 := by
    calc
      (p : A) = s (p : Chapter10ResidueField A) := by
        symm
        exact map_natCast s p
      _ = s 0 := by rw [hpzero]
      _ = 0 := map_zero s
  exact (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero) hpA

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10
