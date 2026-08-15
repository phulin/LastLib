import LastLib.Book03RamificationTheory.Chapter02.Section04HigherGradedPieces
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section07GaloisActionOnTheLayers
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace LastLib.Book03RamificationTheory.Chapter02

noncomputable section

open scoped BigOperators Pointwise

universe u

/-! ## 2.5. Action on finite precision and units -/

/-- The precision quotient of a valuation ring. -/
abbrev chapter02PrecisionQuotient
    (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) : Type _ :=
  A ⧸ (IsLocalRing.maximalIdeal A) ^ n

/-- The field-level principal-unit filtration `U_Lⁿ = 1 + 𝔪_Lⁿ`. -/
abbrev chapter02PrincipalUnitGroup
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) : Subgroup Lˣ :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10FieldUnitFiltration A n

/-- The automorphism ratio `σ(u)/u` in the field unit group. -/
def chapter02UnitRatio
    (K : Type u) {L : Type u} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L)
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A)
    (u : Lˣ) : Lˣ :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10GaloisUnitAction
    (σ : Gal(L / K)).toRingEquiv u / u

/-- Membership in the principal-unit group is the expected ideal congruence. -/
theorem chapter02_principal_unit_mem_iff
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) (u : Lˣ) :
    u ∈ chapter02PrincipalUnitGroup A n ↔
      ∃ z : Aˣ, (z : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n ∧
        (z : L) = (u : L) := by
  change u ∈
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A n).map
        (Units.map A.subtype.toMonoidHom) ↔ _
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    rfl
  · rintro ⟨z, hz, hzu⟩
    refine ⟨z, hz, ?_⟩
    exact Units.ext (by simpa using hzu)

/-- The principal-unit filtration is descending. -/
theorem chapter02_principal_unit_group_succ_le
    {L : Type*} [Field L] (A : ValuationSubring L) (n : ℕ) :
    chapter02PrincipalUnitGroup A (n + 1) ≤
      chapter02PrincipalUnitGroup A n := by
  intro u hu
  change u ∈
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A (n + 1)).map
        (Units.map A.subtype.toMonoidHom) at hu
  change u ∈
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration A n).map
        (Units.map A.subtype.toMonoidHom)
  rcases hu with ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  change ((z : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1) at hz
  change ((z : A) - 1) ∈ (IsLocalRing.maximalIdeal A) ^ n
  exact (Ideal.pow_le_pow_right n.le_succ) hz

/- DEPENDENCY_GUESS: The quotient action is the action of the decomposition
   group on `A` descended through the stabilized ideal power.  The canonical
   quotient-lifting declaration is not exposed by the pinned earlier API, so
   this structure records the descended action, its compatibility, and exact
   kernel until reconciliation. -/
/-- A finite-precision action package records the exact kernel. -/
structure Chapter02PrecisionActionData
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (i : ℕ) where
  action :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      K A →* RingAut (chapter02PrecisionQuotient A (i + 1))
  kernel_eq :
    MonoidHom.ker action =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
        K A (i + 1)
  /-- The packaged action is the natural action induced from the valuation ring. -/
  action_apply :
    ∀ (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K A) (x : A),
      action σ (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (i + 1)) x) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (i + 1)) (σ • x)

/-- Every lower group is the kernel of the action visible at its precision. -/
theorem chapter02_precision_action_exists
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring L) (i : ℕ)
    (_hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A) :
    Nonempty (Chapter02PrecisionActionData K L A i) := by
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let J : Ideal A := I ^ (i + 1)
  let e : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      K A →* RingAut A :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05ValuationRingAction K A
  have hmap (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      K A) : J.map (e σ) = J := by
    dsimp [J, I]
    rw [Ideal.map_pow]
    simp
  let qval (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      K A) : RingAut (chapter02PrecisionQuotient A (i + 1)) := by
    change RingAut (A ⧸ J)
    exact Ideal.quotientEquiv J J (e σ) (hmap σ).symm
  have hqval_apply
      (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K A) (x : A) :
      qval σ (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (e σ x) := by
    dsimp [qval]
    exact Ideal.quotientEquiv_mk J J (e σ) (hmap σ).symm x
  let q : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      K A →* RingAut (chapter02PrecisionQuotient A (i + 1)) := {
    toFun := qval
    map_one' := by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      calc
        qval 1 (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (e 1 x) :=
          hqval_apply 1 x
        _ = Ideal.Quotient.mk J x := by simp [e]
    map_mul' := by
      intro σ τ
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      calc
        qval (σ * τ) (Ideal.Quotient.mk J x) =
            Ideal.Quotient.mk J (e (σ * τ) x) := hqval_apply (σ * τ) x
        _ = Ideal.Quotient.mk J (e σ (e τ x)) := by simp [e]
        _ = qval σ (Ideal.Quotient.mk J (e τ x)) := (hqval_apply σ _).symm
        _ = qval σ (qval τ (Ideal.Quotient.mk J x)) := by rw [hqval_apply τ x] }
  have hq_apply
      (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K A) (x : A) :
      q σ (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (i + 1)) x) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (i + 1)) (σ • x) := by
    change q σ (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (e σ x)
    exact hqval_apply σ x
  have hker : MonoidHom.ker q =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
        K A (i + 1) := by
    ext σ
    constructor
    · intro hq
      change q σ = 1 at hq
      change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
        A (i + 1) σ
      intro x
      have hmk' : q σ (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J x := by
        rw [hq]
        rfl
      have hmk : Ideal.Quotient.mk J (e σ x) = Ideal.Quotient.mk J x :=
        (hq_apply σ x).symm.trans hmk'
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr hmk
    · intro hσ
      change q σ = 1
      ext y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      change LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05HigherCongruence
        A (i + 1) σ at hσ
      have hx := hσ x
      change e σ x - x ∈ J at hx
      change q σ (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J x
      have happly : q σ (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (e σ x) := by
        exact hq_apply σ x
      rw [happly, ← sub_eq_zero]
      have hzero : Ideal.Quotient.mk J (e σ x - x) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hx
      simpa only [map_sub] using hzero
  exact ⟨{
    action := q
    kernel_eq := hker
    action_apply := by
      intro σ x
      exact hq_apply σ x }⟩

theorem chapter02_precision_action_apply
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (i : ℕ)
    (D : Chapter02PrecisionActionData K L A i)
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A)
    (x : A) :
    D.action σ (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (i + 1)) x) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (i + 1)) (σ • x) := by
  exact D.action_apply σ x

theorem chapter02_precision_action_mem_iff
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (i : ℕ)
    (D : Chapter02PrecisionActionData K L A i)
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup K A) :
    σ ∈ D.action.ker ↔
      σ ∈ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
        K A (i + 1) := by
  rw [D.kernel_eq]

/-- The exact sequence seen at precision `i+1`. -/
theorem chapter02_precision_action_exact
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (i : ℕ)
    (D : Chapter02PrecisionActionData K L A i) :
    Function.MulExact
        (Subgroup.subtype
          (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
            K A (i + 1))) D.action := by
  intro σ
  constructor
  · intro hσ
    have hker : σ ∈ D.action.ker := (MonoidHom.mem_ker).2 hσ
    rw [D.kernel_eq] at hker
    exact ⟨⟨σ, hker⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    apply (MonoidHom.mem_ker).1
    rw [D.kernel_eq]
    exact τ.property

/-- A finite filtration has trivial intersection. -/
theorem chapter02_lower_filtration_iInf_eq_bot
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) :
    (⨅ n : ℕ, F.group n) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro σ hσ
  obtain ⟨N, hN⟩ := F.eventually_trivial
  have hσ' : ∀ n : ℕ, σ ∈ F.group n := by
    simpa using hσ
  have hσN : σ ∈ F.group N := hσ' N
  rw [hN N le_rfl] at hσN
  exact hσN

/-- An automorphism invisible at every finite precision is the identity. -/
theorem chapter02_invisible_at_every_precision_eq_one
    {G : Type u} [Group G] [Finite G]
    (F : Chapter02LowerFiltration G) (σ : G)
    (hσ : ∀ n : ℕ, σ ∈ F.group n) :
    σ = 1 := by
  have hmem : σ ∈ (⨅ n : ℕ, F.group n) := by
    simpa using hσ
  rw [chapter02_lower_filtration_iInf_eq_bot F] at hmem
  exact hmem

/-- The unit-filtration estimate attached to a lower group. -/
theorem chapter02_unit_ratio_mem_deeper_principal_units
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (_hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (_hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring)
    [Algebra (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring)]
    (i n : ℕ)
    (_hi : 1 ≤ i) (_hn : 1 ≤ n)
    (_hseparable : Algebra.IsSeparable
      (IsLocalRing.ResidueField vK.toValuation.valuationSubring)
      (IsLocalRing.ResidueField vL.toValuation.valuationSubring))
    (σ : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      K vL.toValuation.valuationSubring)
    (hσ : σ ∈ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05RamificationGroup
      K vL.toValuation.valuationSubring (i + 1))
    (u : Lˣ)
    (hu : u ∈ chapter02PrincipalUnitGroup vL.toValuation.valuationSubring n) :
    chapter02UnitRatio K vL.toValuation.valuationSubring σ u ∈
      chapter02PrincipalUnitGroup vL.toValuation.valuationSubring (n + i) := by
  let A := vL.toValuation.valuationSubring
  let I : Ideal A := IsLocalRing.maximalIdeal A
  obtain ⟨z, hz, hzu⟩ :=
    (chapter02_principal_unit_mem_iff A n u).1 hu
  let e : RingAut A := MulSemiringAction.toRingAut _ _ σ
  have hzu' : Units.map A.subtype.toMonoidHom z = u := by
    apply Units.ext
    simpa using hzu
  change ∀ x : A, (σ • x - x) ∈ I ^ (i + 1) at hσ
  have hdelta (x : A) : e x - x ∈ I ^ (i + 1) := by
    change σ • x - x ∈ I ^ (i + 1)
    exact hσ x
  obtain ⟨π, hπ⟩ :=
    Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial vL.toValuation
  have hπI : (π : A) ∈ I := by
    change (π : A) ∈ IsLocalRing.maximalIdeal A
    rw [hπ.is_generator]
    exact Ideal.mem_span_singleton_self _
  have hπpow (m : ℕ) : (π : A) ^ m ∈ I ^ m :=
    Ideal.pow_mem_pow hπI m
  have heπI : e (π : A) ∈ I := by
    change σ • (π : A) ∈ I
    exact
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.decomposition_group_preserves_maximal_ideal
        A σ (π : A)).mp hπI
  have heπpow (m : ℕ) : e (π : A) ^ m ∈ I ^ m :=
    Ideal.pow_mem_pow heπI m
  have hpowdiff : ∀ m : ℕ,
      e (π : A) ^ m - (π : A) ^ m ∈ I ^ (m + i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hleft : e (π : A) ∈ I ^ 1 := by
          simpa [pow_one] using heπI
        have hleft' := Ideal.mul_mem_mul hleft ih
        rw [← Ideal.IsTwoSided.pow_add (I := I) 1 (m + i)] at hleft'
        have hright := Ideal.mul_mem_mul (hdelta (π : A)) (hπpow m)
        rw [← Ideal.IsTwoSided.pow_add (I := I) (i + 1) m] at hright
        have hleft'' :
            e (π : A) * (e (π : A) ^ m - (π : A) ^ m) ∈
              I ^ ((m + 1) + i) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hleft'
        have hright' :
            (e (π : A) - (π : A)) * (π : A) ^ m ∈
              I ^ ((m + 1) + i) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright
        rw [pow_succ, pow_succ]
        have hsum :
            e (π : A) * (e (π : A) ^ m - (π : A) ^ m) +
                (e (π : A) - (π : A)) * (π : A) ^ m ∈
              I ^ ((m + 1) + i) :=
          (I ^ ((m + 1) + i)).add_mem hleft'' hright'
        convert hsum using 1; ring
  obtain ⟨a, ha⟩ : ∃ a : A, a * (π : A) ^ n = (z : A) - 1 := by
    rw [hπ.is_generator, Ideal.span_singleton_pow] at hz
    exact Ideal.mem_span_singleton'.mp hz
  have hfirst :
      (e a - a) * e (π : A) ^ n ∈ I ^ (n + i) := by
    have hfirst' := Ideal.mul_mem_mul (hdelta a) (heπpow n)
    rw [← Ideal.IsTwoSided.pow_add (I := I) (i + 1) n] at hfirst'
    have hle : I ^ ((i + 1) + n) ≤ I ^ (n + i) := by
      exact Ideal.pow_le_pow_right (by omega)
    exact hle hfirst'
  have hsecond :
      a * (e (π : A) ^ n - (π : A) ^ n) ∈ I ^ (n + i) := by
    exact Ideal.mul_mem_left _ _ (hpowdiff n)
  have hdeep' : e ((z : A) - 1) - ((z : A) - 1) ∈ I ^ (n + i) := by
    rw [← ha, map_mul, map_pow]
    have hsum :
        (e a - a) * e (π : A) ^ n +
            a * (e (π : A) ^ n - (π : A) ^ n) ∈ I ^ (n + i) :=
      (I ^ (n + i)).add_mem hfirst hsecond
    convert hsum using 1; ring
  have hdeep : e (z : A) - (z : A) ∈ I ^ (n + i) := by
    convert hdeep' using 1; simp [map_sub]
  let w : Aˣ := Units.map e.toRingHom.toMonoidHom z / z
  have hw : ((w : Aˣ) : A) - 1 ∈ I ^ (n + i) := by
    change (e (z : A) * ((z⁻¹ : Aˣ) : A) - 1) ∈ I ^ (n + i)
    have hmul : ((z⁻¹ : Aˣ) : A) * (e (z : A) - (z : A)) ∈ I ^ (n + i) :=
      Ideal.mul_mem_left _ _ hdeep
    have hzinv : ((z⁻¹ : Aˣ) : A) * (z : A) = 1 := by simp
    have heq :
        e (z : A) * ((z⁻¹ : Aˣ) : A) - 1 =
          ((z⁻¹ : Aˣ) : A) * (e (z : A) - (z : A)) := by
      rw [mul_sub, mul_comm (e (z : A)) ((z⁻¹ : Aˣ) : A), hzinv]
    rw [heq]
    exact hmul
  rw [← hzu']
  apply (chapter02_principal_unit_mem_iff A (n + i) _).2
  refine ⟨w, hw, ?_⟩
  have hunitmap :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10GaloisUnitAction
          (σ : Gal(L / K)).toRingEquiv
          (Units.map A.subtype.toMonoidHom z) =
        Units.map A.subtype.toMonoidHom
          (Units.map e.toRingHom.toMonoidHom z) := by
    apply Units.ext
    rfl
  have hratio_units :
      Units.map A.subtype.toMonoidHom w =
        chapter02UnitRatio K A σ (Units.map A.subtype.toMonoidHom z) := by
    unfold chapter02UnitRatio
    dsimp [w]
    rw [map_div]
    change
      Units.map A.subtype.toMonoidHom
          (Units.map e.toRingHom.toMonoidHom z) /
          Units.map A.subtype.toMonoidHom z =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10GaloisUnitAction
            (σ : Gal(L / K)).toRingEquiv
            (Units.map A.subtype.toMonoidHom z) /
          Units.map A.subtype.toMonoidHom z
    rw [hunitmap]
  exact congrArg (fun q : Lˣ => (q : L)) hratio_units

end

end LastLib.Book03RamificationTheory.Chapter02
