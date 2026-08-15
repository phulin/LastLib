import LastLib.Book06GlobalClassFieldTheory.Chapter01.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section01WhyUnitsNeedTheirOwnFiltration

namespace LastLib.Book06GlobalClassFieldTheory.Chapter01

open Set
open scoped BigOperators NumberField

noncomputable section

universe uF uk

/-! ## 1.2. Conventions at finite and infinite places -/

abbrev FinitePlaceResidueField {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) :=
  IsLocalRing.ResidueField (v.adicCompletionIntegers K)

def finitePlaceMaximalIdeal {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) : Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)

/- The principal-unit part of the standard finite-place filtration. -/
def finitePlacePrincipalUnitSet {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) (n : ℕ) : Set (BookPlace.completion (Sum.inl v)) :=
  {x | ∃ y : v.adicCompletionIntegers K,
      y ∈ (finitePlaceMaximalIdeal v) ^ n ∧
      x = 1 + algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y}

/- `U⁰ = Oᵥˣ` and `Uⁿ = 1 + 𝔭ᵥⁿ` for n ≥ 1. -/
def finitePlaceUnitFiltration {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) (n : ℕ) : Set (BookPlace.completion (Sum.inl v)) :=
  if n = 0 then finitePlaceUnitSet v else finitePlacePrincipalUnitSet v n

theorem finitePlaceUnitFiltration_zero {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) :
    finitePlaceUnitFiltration v 0 = finitePlaceUnitSet v := by
  simp [finitePlaceUnitFiltration]

theorem finitePlaceUnitFiltration_of_pos {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) {n : ℕ} (hn : 0 < n) :
    finitePlaceUnitFiltration v n = finitePlacePrincipalUnitSet v n := by
  simp [finitePlaceUnitFiltration, Nat.ne_of_gt hn]

theorem finitePlaceUnitFiltration_succ_nested
    {K : Type*} [Field K] [NumberField K] (v : FinitePlaceIndex K) (n : ℕ) :
    finitePlaceUnitFiltration v (n + 1) ⊆ finitePlaceUnitFiltration v n := by
  intro x hx
  cases n with
  | zero =>
      have hx' : x ∈ finitePlacePrincipalUnitSet v 1 := by
        rw [← finitePlaceUnitFiltration_of_pos v (Nat.zero_lt_succ 0)]
        exact hx
      rcases hx' with ⟨y, hy, hxy⟩
      rw [finitePlaceUnitFiltration_zero]
      change ∃ u : (v.adicCompletionIntegers K)ˣ,
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (u : _) = x
      have hy₁ : y ∈ finitePlaceMaximalIdeal v := by
        simpa [pow_one] using hy
      have hunit : IsUnit (1 + y) := by
        apply IsLocalRing.notMem_maximalIdeal.mp
        intro hmem
        have hone : (1 : v.adicCompletionIntegers K) ∈
            finitePlaceMaximalIdeal v := by
          have hsub := sub_mem hmem hy₁
          simpa only [add_sub_cancel_right, finitePlaceMaximalIdeal] using hsub
        exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) hone
      refine ⟨hunit.unit, ?_⟩
      rw [hunit.unit_spec]
      rw [hxy]
      simp
  | succ n =>
      simp [finitePlaceUnitFiltration] at hx ⊢
      rcases hx with ⟨y, hy, hxy⟩
      refine ⟨y, ?_, hxy⟩
      exact (Ideal.pow_le_pow_right (Nat.succ n).le_succ) hy

theorem finitePlaceUnitFiltration_is_subgroup
    {K : Type*} [Field K] [NumberField K] (v : FinitePlaceIndex K) (n : ℕ) :
    ∃ H : Subgroup (BookPlace.completion (Sum.inl v))ˣ,
      (H : Set ((BookPlace.completion (Sum.inl v))ˣ)) =
        {u : (BookPlace.completion (Sum.inl v))ˣ |
          (u : BookPlace.completion (Sum.inl v)) ∈
            finitePlaceUnitFiltration v n} := by
  refine ⟨LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10FieldUnitFiltration
    (v.adicCompletionIntegers K) n, ?_⟩
  ext u
  change u ∈ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10FieldUnitFiltration
      (v.adicCompletionIntegers K) n ↔
    (u : v.adicCompletion K) ∈ finitePlaceUnitFiltration v n
  cases n with
  | zero =>
      rw [finitePlaceUnitFiltration_zero]
      have hzero :=
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_field_filtration_zero_one
          (v.adicCompletionIntegers K)).1
      rw [hzero]
      constructor
      · intro hu
        change ∃ a : (v.adicCompletionIntegers K)ˣ,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (a : _) =
            (u : v.adicCompletion K)
        let a : (v.adicCompletionIntegers K)ˣ :=
          (v.adicCompletionIntegers K).unitGroupMulEquiv
            ⟨u, hu⟩
        refine ⟨a, ?_⟩
        change ((v.adicCompletionIntegers K).unitGroupMulEquiv
            (⟨u, hu⟩ : (v.adicCompletionIntegers K).unitGroup) :
              v.adicCompletionIntegers K) = (u : v.adicCompletion K)
        exact (v.adicCompletionIntegers K).coe_unitGroupMulEquiv_apply
          ⟨u, hu⟩
      · intro hu
        change ∃ a : (v.adicCompletionIntegers K)ˣ,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (a : _) =
            (u : v.adicCompletion K) at hu
        rcases hu with ⟨a, ha⟩
        let z : (v.adicCompletionIntegers K).unitGroup :=
          (v.adicCompletionIntegers K).unitGroupMulEquiv.symm a
        have hz : (z : (v.adicCompletion K)ˣ) = u := by
          apply Units.ext
          change algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
              (a : v.adicCompletionIntegers K) = (u : v.adicCompletion K)
          exact ha
        rw [← hz]
        exact z.property
  | succ n =>
      simp [finitePlaceUnitFiltration]
      rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10FieldUnitFiltration]
      constructor
      · intro hu
        rcases Subgroup.mem_map.mp hu with ⟨a, ha, hua⟩
        change ((a : v.adicCompletionIntegers K) - 1) ∈
            (finitePlaceMaximalIdeal v) ^ (n + 1) at ha
        refine ⟨(a : v.adicCompletionIntegers K) - 1, ha, ?_⟩
        rw [← congrArg Units.val hua]
        change algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            (a : v.adicCompletionIntegers K) =
          1 + algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
            ((a : v.adicCompletionIntegers K) - 1)
        simp
      · intro hu
        rcases hu with ⟨y, hy, huy⟩
        have hy₁ : y ∈ finitePlaceMaximalIdeal v := by
          simpa only [pow_one] using
            (Ideal.pow_le_pow_right
              (Nat.succ_le_succ (Nat.zero_le n))) hy
        have hunit : IsUnit (1 + y) := by
          apply IsLocalRing.notMem_maximalIdeal.mp
          intro hmem
          have hone : (1 : v.adicCompletionIntegers K) ∈
              finitePlaceMaximalIdeal v := by
            have hsub := sub_mem hmem hy₁
            simpa only [add_sub_cancel_right, finitePlaceMaximalIdeal] using hsub
          exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) hone
        refine Subgroup.mem_map.mpr ⟨hunit.unit, ?_, ?_⟩
        · change ((hunit.unit : v.adicCompletionIntegers K) - 1) ∈
            (finitePlaceMaximalIdeal v) ^ (n + 1)
          rw [hunit.unit_spec]
          simpa using hy
        · apply Units.ext
          change algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
              (hunit.unit : v.adicCompletionIntegers K) = (u : v.adicCompletion K)
          rw [hunit.unit_spec]
          exact huy.symm

/- A stable subgroup representative is needed when local reciprocity is
   stated on a specified unit level. -/
noncomputable def finitePlaceUnitFiltrationSubgroup
    {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) (n : ℕ) :
    Subgroup (BookPlace.completion (Sum.inl v))ˣ :=
  Classical.choose (finitePlaceUnitFiltration_is_subgroup v n)

theorem finitePlaceUnitFiltrationSubgroup_carrier
    {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) (n : ℕ) :
    (finitePlaceUnitFiltrationSubgroup v n :
      Set ((BookPlace.completion (Sum.inl v))ˣ)) =
      {u : (BookPlace.completion (Sum.inl v))ˣ |
        (u : BookPlace.completion (Sum.inl v)) ∈
          finitePlaceUnitFiltration v n} :=
  Classical.choose_spec (finitePlaceUnitFiltration_is_subgroup v n)

@[simp]
theorem finitePlaceUnitFiltrationSubgroup_mem_iff
    {K : Type*} [Field K] [NumberField K]
    (v : FinitePlaceIndex K) (n : ℕ)
    (u : (BookPlace.completion (Sum.inl v))ˣ) :
    u ∈ finitePlaceUnitFiltrationSubgroup v n ↔
      (u : BookPlace.completion (Sum.inl v)) ∈
        finitePlaceUnitFiltration v n := by
  change u ∈ (finitePlaceUnitFiltrationSubgroup v n :
    Set ((BookPlace.completion (Sum.inl v))ˣ)) ↔ _
  rw [finitePlaceUnitFiltrationSubgroup_carrier]
  rfl

/- A residue-field automorphism is arithmetic Frobenius when it is q-power. -/
def arithmeticFrobeniusAction (k : Type*) [MonoidWithZero k] (q : ℕ) : k → k :=
  fun x => x ^ q

def geometricFrobeniusAction {k : Type*} [Field k] (σ : k ≃+* k) : k ≃+* k :=
  σ.symm

theorem geometricFrobeniusAction_inverse {k : Type*} [Field k]
    (σ : k ≃+* k) : geometricFrobeniusAction σ = σ.symm :=
  rfl

/- The local reciprocity normalization at a finite place. -/
structure FiniteReciprocityNormalization
    (F : Type uF) (k : Type uk) [Field F] [Field k] [Fintype k]
    where
  reciprocity : Fˣ →* Field.absoluteGaloisGroupAbelianization F
  valuation : AddValuation F (WithTop ℤ)
  uniformizer : Fˣ
  uniformizer_spec : valuation (uniformizer : F) = (1 : WithTop ℤ)
  /- Frobenius acts on the residue field of an unramified finite level, not on
     the base residue field itself (where q-power is the identity). -/
  residueExtension : Type uk
  [residueExtensionField : Field residueExtension]
  [residueExtensionFintype : Fintype residueExtension]
  [residueExtensionAlgebra : Algebra k residueExtension]
  residueAction : Field.absoluteGaloisGroupAbelianization F →*
    (residueExtension ≃ₐ[k] residueExtension)
  unitSubgroup : Subgroup Fˣ
  unitSubgroup_spec : ∀ u : Fˣ,
    u ∈ unitSubgroup ↔ valuation (u : F) = 0
  inertia : Subgroup (Field.absoluteGaloisGroupAbelianization F)
  unit_image_eq_inertia :
    (reciprocity.comp unitSubgroup.subtype).range = inertia
  q : ℕ
  q_card : q = Fintype.card k
  arithmetic_uniformizer : ∀ x : residueExtension,
    residueAction (reciprocity uniformizer) x =
      arithmeticFrobeniusAction residueExtension q x
  unit_residue_trivial : ∀ u : Fˣ, u ∈ unitSubgroup → ∀ x : residueExtension,
    residueAction (reciprocity u) x = x

/- LOCAL_DEPENDENCY_GUESS: this is the local reciprocity map and its finite
normalization, awaiting the local class-field interfaces. -/
structure LocalReciprocityData (K : Type*) [Field K] [NumberField K] where
  [residueFintype : ∀ v : FinitePlaceIndex K, Fintype (FinitePlaceResidueField v)]
  localReciprocity : (v : BookPlace K) →
    (BookPlace.completion v)ˣ →*
      Field.absoluteGaloisGroupAbelianization (BookPlace.completion v)
  finite_normalization : ∀ v : FinitePlaceIndex K,
    FiniteReciprocityNormalization
      (BookPlace.completion (Sum.inl v)) (FinitePlaceResidueField v)
  finite_reciprocity_agrees : ∀ v : FinitePlaceIndex K,
    (finite_normalization v).reciprocity = localReciprocity (Sum.inl v)

theorem finite_local_reciprocity_uses_arithmetic_frobenius
    {K : Type*} [Field K] [NumberField K]
    (R : LocalReciprocityData K) (v : FinitePlaceIndex K) :
    letI : Fintype (FinitePlaceResidueField v) := R.residueFintype v
    let N := R.finite_normalization v
    letI : Field N.residueExtension := N.residueExtensionField
    letI : Fintype N.residueExtension := N.residueExtensionFintype
    letI : Algebra (FinitePlaceResidueField v) N.residueExtension :=
      N.residueExtensionAlgebra
    ∀ x : N.residueExtension,
      N.residueAction (N.reciprocity N.uniformizer) x = x ^ N.q := by
  let _ : Fintype (FinitePlaceResidueField v) := R.residueFintype v
  let N := R.finite_normalization v
  let _ : Field N.residueExtension := N.residueExtensionField
  let _ : Fintype N.residueExtension := N.residueExtensionFintype
  let _ : Algebra (FinitePlaceResidueField v) N.residueExtension :=
    N.residueExtensionAlgebra
  exact N.arithmetic_uniformizer

/- At an unramified finite prime, the chosen uniformizer maps to arithmetic
Frobenius; geometric Frobenius is its inverse. -/
def GlobalUnramifiedFrobeniusConvention
    (F : Type uF) (k : Type uk) [Field F] [Field k] [Fintype k]
    (R : FiniteReciprocityNormalization F k) : Prop := by
  letI : Field R.residueExtension := R.residueExtensionField
  letI : Fintype R.residueExtension := R.residueExtensionFintype
  letI : Algebra k R.residueExtension := R.residueExtensionAlgebra
  exact ∃ (arith geom : R.residueExtension ≃ₐ[k] R.residueExtension),
    (∀ x : R.residueExtension, arith x = x ^ R.q) ∧
      geom = arith.symm ∧
      (∀ x : R.residueExtension,
        R.residueAction (R.reciprocity R.uniformizer) x = arith x)

theorem global_unramified_prime_uses_arithmetic_convention
    {F : Type uF} {k : Type uk} [Field F] [Field k] [Fintype k]
    (R : FiniteReciprocityNormalization F k)
    (h : GlobalUnramifiedFrobeniusConvention F k R) :
    letI : Field R.residueExtension := R.residueExtensionField
    letI : Fintype R.residueExtension := R.residueExtensionFintype
    letI : Algebra k R.residueExtension := R.residueExtensionAlgebra
    ∃ arith : R.residueExtension ≃ₐ[k] R.residueExtension,
      (∀ x : R.residueExtension, arith x = x ^ R.q) ∧
        ∀ x : R.residueExtension,
          R.residueAction (R.reciprocity R.uniformizer) x = arith x := by
  rcases h with ⟨arith, geom, harith, hgeom, hrec⟩
  exact ⟨arith, harith, hrec⟩

theorem complex_finite_extension_is_trivial
    (L : Type*) [Field L] [Algebra ℂ L] [FiniteDimensional ℂ L] :
    Nonempty (L ≃ₐ[ℂ] ℂ) := by
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId ℂ L)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := L))).symm⟩

/- The complex local reciprocity map is trivial. -/
def complexLocalReciprocity :
    ℂˣ →* Field.absoluteGaloisGroupAbelianization ℂ :=
  1

theorem complex_local_reciprocity_trivial (x : ℂˣ) :
    complexLocalReciprocity x = 1 := by
  simp [complexLocalReciprocity]

/- The real local quotient kills positive units and detects the sign. -/
def positiveRealUnitSubgroup : Subgroup ℝˣ where
  carrier := {u | 0 < (u : ℝ)}
  one_mem' := by norm_num
  mul_mem' := by
    intro a b ha hb
    exact mul_pos (show 0 < (a : ℝ) from ha) (show 0 < (b : ℝ) from hb)
  inv_mem' := by
    intro a ha
    simpa only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val] using
      (inv_pos.mpr (show (0 : ℝ) < (a : ℝ) from ha))

abbrev RealLocalReciprocityQuotient := ℝˣ ⧸ positiveRealUnitSubgroup

def negativeRealUnit : ℝˣ := Units.mk0 (-1) (by norm_num)

/- LOCAL_DEPENDENCY_GUESS: the real local Artin map is the sign quotient
identified with `Gal(ℂ/ℝ)`. -/
def realLocalReciprocity : ℝˣ →* Gal(ℂ / ℝ) := by
  have hconj : (RCLike.conjAe : Gal(ℂ / ℝ)) * RCLike.conjAe = 1 := by
    ext z
    simp [RCLike.conjAe_coe]
  refine
    { toFun := fun u => if 0 < (u : ℝ) then 1 else RCLike.conjAe
      map_one' := by simp
      map_mul' := by
        intro u v
        rcases lt_or_gt_of_ne (Units.ne_zero u) with hu | hu <;>
          rcases lt_or_gt_of_ne (Units.ne_zero v) with hv | hv
        · have huv : 0 < ((u * v : ℝˣ) : ℝ) := by
            simpa using (mul_pos_of_neg_of_neg hu hv)
          have hnu : ¬ 0 < (u : ℝ) := not_lt_of_ge (le_of_lt hu)
          have hnv : ¬ 0 < (v : ℝ) := not_lt_of_ge (le_of_lt hv)
          simpa only [if_pos huv, if_neg hnu, if_neg hnv, one_mul, mul_one]
            using hconj.symm
        · have huv : ((u * v : ℝˣ) : ℝ) < 0 := by
            simpa using (mul_neg_of_neg_of_pos hu hv)
          have hnu : ¬ 0 < (u : ℝ) := not_lt_of_ge (le_of_lt hu)
          have hnuv : ¬ 0 < ((u * v : ℝˣ) : ℝ) := not_lt_of_ge (le_of_lt huv)
          simp only [if_neg hnuv, if_neg hnu, if_pos hv, mul_one]
        · have huv : ((u * v : ℝˣ) : ℝ) < 0 := by
            simpa using (mul_neg_of_pos_of_neg hu hv)
          have hnv : ¬ 0 < (v : ℝ) := not_lt_of_ge (le_of_lt hv)
          have hnuv : ¬ 0 < ((u * v : ℝˣ) : ℝ) := not_lt_of_ge (le_of_lt huv)
          simp only [if_neg hnuv, if_pos hu, if_neg hnv, one_mul]
        · have huv : 0 < ((u * v : ℝˣ) : ℝ) := by
            simpa using (mul_pos hu hv)
          simp only [if_pos huv, if_pos hu, if_pos hv, mul_one] }

def realComplexConjugation : Gal(ℂ / ℝ) :=
  RCLike.conjAe

structure RealLocalReciprocityQuotientEquivalence where
  equiv : RealLocalReciprocityQuotient ≃* Gal(ℂ / ℝ)
  compatible : ∀ u : ℝˣ,
    equiv (QuotientGroup.mk' positiveRealUnitSubgroup u) =
      realLocalReciprocity u

theorem real_local_reciprocity_quotient_equiv :
    Nonempty RealLocalReciprocityQuotientEquivalence := by
  have hconj_ne_one : (RCLike.conjAe : Gal(ℂ / ℝ)) ≠ 1 := by
    intro h
    have hI := congrArg (fun f : Gal(ℂ / ℝ) => f Complex.I) h
    have hIm := congrArg Complex.im hI
    norm_num at hIm
  have hsurj : Function.Surjective realLocalReciprocity := by
    intro σ
    rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with hσ | hσ
    · have hσ' : σ = 1 := by
        ext z
        exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f z) hσ
      exact ⟨1, hσ'.symm ▸ by simp [realLocalReciprocity]⟩
    · have hσ' : σ = realComplexConjugation := by
        ext z
        exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f z) hσ
      refine ⟨negativeRealUnit, ?_⟩
      rw [hσ']
      simp [realLocalReciprocity, negativeRealUnit, realComplexConjugation]
  have hker : positiveRealUnitSubgroup = realLocalReciprocity.ker := by
    ext u
    change 0 < (u : ℝ) ↔ realLocalReciprocity u = 1
    constructor
    · intro hu
      simp [realLocalReciprocity, hu]
    · intro hu
      by_contra hnot
      rcases lt_or_gt_of_ne (Units.ne_zero u) with hneg | hpos
      · have hnu : ¬ 0 < (u : ℝ) := not_lt_of_ge (le_of_lt hneg)
        have : (RCLike.conjAe : Gal(ℂ / ℝ)) = 1 := by
          simpa [realLocalReciprocity, hnu] using hu
        exact hconj_ne_one this
      · exact hnot hpos
  refine ⟨⟨QuotientGroup.liftEquiv positiveRealUnitSubgroup hsurj hker, ?_⟩⟩
  intro u
  simpa only [QuotientGroup.mk'_apply] using
    (QuotientGroup.liftEquiv_mk positiveRealUnitSubgroup hsurj hker u)

theorem real_positive_unit_killed (u : ℝˣ)
    (hu : u ∈ positiveRealUnitSubgroup) :
    realLocalReciprocity u = 1 := by
  change 0 < (u : ℝ) at hu
  simp [realLocalReciprocity, hu]

theorem real_negative_unit_is_complex_conjugation :
    realLocalReciprocity negativeRealUnit = realComplexConjugation := by
  simp [realLocalReciprocity, negativeRealUnit, realComplexConjugation]

/- Infinite-place ramification can only occur over a real place and produces
a complex place. -/
def InfinitePlaceLiesAbove
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (w : InfinitePlaceIndex L) (v : InfinitePlaceIndex K) : Prop :=
  NumberField.InfinitePlace.LiesOver w v

def InfinitePlaceRamifies
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (w : InfinitePlaceIndex L) (v : InfinitePlaceIndex K) : Prop :=
  InfinitePlaceLiesAbove w v ∧
    NumberField.InfinitePlace.IsReal v ∧
    NumberField.InfinitePlace.IsComplex w

theorem complex_infinite_place_never_ramifies
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : InfinitePlaceIndex K)
    (hv : NumberField.InfinitePlace.IsComplex v)
    (w : InfinitePlaceIndex L) :
    ¬ InfinitePlaceRamifies w v := by
  intro h
  exact (NumberField.InfinitePlace.ne_of_isReal_isComplex h.2.1 hv) rfl

theorem real_infinite_place_may_ramify
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (w : InfinitePlaceIndex L) (v : InfinitePlaceIndex K)
    (h : InfinitePlaceRamifies w v) :
    NumberField.InfinitePlace.IsReal v ∧
      NumberField.InfinitePlace.IsComplex w := by
  exact ⟨h.2.1, h.2.2⟩

/- A modulus may contain finite places and real infinite places, but never a
complex infinite place. -/
structure BookModulus (K : Type*) [Field K] [NumberField K] where
  finitePart : FinitePlaceIndex K →₀ ℕ
  infinitePart : Finset (InfinitePlaceIndex K)
  infinitePart_real : ∀ v ∈ infinitePart,
    NumberField.InfinitePlace.IsReal v

def modulusAllowsInfinitePlace {K : Type*} [Field K] [NumberField K]
    (m : BookModulus K) (v : InfinitePlaceIndex K) : Prop :=
  v ∈ m.infinitePart

theorem modulus_never_contains_complex_place
    {K : Type*} [Field K] [NumberField K]
    (m : BookModulus K) (v : InfinitePlaceIndex K)
    (hv : NumberField.InfinitePlace.IsComplex v) :
    ¬ modulusAllowsInfinitePlace m v := by
  intro hv_in
  exact (NumberField.InfinitePlace.ne_of_isReal_isComplex
    (m.infinitePart_real v hv_in) hv) rfl

theorem modulus_real_places_are_permitted
    {K : Type*} [Field K] [NumberField K]
    (m : BookModulus K) (v : InfinitePlaceIndex K)
    (hv : v ∈ m.infinitePart) :
    NumberField.InfinitePlace.IsReal v :=
  m.infinitePart_real v hv

def ideleNormClassImage
  {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) : Set (C_K K) :=
  Set.range (fun x : BookIdeleGroup L =>
    classQuotient (componentwiseIdeleNorm N x))

theorem ideleNormClassImage_eq_classNormGroup
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) :
    ideleNormClassImage N = (classNormGroup N : Set (C_K K)) := by
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    change classQuotient (componentwiseIdeleNorm N x) ∈
      (classNorm N).range
    exact ⟨classQuotient x, classNorm_apply_classQuotient N x⟩
  · intro hc
    change c ∈ (classNorm N).range at hc
    rcases hc with ⟨q, rfl⟩
    rcases QuotientGroup.mk'_surjective (principalIdeleSubgroup L) q with ⟨x, rfl⟩
    exact ⟨x, classNorm_apply_classQuotient N x⟩

theorem classNorm_membership_iff_principal_times_ideleNorm
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) (c : C_K K) :
    c ∈ classNormGroup N ↔
      ∃ x : I_K K, x ∈ principalTimesIdeleNormGroup N ∧ classQuotient x = c := by
  rw [classNormGroup_eq_principal_times_norm_quotient N]
  constructor
  · intro hc
    rcases Subgroup.mem_map.mp hc with ⟨x, hx, hxc⟩
    exact ⟨x, hx, hxc⟩
  · rintro ⟨x, hx, hxc⟩
    exact Subgroup.mem_map.mpr ⟨x, hx, hxc⟩

end
end LastLib.Book06GlobalClassFieldTheory.Chapter01
