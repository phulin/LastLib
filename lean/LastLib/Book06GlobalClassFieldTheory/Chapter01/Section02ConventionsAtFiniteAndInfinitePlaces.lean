import LastLib.Book06GlobalClassFieldTheory.Chapter01.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter01

open Set
open scoped BigOperators NumberField

noncomputable section

universe uF

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
  sorry

theorem finitePlaceUnitFiltration_is_subgroup
    {K : Type*} [Field K] [NumberField K] (v : FinitePlaceIndex K) (n : ℕ) :
    ∃ H : Subgroup (BookPlace.completion (Sum.inl v))ˣ,
      (H : Set ((BookPlace.completion (Sum.inl v))ˣ)) =
        {u : (BookPlace.completion (Sum.inl v))ˣ |
          (u : BookPlace.completion (Sum.inl v)) ∈
          finitePlaceUnitFiltration v n} := by
  sorry

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
    (F : Type uF) (k : Type*) [Field F] [Field k] [Fintype k]
    where
  reciprocity : Fˣ →* Field.absoluteGaloisGroupAbelianization F
  valuation : AddValuation F (WithTop ℤ)
  uniformizer : Fˣ
  uniformizer_spec : valuation (uniformizer : F) = (1 : WithTop ℤ)
  residueAction : Field.absoluteGaloisGroupAbelianization F →* (k ≃+* k)
  unitSubgroup : Subgroup Fˣ
  inertia : Subgroup (Field.absoluteGaloisGroupAbelianization F)
  unit_image_eq_inertia :
    (reciprocity.comp unitSubgroup.subtype).range = inertia
  unramified : Prop
  unramified_iff_inertia_trivial : unramified ↔ inertia = ⊥
  q : ℕ
  q_card : q = Fintype.card k
  arithmetic_uniformizer : ∀ x : k,
    residueAction (reciprocity uniformizer) x = arithmeticFrobeniusAction k q x

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
    ∀ x : FinitePlaceResidueField v,
      (R.finite_normalization v).residueAction
          ((R.finite_normalization v).reciprocity
            (R.finite_normalization v).uniformizer) x =
        x ^ (R.finite_normalization v).q := by
  sorry

/- At an unramified finite prime, the chosen uniformizer maps to arithmetic
Frobenius; geometric Frobenius is its inverse. -/
def GlobalUnramifiedFrobeniusConvention (k : Type*) [Field k] [Fintype k] : Prop :=
  ∃ (arith geom : k ≃+* k),
    (∀ x : k, arith x = x ^ Fintype.card k) ∧ geom = arith.symm

theorem global_unramified_prime_uses_arithmetic_convention
    {k : Type*} [Field k] [Fintype k]
    (h : GlobalUnramifiedFrobeniusConvention k) :
    ∃ arith : k ≃+* k, ∀ x : k, arith x = x ^ Fintype.card k := by
  rcases h with ⟨arith, geom, harith, hgeom⟩
  exact ⟨arith, harith⟩

theorem complex_finite_extension_is_trivial
    (L : Type*) [Field L] [Algebra ℂ L] [FiniteDimensional ℂ L] :
    Nonempty (L ≃ₐ[ℂ] ℂ) := by
  sorry

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
  sorry

def realComplexConjugation : Gal(ℂ / ℝ) :=
  RCLike.conjAe

structure RealLocalReciprocityQuotientEquivalence where
  equiv : RealLocalReciprocityQuotient ≃* Gal(ℂ / ℝ)
  compatible : ∀ u : ℝˣ,
    equiv (QuotientGroup.mk' positiveRealUnitSubgroup u) =
      realLocalReciprocity u

theorem real_local_reciprocity_quotient_equiv :
    Nonempty RealLocalReciprocityQuotientEquivalence := by
  sorry

theorem real_positive_unit_killed (u : ℝˣ)
    (hu : u ∈ positiveRealUnitSubgroup) :
    realLocalReciprocity u = 1 := by
  sorry

theorem real_negative_unit_is_complex_conjugation :
    realLocalReciprocity negativeRealUnit = realComplexConjugation := by
  sorry

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
  sorry

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
  sorry

theorem classNorm_membership_iff_principal_times_ideleNorm
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : GlobalNormInterface K L) (c : C_K K) :
    c ∈ classNormGroup N ↔
      ∃ x : I_K K, x ∈ principalTimesIdeleNormGroup N ∧ classQuotient x = c := by
  sorry

end
end LastLib.Book06GlobalClassFieldTheory.Chapter01
