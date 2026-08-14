import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section03ConstructingTheUnramifiedLift
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial
open scoped Polynomial WithZero
open LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06

noncomputable section

universe uK uΩ uModel uCompletion

/-! # Book 2, Chapter 7, §7.4: finite residue fields -/

/-- The finite-residue-field hypothesis. -/
def Chapter07FiniteResidueField (k : Type*) [Field k] : Prop :=
  Finite k

/-- The cardinality used as `q` in finite-residue-field formulas. -/
def Chapter07ResidueCardinality (k : Type*) [Field k] [Fintype k] : ℕ :=
  Fintype.card k

/-- The arithmetic Frobenius polynomial map `x ↦ x^q`, before installing the
field-specific ring-hom proof. -/
def Chapter07ArithmeticFrobeniusMap
    (q : ℕ) (k : Type*) [MonoidWithZero k] : k → k :=
  fun x => x ^ q

/-- An extension model that retains the field, residue-field, and Frobenius
data as structure fields.  Instance fields are used because the carrier types
are existential in the existence theorem below. -/
structure Chapter07FiniteResidueUnramifiedModel
    (A K k : Type*) [CommRing A] [Field K] [Field k] [Fintype k]
    [Algebra A K] [IsFractionRing A K] (res : A →+* k) where
  carrier : Type uModel
  [carrierField : Field carrier]
  [carrierAlgebra : Algebra K carrier]
  [carrierAAlgebra : Algebra A carrier]
  [carrierTower : IsScalarTower A K carrier]
  [carrierFinite : FiniteDimensional K carrier]
  residue : Type uModel
  [residueField : Field residue]
  [residueAlgebra : Algebra k residue]
  [residueFinite : FiniteDimensional k residue]
  profile : Chapter07FiniteLocalExtensionData K carrier k residue
  unramified : Chapter07UnramifiedExtension profile
  q : ℕ
  q_card : Fintype.card k = q
  degree : ℕ
  degree_eq : degree = Module.finrank K carrier
  [residueFintype : Fintype residue]
  residue_card : Fintype.card residue = (Fintype.card k) ^ degree
  residueDegree : ℕ
  residueDegree_eq : residueDegree = Module.finrank k residue
  ramificationIndex : ℕ
  ramificationIndex_eq_one : ramificationIndex = 1
  residue_separable : ∀ x : residue, IsSeparable k x
  integralModel : Subalgebra A carrier
  integralModel_finite : Module.Finite A integralModel
  residueMap : integralModel →+* residue
  residueIdeal : Ideal integralModel
  /-- The displayed integral model has the stated fraction field; this keeps
  the carrier field from being an unrelated field with the same numerical
  profile. -/
  integralModel_fractionRing : IsFractionRing integralModel carrier
  /-- The integral model is genuinely unramified over the base ring. -/
  integralModel_etale : Algebra.Etale A integralModel
  residueMap_compatible :
    residueMap.comp (algebraMap A integralModel) =
      (algebraMap k residue).comp res
  residueMap_surjective : Function.Surjective residueMap
  residueMap_kernel : RingHom.ker residueMap = residueIdeal
  residueIdeal_maximal : residueIdeal.IsMaximal
  frobenius : carrier ≃ₐ[K] carrier
  frobeniusOnModel : integralModel ≃+* integralModel
  frobeniusOnModel_compatible : ∀ x : integralModel,
    (frobeniusOnModel x : carrier) = frobenius x
  frobenius_on_residue :
    ∀ x : integralModel,
      residueMap (frobeniusOnModel x) = (residueMap x) ^ q

/-- The automorphism group used for finite unramified Galois groups. -/
abbrev Chapter07GaloisAutomorphismGroup
    (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  L ≃ₐ[K] L

/-- Existence of the unique degree-`f` unramified lift over a finite residue
field.  The polynomial hypothesis is the finite-field residue construction
used in §7.3. -/
theorem chapter07_finite_field_irreducible_separable_polynomial_exists
    {k : Type*} [Field k] [Fintype k] (f : ℕ) (hf : 0 < f) :
    ∃ gbar : k[X],
      gbar.Monic ∧ Irreducible gbar ∧ gbar.Separable ∧
        gbar.natDegree = f := by
  sorry

/-- Existence of the unique degree-`f` unramified lift over a finite residue
field.  The polynomial hypothesis is the finite-field residue construction
used in §7.3. -/
theorem chapter07_finite_residue_unramified_exists
    {A K k : Type*} [CommRing A] [IsDomain A]
    [Field K] [Field k] [Fintype k]
    [Algebra A K] [IsFractionRing A K] [HenselianLocalRing A]
    [IsDiscreteValuationRing A]
    (res : A →+* k) (f : ℕ) (hf : 0 < f)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A)
    (hpoly : ∃ gbar : k[X],
      gbar.Monic ∧ Irreducible gbar ∧ gbar.Separable ∧ gbar.natDegree = f) :
    ∃ M : Chapter07FiniteResidueUnramifiedModel A K k res,
      M.degree = f ∧ M.residueDegree = f ∧ M.ramificationIndex = 1 := by
  sorry

/-- The finite-field existence theorem with the irreducible-polynomial
hypothesis discharged by the finite-field polynomial existence result. -/
theorem chapter07_finite_residue_unramified_exists_for_degree
    {A K k : Type*} [CommRing A] [IsDomain A]
    [Field K] [Field k] [Fintype k]
    [Algebra A K] [IsFractionRing A K] [HenselianLocalRing A]
    [IsDiscreteValuationRing A]
    (res : A →+* k) (f : ℕ) (hf : 0 < f)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A) :
    ∃ M : Chapter07FiniteResidueUnramifiedModel A K k res,
      M.degree = f ∧ M.residueDegree = f ∧ M.ramificationIndex = 1 := by
  sorry

/-- Any two models produced for the same finite residue degree are isomorphic
over the base field. -/
theorem chapter07_finite_residue_unramified_unique
    {A K k : Type*} [CommRing A] [IsDomain A]
    [Field K] [Field k] [Fintype k]
    [Algebra A K] [IsFractionRing A K] [HenselianLocalRing A]
    [IsDiscreteValuationRing A]
    (res : A →+* k) (f : ℕ)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A)
    (M₁ M₂ : Chapter07FiniteResidueUnramifiedModel A K k res)
    (h₁ : M₁.degree = f) (h₂ : M₂.degree = f) :
    letI : Field M₁.carrier := M₁.carrierField
    letI : Field M₂.carrier := M₂.carrierField
    letI : Algebra K M₁.carrier := M₁.carrierAlgebra
    letI : Algebra K M₂.carrier := M₂.carrierAlgebra
    Nonempty (M₁.carrier ≃ₐ[K] M₂.carrier) := by
  sorry

/-- The finite unramified Galois group is cyclic, with generator characterized
by arithmetic Frobenius on the residue field. -/
theorem chapter07_finite_residue_galois_group_is_cyclic
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [Fintype k] [Finite l]
    [Algebra.IsAlgebraic k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter06UnramifiedGaloisReduction K L k l) :
    IsCyclic (Chapter07GaloisAutomorphismGroup K L) ∧
      ∃ σ : Chapter07GaloisAutomorphismGroup K L,
        D.reduction σ = chapter06ArithmeticFrobenius k l ∧
          orderOf σ = Module.finrank k l ∧
          (∀ τ : Chapter07GaloisAutomorphismGroup K L,
            ∃ n : ℤ, σ ^ n = τ) ∧
        Nonempty
          (Chapter07GaloisAutomorphismGroup K L ≃*
            Multiplicative (ZMod (Module.finrank k l))) := by
  sorry

/- The source-level unramified predicate for an intermediate field, with the
finite residue field and its chosen ambient residue closure fixed by the
caller. -/
structure Chapter07IntermediateUnramifiedData
    (K : Type uK) (Ω : Type uΩ) (k κ : Type uModel)
    [Field K] [Field Ω] [Field k] [Field κ] [Fintype k]
    [Algebra K Ω] [Algebra k κ]
    (E : IntermediateField K Ω) [FiniteDimensional K E] where
  residue : IntermediateField k κ
  [residueFinite : FiniteDimensional k residue]
  profile : Chapter07FiniteLocalExtensionData K E k residue
  actual :
    Chapter07ActualUnramifiedIntermediateData K Ω k κ E residue profile

def Chapter07IntermediateIsUnramified
    {K : Type uK} {Ω : Type uΩ} [Field K] [Field Ω] [Algebra K Ω]
    (k κ : Type uModel) [Field k] [Field κ] [Fintype k] [Algebra k κ]
    (E : IntermediateField K Ω) : Prop :=
  ∃ hfinite : FiniteDimensional K E,
    letI := hfinite
    Nonempty (Chapter07IntermediateUnramifiedData K Ω k κ E)

abbrev Chapter07PositiveNat := {n : ℕ // 0 < n}

/-- The standard finite-field indexing of unramified lifts in a fixed
separable closure.  The degree, nesting, and exhaustivity fields make the
chosen tower explicit instead of hiding it behind an arbitrary function. -/
structure Chapter07FiniteResidueTower
    (K : Type uK) (Ω : Type uΩ) (k κ : Type uModel)
    [Field K] [Field Ω] [Field k] [Field κ] [Fintype k]
    [Algebra K Ω] [Algebra k κ] where
  level : Chapter07PositiveNat → IntermediateField K Ω
  level_finite : ∀ f, FiniteDimensional K (level f)
  level_degree : ∀ f, Module.finrank K (level f) = f.1
  level_is_galois : ∀ f,
    letI := level_finite f
    IsGalois K (level f)
  level_unramified : ∀ f,
    letI := level_finite f
    Chapter07IntermediateIsUnramified k κ (level f)
  nested : ∀ {m n : Chapter07PositiveNat}, m.1 ∣ n.1 → level m ≤ level n
  exhaustive : ∀ E : IntermediateField K Ω,
    Chapter07IntermediateIsUnramified k κ E →
    ∃ f, E = level f
  compositum_lcm : ∀ m n, ∃ f,
    f.1 = Nat.lcm m.1 n.1 ∧ level m ⊔ level n = level f
  intersection_gcd : ∀ m n, ∃ f,
    f.1 = Nat.gcd m.1 n.1 ∧ level m ⊓ level n = level f

/-- The maximal unramified subextension inside a chosen separable closure is
the union of all finite unramified levels. -/
def chapter07MaximalUnramifiedExtension
    (K : Type uK) (Ω : Type uΩ) [Field K] [Field Ω] [Algebra K Ω]
    (k κ : Type uModel) [Field k] [Field κ] [Fintype k]
    [Algebra k κ]
    (T : Chapter07FiniteResidueTower.{uK, uΩ, uModel} K Ω k κ) :
  IntermediateField K Ω :=
  ⨆ f, T.level f

/-- A chosen completion of the maximal unramified union, retaining its
embedding rather than treating non-algebraicity as a property of an unnamed
type. -/
structure Chapter07MaximalUnramifiedCompletionData
    (K : Type uK) (Ω : Type uΩ) (k κ : Type uModel)
    [Field K] [Field Ω] [Field k] [Field κ] [Fintype k] [UniformSpace Ω]
    [Algebra K Ω] [Algebra k κ]
    (T : Chapter07FiniteResidueTower K Ω k κ) where
  completion : Type*
  [completionField : Field completion]
  [completionAlgebra : Algebra K completion]
  [completionUniformSpace : UniformSpace completion]
  [completionT2Space : T2Space completion]
  [completionComplete : CompleteSpace completion]
  embedding : ↥(chapter07MaximalUnramifiedExtension K Ω k κ T) →+* completion
  embedding_compatible :
    embedding.comp
        (algebraMap K (↥(chapter07MaximalUnramifiedExtension K Ω k κ T))) =
      algebraMap K completion
  /-- The completion contains the maximal unramified union as an actual
  embedding, rather than merely receiving an unrelated ring homomorphism. -/
  embedding_injective : Function.Injective embedding
  /-- The displayed field is generated topologically by the maximal
  unramified union, as required of its completion. -/
  embedding_dense : DenseRange embedding
  /-- The completion topology is the one induced from the ambient uniform
  topology on the maximal unramified union, rather than an unrelated topology
  on the target field. -/
  embedding_isUniformInducing : IsUniformInducing embedding
  /-- A genuine completion is a proper enlargement of the uncompleted union. -/
  embedding_not_surjective : ¬Function.Surjective embedding
  /-- Every element algebraic over the base already lies in the algebraic
  unramified union.  This is the completion property needed to deduce that a
  proper completion contains a transcendental element. -/
  algebraic_elements_in_range : ∀ x : completion, IsAlgebraic K x →
    ∃ y : ↥(chapter07MaximalUnramifiedExtension K Ω k κ T), embedding y = x

/-- The automorphism group of the actual maximal unramified union in the
chosen ambient field. -/
abbrev Chapter07MaximalUnramifiedAutomorphismGroup
    (K : Type uK) (Ω : Type uΩ) (k κ : Type uModel)
    [Field K] [Field Ω] [Field k] [Field κ] [Algebra K Ω] [Algebra k κ]
    [Fintype k]
    (T : Chapter07FiniteResidueTower K Ω k κ) :=
  (↥(chapter07MaximalUnramifiedExtension K Ω k κ T)) ≃ₐ[K]
    (↥(chapter07MaximalUnramifiedExtension K Ω k κ T))

/-- The finite-residue construction supplies an actual completion data object
for the maximal unramified union; no completion witness is supplied by the
caller. -/
theorem chapter07_finite_residue_tower_completion_exists
    {K : Type uK} {Ω : Type uΩ} {k κ : Type uModel}
    [Field K] [Field Ω] [Field k] [Field κ]
    [Fintype k] [UniformSpace Ω]
    [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (T : Chapter07FiniteResidueTower K Ω k κ)
    (vK : Valuation K ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (residueIdentification : Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vK
        ≃+* k)) :
    Nonempty (Chapter07MaximalUnramifiedCompletionData K Ω k κ T) := by
  sorry

/-- In an algebraically closed algebraic ambient field, the finite-residue
construction supplies the fixed-residue tower. -/
theorem chapter07_finite_residue_tower_exists
    {K : Type uK} {Ω : Type uΩ} {k κ : Type uModel}
    [Field K] [Field Ω] [Field k] [Field κ]
    [Fintype k] [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (vK : Valuation K ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring)
    (residueIdentification : Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vK
        ≃+* k)) :
    Nonempty (Chapter07FiniteResidueTower K Ω k κ) := by
  sorry

/-- Starting from the finite-residue hypotheses, the construction supplies a
finite-residue tower together with actual completion data for its maximal
unramified union. -/
theorem chapter07_finite_residue_completion_data_exists
    {K : Type uK} {Ω : Type uΩ} {k κ : Type uModel}
    [Field K] [Field Ω] [Field k] [Field κ]
    [Fintype k] [UniformSpace Ω]
    [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (vK : Valuation K ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring)
    (residueIdentification : Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vK
        ≃+* k)) :
    ∃ T : Chapter07FiniteResidueTower K Ω k κ,
      Nonempty (Chapter07MaximalUnramifiedCompletionData K Ω k κ T) := by
  sorry

theorem chapter07_maximal_unramified_extension_is_maximal
    {K : Type uK} {Ω : Type uΩ} [Field K] [Field Ω] [Algebra K Ω]
    (k κ : Type uModel) [Field k] [Field κ] [Fintype k]
    [Algebra k κ]
    (T : Chapter07FiniteResidueTower.{uK, uΩ, uModel} K Ω k κ) :
    ∀ E : IntermediateField K Ω,
      Chapter07IntermediateIsUnramified k κ E →
      E ≤ chapter07MaximalUnramifiedExtension K Ω k κ T := by
  intro E hE
  obtain ⟨f, hf⟩ := T.exhaustive E hE
  rw [hf]
  exact le_iSup (fun f : Chapter07PositiveNat => T.level f) f

/-- The numerical compositum and intersection laws in the finite-residue
tower. -/
theorem chapter07_finite_residue_tower_compositum_intersection
    {K : Type uK} {Ω : Type uΩ} [Field K] [Field Ω] [Algebra K Ω]
    (k κ : Type uModel) [Field k] [Field κ] [Fintype k]
    [Algebra k κ]
    (T : Chapter07FiniteResidueTower.{uK, uΩ, uModel} K Ω k κ)
    (m n : Chapter07PositiveNat) :
    (∃ f, f.1 = Nat.lcm m.1 n.1 ∧ T.level m ⊔ T.level n = T.level f) ∧
      (∃ f, f.1 = Nat.gcd m.1 n.1 ∧ T.level m ⊓ T.level n = T.level f) := by
  sorry

/-- A fixed inverse-limit model of the profinite completion of the integers.
Compatibility is expressed using Mathlib's canonical maps `ZMod n → ZMod m`
for `m ∣ n`. -/
def Chapter07ProfiniteIntegerCompletionSubgroup :
    AddSubgroup (∀ n : Chapter07PositiveNat, ZMod n.1) where
  carrier := {x |
    ∀ (m n : Chapter07PositiveNat) (h : m.1 ∣ n.1),
      ZMod.castHom h (ZMod m.1) (x n) = x m}
  zero_mem' := by
    intro m n h
    simp
  add_mem' := by
    intro x y hx hy m n h
    change ZMod.castHom h (ZMod m.1) (x n + y n) = x m + y m
    rw [map_add, hx m n h, hy m n h]
  neg_mem' := by
    intro x hx m n h
    change ZMod.castHom h (ZMod m.1) (-x n) = -x m
    rw [map_neg, hx m n h]

abbrev Chapter07ProfiniteIntegerCompletion : Type :=
  Chapter07ProfiniteIntegerCompletionSubgroup

/-- The canonical integer-to-compatible-residue map. -/
def chapter07IntegerToProfiniteCompletion
    (z : ℤ) : Chapter07ProfiniteIntegerCompletion :=
  ⟨fun n => z, by
    intro m n h
    simp⟩

/-- The inverse-limit assertion for the Galois group of the maximal
unramified extension.  The finite quotient maps are retained explicitly. -/
structure Chapter07MaximalUnramifiedGaloisData
    (G : Type*) [Group G] where
  quotient : ∀ n : Chapter07PositiveNat, G →* Multiplicative (ZMod n.1)
  quotient_surjective : ∀ n, Function.Surjective (quotient n)
  quotient_compatible :
    ∀ (m n : Chapter07PositiveNat) (h : m.1 ∣ n.1),
      ((ZMod.castHom h (ZMod m.1)).toAddMonoidHom.toMultiplicative).comp
          (quotient n) = quotient m
  quotient_separates : ∀ {g h : G},
    (∀ n : Chapter07PositiveNat, quotient n g = quotient n h) → g = h
  quotient_realizes : ∀ x : Chapter07ProfiniteIntegerCompletion, ∃ g : G,
    ∀ n : Chapter07PositiveNat, quotient n g = Multiplicative.ofAdd (x.1 n)
  arithmeticFrobenius : G
  arithmeticFrobenius_image :
    ∀ n : Chapter07PositiveNat,
      quotient n arithmeticFrobenius = Multiplicative.ofAdd (1 : ZMod n.1)

/-- The two actual maximal-unramified outputs attached to one finite-residue
tower.  Keeping them in one structure prevents the completion and inverse
limit statements from silently referring to different towers. -/
structure Chapter07FiniteResidueMaximalUnramifiedData
    (K : Type uK) (Ω : Type uΩ) (k κ : Type uModel)
    [Field K] [Field Ω] [Field k] [Field κ] [Fintype k] [UniformSpace Ω]
    [Algebra K Ω] [Algebra k κ]
    (T : Chapter07FiniteResidueTower K Ω k κ) where
  completion :
    Chapter07MaximalUnramifiedCompletionData.{uK, uΩ, uModel, uCompletion}
      K Ω k κ T
  galois :
    Chapter07MaximalUnramifiedGaloisData
      (Chapter07MaximalUnramifiedAutomorphismGroup K Ω k κ T)

/-- The finite-residue construction supplies inverse-limit quotient data for
the actual automorphism group of the maximal unramified union. -/
theorem chapter07_finite_residue_tower_galois_data_exists
    {K : Type uK} {Ω : Type uΩ} {k κ : Type uModel}
    [Field K] [Field Ω] [Field k] [Field κ]
    [Fintype k] [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (T : Chapter07FiniteResidueTower K Ω k κ) :
    Nonempty
      (Chapter07MaximalUnramifiedGaloisData
        (Chapter07MaximalUnramifiedAutomorphismGroup K Ω k κ T)) := by
  sorry

/-- Starting from the finite-residue hypotheses, the construction supplies a
finite-residue tower whose actual maximal-unramified automorphism group carries
the compatible finite quotient data of the profinite inverse limit. -/
theorem chapter07_finite_residue_galois_data_exists
    {K : Type uK} {Ω : Type uΩ} {k κ : Type uModel}
    [Field K] [Field Ω] [Field k] [Field κ]
    [Fintype k] [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (vK : Valuation K ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring)
    (residueIdentification : Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vK
        ≃+* k)) :
    ∃ T : Chapter07FiniteResidueTower K Ω k κ,
      Nonempty
        (Chapter07MaximalUnramifiedGaloisData
          (Chapter07MaximalUnramifiedAutomorphismGroup K Ω k κ T)) := by
  sorry

/-- For a fixed finite-residue tower, the completion and the inverse-limit
Galois data are supplied for that same actual maximal unramified union. -/
theorem chapter07_finite_residue_tower_maximal_unramified_data_exists
    {K : Type uK} {Ω : Type uΩ} {k κ : Type uModel}
    [Field K] [Field Ω] [Field k] [Field κ]
    [Fintype k] [UniformSpace Ω]
    [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (T : Chapter07FiniteResidueTower K Ω k κ)
    (vK : Valuation K ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (residueIdentification : Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vK
        ≃+* k)) :
    Nonempty (Chapter07FiniteResidueMaximalUnramifiedData K Ω k κ T) := by
  sorry

/-- The finite-residue hypotheses produce one tower carrying both actual
completion data and actual maximal-unramified inverse-limit Galois data. -/
theorem chapter07_finite_residue_maximal_unramified_data_exists
    {K : Type uK} {Ω : Type uΩ} {k κ : Type uModel}
    [Field K] [Field Ω] [Field k] [Field κ]
    [Fintype k] [UniformSpace Ω]
    [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (vK : Valuation K ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (residueIdentification : Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ResidueField vK
        ≃+* k)) :
    ∃ T : Chapter07FiniteResidueTower K Ω k κ,
      Nonempty (Chapter07FiniteResidueMaximalUnramifiedData K Ω k κ T) := by
  sorry

theorem chapter07_maximal_unramified_galois_group_is_profinite_integer_completion
    (G : Type*) [Group G]
    (hG : Chapter07MaximalUnramifiedGaloisData G) :
    ∃ e : G ≃* Multiplicative Chapter07ProfiniteIntegerCompletion,
      e hG.arithmeticFrobenius =
        Multiplicative.ofAdd (chapter07IntegerToProfiniteCompletion 1) := by
  sorry

/-- The precise formal content of the warning about the completed infinite
union: non-algebraicity is a property of the chosen completion model, not an
automatic consequence of merely naming a completion. -/
def Chapter07CompletionIsNonAlgebraic
    (K Kcompletion : Type*) [Field K] [Field Kcompletion] [Algebra K Kcompletion]
  : Prop :=
  ∃ x : Kcompletion, ¬IsAlgebraic K x

/-- The chosen completion in the construction data is genuinely non-algebraic
over the base field. -/
theorem chapter07_maximal_unramified_completion_is_non_algebraic
    {K : Type uK} {Ω : Type uΩ} {k κ : Type uModel}
    [Field K] [Field Ω] [Field k] [Field κ] [Fintype k] [UniformSpace Ω]
    [Algebra K Ω] [Algebra k κ]
    (T : Chapter07FiniteResidueTower K Ω k κ)
    (C : Chapter07MaximalUnramifiedCompletionData K Ω k κ T) :
    (@Chapter07CompletionIsNonAlgebraic K C.completion _
      C.completionField C.completionAlgebra) := by
  have hnot : ∃ x : C.completion,
      ∀ y : ↥(chapter07MaximalUnramifiedExtension K Ω k κ T), C.embedding y ≠ x := by
    by_contra h
    apply C.embedding_not_surjective
    intro x
    by_contra hx
    apply h
    exact ⟨x, fun y hy => hx ⟨y, hy⟩⟩
  obtain ⟨x, hx⟩ := hnot
  refine ⟨x, ?_⟩
  intro hxalg
  obtain ⟨y, hy⟩ := C.algebraic_elements_in_range x hxalg
  exact hx y hy

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
