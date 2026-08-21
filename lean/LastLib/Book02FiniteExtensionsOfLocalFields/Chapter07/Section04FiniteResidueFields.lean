import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.PrimitiveElement
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
  [carrierGalois : IsGalois K carrier]
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
  profile_residueDegree : profile.residueDegree = residueDegree
  ramificationIndex : ℕ
  ramificationIndex_eq_one : ramificationIndex = 1
  profile_ramificationIndex : profile.ramificationIndex = ramificationIndex
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
  frobenius_order : orderOf frobenius = degree
  frobenius_generates : ∀ σ : carrier ≃ₐ[K] carrier, ∃ n : ℤ, frobenius ^ n = σ
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
  let _ : PerfectField k := PerfectField.ofFinite
  let ⟨p, hp⟩ := CharP.exists k
  let _ : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let _ : NeZero f := ⟨Nat.ne_of_gt hf⟩
  obtain ⟨α, hα⟩ :=
    Field.exists_primitive_element_of_finite_bot k (FiniteField.Extension k p f)
  let gbar : k[X] := minpoly k α
  have hαint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hirr : Irreducible gbar := minpoly.irreducible hαint
  refine ⟨gbar, minpoly.monic hαint, hirr,
    PerfectField.separable_of_irreducible hirr, ?_⟩
  simpa [gbar, FiniteField.finrank_extension] using
    (Field.primitive_element_iff_minpoly_natDegree_eq k α).mp hα

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
  obtain ⟨gbar, hgbar_monic, hgbar_irreducible, hgbar_separable,
    hgbar_degree⟩ := chapter07_finite_field_irreducible_separable_polynomial_exists
      (k := k) f hf
  exact chapter07_finite_residue_unramified_exists res f hf
    hres_surjective hres_kernel
    ⟨gbar, hgbar_monic, hgbar_irreducible, hgbar_separable, hgbar_degree⟩

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
  let σ : Chapter07GaloisAutomorphismGroup K L :=
    chapter06UnramifiedArithmeticFrobenius D
  have hσ : D.reduction σ = chapter06ArithmeticFrobenius k l := by
    simp [σ, chapter06UnramifiedArithmeticFrobenius]
  have horder : orderOf σ = Module.finrank k l := by
    calc
      orderOf σ = orderOf (D.reduction σ) := (D.reduction.orderOf_eq σ).symm
      _ = orderOf (chapter06ArithmeticFrobenius k l) := by rw [hσ]
      _ = Module.finrank k l :=
        chapter06_arithmetic_frobenius_order k l (Module.finrank k l) rfl
  let _ : IsCyclic (Chapter07GaloisAutomorphismGroup K L) :=
    (D.reduction.isCyclic).mpr inferInstance
  refine ⟨inferInstance, σ, hσ, horder, ?_, ?_⟩
  · intro τ
    exact chapter06_unramified_arithmetic_frobenius_generates D τ
  · have hcard :
        Nat.card (Chapter07GaloisAutomorphismGroup K L) =
          Nat.card (Multiplicative (ZMod (Module.finrank k l))) := by
      calc
        Nat.card (Chapter07GaloisAutomorphismGroup K L) =
            Nat.card (Gal(l / k)) := Nat.card_congr D.reduction
        _ = Module.finrank k l := IsGalois.card_aut_eq_finrank k l
        _ = Nat.card (Multiplicative (ZMod (Module.finrank k l))) := by
          let _ : NeZero (Module.finrank k l) := NeZero.of_pos Module.finrank_pos
          simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    exact ⟨mulEquivOfCyclicCardEq hcard⟩

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

/-- In an algebraically closed algebraic ambient field, the finite-residue
construction supplies the fixed-residue tower. -/
/-
Proof roadmap for `chapter07_finite_residue_tower_exists`.

The interface is intentional: the levels must be *the actual subfields of
`Ω`*, not merely abstract models isomorphic to unramified extensions.  The
fixed-closure classification built in §7.3 is the bridge which supplies those
subfields coherently.

1. Choose
   `C : Chapter07CanonicalUnramifiedClassification K Ω k κ` from
   `chapter07_canonical_unramified_classification_exists vK hcomplete
   residueIdentification` (Section03ConstructingTheUnramifiedLift.lean,
   lines 437ff).  Its `reduction` is an equivalence between the witnessed
   unramified intermediate fields in `Ω` and the finite separable
   intermediate fields in `κ`; its fields `degree_preserved`,
   `inclusion_preserved`, `compositum_preserved`, and
   `intersection_preserved` are precisely the coherence data needed below.

2. First construct, on the residue side, the canonical degree-`f` field
   `residueLevel (f : Chapter07PositiveNat) : IntermediateField k κ`.  A
   convenient definition is

       Algebra.adjoin k
         ((X ^ (Fintype.card k) ^ f.1 - X : k[X]).rootSet κ).

   Package it as
   `canonicalResidueLevel f :
     Chapter07CanonicalFiniteSeparableResidueIntermediate k κ`.
   For finiteness and its degree, put `p := (CharP.exists k).choose`, install
   `Fact p.Prime`, `CharP k p`, and `NeZero f.1`, and use:

   * `IsAlgClosed.splits` and
     `IntermediateField.adjoin_rootSet_isSplittingField` from
     Mathlib/FieldTheory/SplittingField/IsSplittingField.lean;
   * the `IsSplittingField k (FiniteField.Extension k p f.1)
       (X ^ Nat.card k ^ f.1 - X)` instance and
     `FiniteField.finrank_extension` from
     Mathlib/FieldTheory/Finite/Extension.lean;
   * `Polynomial.IsSplittingField.algEquiv` to identify the two splitting
     fields (normalize `Nat.card k` with `Fintype.card_eq_nat_card`).

   Transporting finrank across that equivalence gives
   `residueLevel_finite f : FiniteDimensional k (residueLevel f)` and
   `residueLevel_degree f : Module.finrank k (residueLevel f) = f.1`.
   The separability field of
   `Chapter07FiniteSeparableResidueIntermediateWitness` follows after
   installing `PerfectField.ofFinite` on `k`, using
   `PerfectField.separable_of_irreducible (minpoly.irreducible
   (Algebra.IsIntegral.isIntegral x))` for each `x`.

3. Prove the residue-field classification lemma

       residue_eq_level (S :
         Chapter07CanonicalFiniteSeparableResidueIntermediate k κ) :
         S.1 = residueLevel
           ⟨Module.finrank k S.1, Module.finrank_pos⟩.

   Install `C.residue_finite S`.  Every `x : S.1` satisfies
   `x ^ (Fintype.card k ^ Module.finrank k S.1) = x`: obtain a `Fintype`
   from finiteness, rewrite its cardinal with
   `Module.card_eq_pow_finrank` (Mathlib/FieldTheory/Finiteness.lean), and
   use `FiniteField.pow_card` (Mathlib/FieldTheory/Finite/Basic.lean), then
   apply the inclusion `S.1.val`.  This puts every element of `S.1` in the
   displayed root set and hence in the adjoin via `Algebra.subset_adjoin`.
   Close equality with
   `IntermediateField.eq_of_le_of_finrank_eq` from
   Mathlib/FieldTheory/IntermediateField/Algebraic.lean and the two degree
   equalities.  This is also the uniqueness statement which later proves
   exhaustiveness.

4. Establish the residue lattice laws before transporting them through `C`:

       residueLevel_mono : m.1 ∣ n.1 → residueLevel m ≤ residueLevel n
       residueLevel_sup  : residueLevel m ⊔ residueLevel n =
         residueLevel ⟨Nat.lcm m.1 n.1, Nat.lcm_pos m.2 n.2⟩
       residueLevel_inf  : residueLevel m ⊓ residueLevel n =
         residueLevel ⟨Nat.gcd m.1 n.1, Nat.gcd_pos_of_pos_left _ m.2⟩.

   For `residueLevel_mono`, use `Algebra.adjoin_mono`; if `n = m*d`, a root
   of `X^(q^m)-X` is a root of `X^(q^n)-X` after `pow_mul`/`pow_pow`.
   For the two equalities, work inside the common finite Galois field
   `residueLevel ⟨Nat.lcm m.1 n.1, ...⟩`.  Its arithmetic Frobenius is
   `FiniteField.frobeniusAlgEquivOfAlgebraic k _`; its underlying function
   and iterates are described by
   `FiniteField.coe_frobeniusAlgEquivOfAlgebraic` and
   `FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate` in
   Mathlib/FieldTheory/Finite/Basic.lean.  Identify `residueLevel m` and
   `residueLevel n` with the fixed fields of the cyclic subgroups generated
   by the `m`-th and `n`-th powers of Frobenius, using
   `IntermediateField.mem_fixedField_iff` and
   `IntermediateField.eq_of_le_of_finrank_eq`.  Extensionality plus Bezout
   for `Nat.gcd` shows that the subgroup join is generated by the gcd power;
   extensionality on `Subgroup.zpowers` shows that their intersection is
   generated by the lcm power.  The order-reversing fixed-field
   correspondence (`IntermediateField.fixedField_le` and
   `IsGalois.intermediateFieldEquivSubgroup`,
   Mathlib/FieldTheory/Galois/Basic.lean) then gives `residueLevel_inf` and
   `residueLevel_sup`.  This route avoids trying to prove the compositum law
   merely from degree divisibility, which supplies only one inclusion.

5. Define the actual `Ω`-level by pulling back the canonical residue level:

       U f := C.reduction.symm (canonicalResidueLevel f)
       level f := (U f).1.

   Take `level_finite f := C.extension_finite (U f)`.  Rewrite
   `C.reduction (U f)` with `Equiv.apply_symm_apply`, then combine
   `C.degree_preserved (U f)` with `residueLevel_degree f` for
   `level_degree`.  `C.galois_preserved (U f)` and the finite-field Galois
   instance give `level_is_galois`.  For `level_unramified`, unfold
   `Chapter07IntermediateIsUnramified`, take `C.extension_finite (U f)`, and
   unpack `(U f).2`; its chosen
   `Chapter07FiniteUnramifiedIntermediateWitness` directly supplies the
   required `Chapter07IntermediateUnramifiedData`.

6. Transport `residueLevel_mono` through `C.inclusion_preserved` to obtain
   `nested`.  For `exhaustive E hE`, unpack `hE` into its finite-dimensional
   instance and `Chapter07IntermediateUnramifiedData`, package these fields
   as a `Chapter07FiniteUnramifiedIntermediateWitness`, hence as
   `UE : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ`, and put
   `f := ⟨Module.finrank K E, Module.finrank_pos⟩`.  Degree preservation
   and `residue_eq_level (C.reduction UE)` identify its residue field with
   `canonicalResidueLevel f`; injectivity of `C.reduction` then gives
   `UE = U f`, and `congrArg Subtype.val` is the requested `E = level f`.

7. Finally use `C.compositum_preserved (U m) (U n)` and
   `C.intersection_preserved (U m) (U n)`.  Their residue equalities, the two
   residue lattice laws, and injectivity of `C.reduction` identify the
   returned witnessed field with `U` at the lcm/gcd index.  Substitute the
   returned carrier equality to obtain exactly `compositum_lcm` and
   `intersection_gcd`, then assemble all fields of
   `Chapter07FiniteResidueTower`.

Do not start from `chapter07_finite_residue_unramified_exists_for_degree`:
that theorem chooses an abstract carrier and
`chapter07_finite_residue_unramified_unique` supplies only an abstract
`AlgEquiv`.  Neither chooses embeddings into `Ω`, and independent uses of
choice therefore cannot prove `nested`, compositum, or intersection
equalities.  The canonical classification equivalence is essential.
-/
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
  exact ⟨T.compositum_lcm m n, T.intersection_gcd m n⟩

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
  obtain ⟨T⟩ := chapter07_finite_residue_tower_exists
    (K := K) (Ω := Ω) (k := k) (κ := κ) vK hcomplete
    residueIdentification
  exact ⟨T, chapter07_finite_residue_tower_galois_data_exists T⟩

/-- For a fixed finite-residue tower, an explicit completion witness is paired
with the inverse-limit Galois data supplied by the tower construction. -/
theorem chapter07_finite_residue_tower_maximal_unramified_data_exists
    {K : Type uK} {Ω : Type uΩ} {k κ : Type uModel}
    [Field K] [Field Ω] [Field k] [Field κ]
    [Fintype k] [UniformSpace Ω]
    [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (T : Chapter07FiniteResidueTower K Ω k κ)
    (C : Chapter07MaximalUnramifiedCompletionData.{uK, uΩ, uModel, uCompletion}
      K Ω k κ T) :
    Nonempty
      (Chapter07FiniteResidueMaximalUnramifiedData.{uK, uΩ, uModel, uCompletion}
        K Ω k κ T) := by
  obtain ⟨G⟩ := chapter07_finite_residue_tower_galois_data_exists T
  exact ⟨⟨C, G⟩⟩

/-- Attach explicitly supplied completion data to a fixed finite-residue tower;
the inverse-limit Galois data are supplied by the tower construction. -/
theorem chapter07_finite_residue_maximal_unramified_data_exists
    {K : Type uK} {Ω : Type uΩ} {k κ : Type uModel}
    [Field K] [Field Ω] [Field k] [Field κ]
    [Fintype k] [UniformSpace Ω]
    [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (T : Chapter07FiniteResidueTower K Ω k κ)
    (C : Chapter07MaximalUnramifiedCompletionData.{uK, uΩ, uModel, uCompletion}
      K Ω k κ T) :
    ∃ T' : Chapter07FiniteResidueTower K Ω k κ,
      Nonempty
        (Chapter07FiniteResidueMaximalUnramifiedData.{uK, uΩ, uModel, uCompletion}
          K Ω k κ T') := by
  exact ⟨T, chapter07_finite_residue_tower_maximal_unramified_data_exists T C⟩

theorem chapter07_maximal_unramified_galois_group_is_profinite_integer_completion
    (G : Type*) [Group G]
    (hG : Chapter07MaximalUnramifiedGaloisData G) :
    ∃ e : G ≃* Multiplicative Chapter07ProfiniteIntegerCompletion,
      e hG.arithmeticFrobenius =
        Multiplicative.ofAdd (chapter07IntegerToProfiniteCompletion 1) := by
  have hcompat (g : G) (m n : Chapter07PositiveNat) (h : m.1 ∣ n.1) :
      ZMod.castHom h (ZMod m.1) ((hG.quotient n g).toAdd) =
        (hG.quotient m g).toAdd := by
    have hq := congrArg (fun φ => φ g) (hG.quotient_compatible m n h)
    exact congrArg Multiplicative.toAdd hq
  let q : G →* Multiplicative Chapter07ProfiniteIntegerCompletion :=
    { toFun := fun g =>
        Multiplicative.ofAdd
          ⟨fun n => (hG.quotient n g).toAdd, fun m n h => hcompat g m n h⟩
      map_one' := by
        apply congrArg Multiplicative.ofAdd
        apply Subtype.ext
        funext n
        simp
      map_mul' := by
        intro g h
        apply congrArg Multiplicative.ofAdd
        apply Subtype.ext
        funext n
        simp }
  have hq_injective : Function.Injective q := by
    intro g h hgh
    apply hG.quotient_separates
    intro n
    apply Multiplicative.ofAdd.injective
    have hcoord := congrArg
      (fun x : Chapter07ProfiniteIntegerCompletion => x.1 n)
      (congrArg Multiplicative.toAdd hgh)
    simpa [q] using hcoord
  have hq_surjective : Function.Surjective q := by
    intro x
    obtain ⟨g, hg⟩ := hG.quotient_realizes (Multiplicative.toAdd x)
    refine ⟨g, ?_⟩
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    funext n
    have hcoord := congrArg Multiplicative.toAdd (hg n)
    have hx : (Multiplicative.toAdd x).1 n = x.1 n := rfl
    rw [hx] at hcoord
    simpa [q] using hcoord
  let e : G ≃* Multiplicative Chapter07ProfiniteIntegerCompletion :=
    MulEquiv.ofBijective q ⟨hq_injective, hq_surjective⟩
  refine ⟨e, ?_⟩
  change q hG.arithmeticFrobenius =
    Multiplicative.ofAdd (chapter07IntegerToProfiniteCompletion 1)
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  funext n
  have hF := hG.arithmeticFrobenius_image n
  have hcoord := congrArg Multiplicative.toAdd hF
  simpa [q, chapter07IntegerToProfiniteCompletion] using hcoord

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
