import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.PrimitiveElement
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section03ConstructingTheUnramifiedLift
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial
open scoped Polynomial WithZero
open LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

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

/-- A finite-residue unramified model together with the normalized valuation,
Henselian integral presentation, and canonical residue identifications needed
to transport elements coherently between the residue and fraction fields. -/
structure Chapter07NormalizedFiniteResidueUnramifiedModel
    (A K k : Type*) [CommRing A] [Field K] [Field k] [Fintype k]
    [Algebra A K] [IsFractionRing A K] (res : A →+* k)
    (valuationBase : AddValuation K (WithTop ℤ))
    extends Chapter07FiniteResidueUnramifiedModel A K k res where
  [integralModelHenselian : HenselianLocalRing integralModel]
  residueIdeal_eq_maximal : residueIdeal = IsLocalRing.maximalIdeal integralModel
  integralResidueIdentification :
    IsLocalRing.ResidueField integralModel ≃+* residue
  integralResidueIdentification_compatible :
    integralResidueIdentification.toRingHom.comp
        (IsLocalRing.residue integralModel) = residueMap
  residue_generator_lifts : ∀ b : integralModel,
    Algebra.adjoin k ({residueMap b} : Set residue) = ⊤ →
      Algebra.adjoin A ({b} : Set integralModel) = ⊤
  field_generator_of_integral_generator : ∀ b : integralModel,
    Algebra.adjoin A ({b} : Set integralModel) = ⊤ →
      Algebra.adjoin K ({(b : carrier)} : Set carrier) = ⊤
  valuationBase_integers : valuationBase.Integers A
  valuation : AddValuation carrier (WithTop ℤ)
  valuation_extension : valuationBase.IsEquiv
    (valuation.comap (algebraMap K carrier))
  extensionData :
    Chapter10HeterogeneousExtensionData valuationBase valuation valuation_extension
  chapter10Profile : Chapter10FiniteExtensionProfile
  chapter10Profile_realized :
    Chapter10ProfileRealizedByData extensionData chapter10Profile
  chapter10Profile_degree : chapter10Profile.degree = degree
  chapter10Profile_ramificationIndex : chapter10Profile.ramificationIndex = 1
  chapter10Profile_residueDegree : chapter10Profile.residueDegree = residueDegree
  chapter10Profile_unramified : Chapter10Unramified chapter10Profile
  baseResidueIdentification : Chapter10ResidueField valuationBase ≃+* k
  extensionResidueIdentification : Chapter10ResidueField valuation ≃+* residue
  canonicalResidueMap :
    Chapter10ResidueField valuationBase →+* Chapter10ResidueField valuation
  canonicalResidueMap_eq :
    letI : Valuation.HasExtension valuationBase valuation := ⟨valuation_extension⟩
    canonicalResidueMap = Chapter10ResidueFieldMap valuationBase valuation
  canonicalResidueMap_compatible :
    extensionResidueIdentification.toRingHom.comp canonicalResidueMap =
      (algebraMap k residue).comp baseResidueIdentification.toRingHom

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
  /-
  Proof roadmap (and the precise missing interface bridge).

  1. Destructure `hpoly` as `⟨gbar, hmonic, hirr, hsep, hdeg⟩`.  Lift its
     finitely many coefficients through `hres_surjective` to a polynomial
     `g : A[X]`, arranged so that

         hg : Chapter07MonicPolynomialLift res gbar g.

     Preserve the leading coefficient as `1`; then `hg.1` and `hg.2` are the
     two facts needed below.  `chapter07_monic_lift_irreducible` and
     `chapter07_lifted_polynomial_quotient_degree` in
     Section03ConstructingTheUnramifiedLift.lean give irreducibility and
     finrank `f` for

         L := Chapter07LiftedPolynomialQuotient K
           (chapter07LiftedPolynomial g).

     Install the `Field L` instance from the irreducibility `Fact`, and use
     `chapter07LiftedRoot g` as the primitive element.

  2. The integral carrier must be the integral closure of `A` in `L` (or a
     proved-equal presentation by `Algebra.adjoin A {chapter07LiftedRoot g}`),
     not the field `L`.  Build its quotient residue map to
     `AdjoinRoot gbar`, prove surjectivity and the kernel equality, and then
     invoke `chapter07_construct_unramified_lift_with_residue_maps` (same
     file, line 452ff).  That theorem supplies the `profile`, `unramified`,
     `integralModel_etale`, and the two profile equalities.  Its hypotheses
     require explicit proofs that this integral carrier is a DVR, is the
     integral closure, and has fraction field `L`; do not replace it by the
     merely finite generated subalgebra supplied by
     `chapter07_constructed_integral_model_is_finite`.

  3. Put the finite residue field structure on `AdjoinRoot gbar`.  Its
     finrank is `f` by `chapter07_lifted_polynomial_quotient_degree` applied
     over `k`; obtain its cardinal formula from
     `Module.card_eq_pow_finrank` in
     Mathlib/FieldTheory/Finiteness.lean, rewriting `hdeg`.  Separability is
     `hsep` transported through the power-basis presentation.

  4. To fill the Frobenius fields, construct the reduction equivalence
     `Chapter06UnramifiedGaloisReduction K L k (AdjoinRoot gbar)` from the
     *same* integral model and residue map.  Then use
     `chapter06UnramifiedArithmeticFrobenius`,
     `chapter06_arithmetic_frobenius_order`, and
     `chapter06_unramified_arithmetic_frobenius_generates` from
     Chapter06/Section02FrobeniusInAnUnramifiedExtension.lean.  Its
     `integralAction` and `integralAction_spec` provide `frobeniusOnModel`
     and compatibility, while
     `chapter06_unramified_arithmetic_frobenius_residue_formula` provides
     the displayed `q`-power formula (set `q := Fintype.card k`).

  5. Assemble `M` with `carrier := L`, the integral closure as
     `integralModel`, and the data above; finish the three requested
     equalities with `hdeg` and the profile equalities.

  Current obstruction: Section03 exposes the field quotient and verifies an
  already supplied integral/residue presentation, but has no declaration
  constructing that presentation from `(res, gbar, g)`.  Likewise Chapter06
  consumes a `Chapter06UnramifiedGaloisReduction` but does not construct one
  from `Chapter07UnramifiedLocalExtensionData`.  Those two bridges must be
  proved here (or, chronologically preferably, added to Section03) before the
  assembly above is implementable.  `HenselianLocalRing.TFAE` only lifts a
  simple root; it does not by itself provide either package.
  -/
  sorry

/-- The finite-residue unramified lift with a prescribed normalized base
valuation, a Henselian integral model, and compatible canonical residue maps. -/
theorem chapter07_normalized_finite_residue_unramified_exists
    {A K k : Type*} [CommRing A] [IsDomain A]
    [Field K] [Field k] [Fintype k]
    [Algebra A K] [IsFractionRing A K] [HenselianLocalRing A]
    [IsDiscreteValuationRing A]
    (res : A →+* k) (valuationBase : AddValuation K (WithTop ℤ))
    (f : ℕ) (hf : 0 < f)
    (hvaluationBase : valuationBase.Integers A)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A)
    (hpoly : ∃ gbar : k[X],
      gbar.Monic ∧ Irreducible gbar ∧ gbar.Separable ∧ gbar.natDegree = f) :
    ∃ M : Chapter07NormalizedFiniteResidueUnramifiedModel
        A K k res valuationBase,
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

/-- The normalized finite-residue lift with the polynomial-existence input
discharged over the finite residue field. -/
theorem chapter07_normalized_finite_residue_unramified_exists_for_degree
    {A K k : Type*} [CommRing A] [IsDomain A]
    [Field K] [Field k] [Fintype k]
    [Algebra A K] [IsFractionRing A K] [HenselianLocalRing A]
    [IsDiscreteValuationRing A]
    (res : A →+* k) (valuationBase : AddValuation K (WithTop ℤ))
    (f : ℕ) (hf : 0 < f)
    (hvaluationBase : valuationBase.Integers A)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A) :
    ∃ M : Chapter07NormalizedFiniteResidueUnramifiedModel
        A K k res valuationBase,
      M.degree = f ∧ M.residueDegree = f ∧ M.ramificationIndex = 1 := by
  obtain ⟨gbar, hgbar_monic, hgbar_irreducible, hgbar_separable,
    hgbar_degree⟩ := chapter07_finite_field_irreducible_separable_polynomial_exists
      (k := k) f hf
  exact chapter07_normalized_finite_residue_unramified_exists
    res valuationBase f hf hvaluationBase hres_surjective hres_kernel
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
  /-
  Proof roadmap (degree equality is not by itself an API bridge).

  The conclusion is mathematically the usual uniqueness of the unramified
  extension of degree `f`, but `h₁` and `h₂` alone cannot be passed to any
  current declaration.  In particular,
  `chapter07_different_monic_lifts_are_isomorphic` in
  Section03ConstructingTheUnramifiedLift.lean requires a common residue
  polynomial and an explicit root of the first lift in the second carrier;
  neither datum is retained by `Chapter07FiniteResidueUnramifiedModel`.

  The intended classification proof is as follows.

  1. Embed both finite algebraic carriers in one algebraic closure `Ω` of
     `K`, and both residues in one algebraic closure `κ` of `k`.  Package the
     images as

         E₁ E₂ : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ

     with actual residue images `S₁ S₂`.  The package must retain algebra
     equivalences `eᵢ : Mᵢ.carrier ≃ₐ[K] Eᵢ.1`; numerical `profile` fields do
     not suffice to construct the required
     `Chapter07ActualUnramifiedIntermediateData`.

  2. Use one
     `C : Chapter07CanonicalUnramifiedClassification K Ω k κ` and arrange
     `C.reduction Eᵢ` to be the packaged `Sᵢ`, via
     `C.reduction_realized`.  Install `C.extension_finite Eᵢ` and
     `C.residue_finite (C.reduction Eᵢ)`.  From `Mᵢ.degree_eq`, `hᵢ`, and
     `C.degree_preserved Eᵢ`, derive

         Module.finrank k (C.reduction E₁).1 =
           Module.finrank k (C.reduction E₂).1.

  3. Prove the two residue intermediate fields equal.  Concretely, every
     element of either degree-`f` field is a root of
     `X ^ (Fintype.card k ^ f) - X`: use
     `Module.card_eq_pow_finrank` (Mathlib/FieldTheory/Finiteness.lean) and
     `FiniteField.pow_card` (Mathlib/FieldTheory/Finite/Basic.lean).
     Inclusion in the common root field follows from
     `Algebra.subset_adjoin`; close each inclusion/equality with
     `IntermediateField.eq_of_le_of_finrank_eq`.  This is the
     `residue_eq_level` lemma described in the roadmap for
     `chapter07_finite_residue_tower_exists` later in this file.

  4. Since `C.reduction` is injective, equality of its two residue values
     gives `hE : E₁ = E₂`.  Form the intermediate-field equivalence with
     `IntermediateField.equivOfEq (congrArg Subtype.val hE)` (or substitute
     by `hE`), and assemble

         e₁.trans ((IntermediateField.equivOfEq ...).trans e₂.symm).

     Wrap this equivalence in `Nonempty`.

  Current obstruction/interface correction required: the model stores no
  common ambient embeddings, no `Chapter07FiniteUnramifiedIntermediateWitness`,
  and no common `Chapter07CanonicalUnramifiedClassification`.  Moreover
  `chapter07_canonical_unramified_classification_exists` requires a rank-one
  valuation, adic completeness, and a residue identification, whereas this
  theorem assumes only a henselian DVR presentation.  Thus equal degree
  does support uniqueness only after a genuine henselian finite-etale
  classification theorem (or equivalent common-classification presentation)
  is connected to the model.  A normal proof must first add that bridge; it
  must not treat finrank equality as if it produced an arbitrary field
  `AlgEquiv`.
  -/
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
  /-- The arithmetic Frobenius at each finite level.  Choosing these as part
  of the tower is essential: unrelated cyclic generators do not determine an
  automorphism of the directed union. -/
  level_frobenius : ∀ f, level f ≃ₐ[K] level f
  /-- Arithmetic Frobenius commutes with every divisibility inclusion. -/
  level_frobenius_compatible : ∀ (m n : Chapter07PositiveNat)
    (h : m.1 ∣ n.1) (x : level m),
      (level_frobenius n ⟨x.1, nested h x.2⟩ : level n).1 =
        (level_frobenius m x).1
  /-- Normalized cyclic coordinates on each finite Galois group. -/
  level_galois_equiv : ∀ f,
    (level f ≃ₐ[K] level f) ≃* Multiplicative (ZMod f.1)
  level_frobenius_image : ∀ f,
    level_galois_equiv f (level_frobenius f) =
      Multiplicative.ofAdd (1 : ZMod f.1)
  /-- Every automorphism of the actual directed union preserves each
  canonical degree level, so restriction really lands in its finite Galois
  group. -/
  level_characteristic : ∀ (f : Chapter07PositiveNat)
    (σ : (↥(⨆ n, level n)) ≃ₐ[K] (↥(⨆ n, level n))) (x : level f),
      (σ ⟨x.1, (le_iSup (fun n => level n) f) x.2⟩).1 ∈ level f

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

7. Use `C.compositum_preserved (U m) (U n)` and
   `C.intersection_preserved (U m) (U n)`.  Their residue equalities, the two
   residue lattice laws, and injectivity of `C.reduction` identify the
   returned witnessed field with `U` at the lcm/gcd index.  Substitute the
   returned carrier equality to obtain exactly `compositum_lcm` and
   `intersection_gcd`.

8. Supply the Galois fields added to the tower interface.  On
   `canonicalResidueLevel f`, take the explicit `q`-power automorphism
   `FiniteField.frobeniusAlgEquivOfAlgebraic k _`.  Its compatibility under
   inclusions is pointwise from
   `FiniteField.coe_frobeniusAlgEquivOfAlgebraic`; its order and generation
   are `chapter06_arithmetic_frobenius_order` and
   `chapter06_arithmetic_frobenius_generates` from
   Chapter06/Section02FrobeniusInAnUnramifiedExtension.lean.  Lift it to
   `level f` using the actual residue realization in
   `C.reduction_realized (U f)` and the reduction identification represented
   by `Chapter06UnramifiedGaloisReduction.reduction`.  Use
   `chapter06_unramified_arithmetic_frobenius_unique` to prove the lifts at
   divisible levels restrict to one another; this uniqueness step is why an
   arbitrary result of `C.galois_group_preserved` is not sufficient by
   itself.  Normalize the finite cyclic equivalence by sending this lift to
   `1`; the order calculation and `IsGalois.card_aut_eq_finrank` show it is a
   `MulEquiv` with `Multiplicative (ZMod f.1)`.  For
   `level_characteristic`, restrict an automorphism of the union to the image
   of `level f`; transport the finite unramified witness across that image,
   apply `exhaustive`, and compare finranks using `level_degree` to identify
   the image with `level f`.  Now assemble every field of
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
/-
Proof roadmap for `chapter07_finite_residue_tower_galois_data_exists`.

The original tower interface stopped at `level_is_galois`; that is not enough
to choose compatible cyclic generators.  The fields `level_frobenius`,
`level_frobenius_compatible`, `level_galois_equiv`,
`level_frobenius_image`, and `level_characteristic` above are the repaired
finite-level interface.  In the following, abbreviate

    U := chapter07MaximalUnramifiedExtension K Ω k κ T
    G := Chapter07MaximalUnramifiedAutomorphismGroup K Ω k κ T.

1. For each `f`, define the inclusion `ι f : T.level f →ₐ[K] U` by
   `x ↦ ⟨x.1, (le_iSup (fun n => T.level n) f) x.2⟩`.  Define

       restrict f : G →* (T.level f ≃ₐ[K] T.level f)

   by restricting `σ` and `σ.symm` along `ι f`.  Both images land in the
   level by `T.level_characteristic f σ` (and the same field applied to
   `σ.symm`); prove the inverse laws by `Subtype.ext` and the inverse laws of
   `σ`.  The defining equation to retain is

       ι f (restrict f σ x) = σ (ι f x).

2. First assemble a global arithmetic Frobenius `F : G`.  For `x : U`, use
   directedness of the levels (a common level is supplied by
   `T.compositum_lcm`) to choose `f` and `xf : T.level f` with `ι f xf = x`,
   and set `F x := ι f (T.level_frobenius f xf)`.  Independence of this
   choice follows by moving two representatives to the lcm level and applying
   `T.level_frobenius_compatible` twice.  Prove preservation of `0`, `1`,
   addition, multiplication, and the `K`-algebra map after moving all inputs
   to one lcm level.  The identical construction with
   `(T.level_frobenius f).symm` is the inverse (derive inverse compatibility
   from forward compatibility and injectivity).  Package the two maps as an
   `AlgEquiv`.  Record

       restrict_frobenius : restrict f F = T.level_frobenius f.

   `Submodule.mem_iSup_of_directed` from
   `Mathlib/LinearAlgebra/Span/Defs.lean` is the useful membership lemma after
   viewing the intermediate fields as submodules; alternatively the same
   choice argument can be proved with `Algebra.iSup_induction` from
   `Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean`.

3. Define the finite quotient by the literal composite

       quotient f := (T.level_galois_equiv f).toMonoidHom.comp (restrict f).

   For surjectivity, if `a : Multiplicative (ZMod f.1)`, take the natural
   representative `a.toAdd.val` and use `F ^ a.toAdd.val`.  Apply
   `T.level_galois_equiv f` to the desired restriction equality; its homomorphism
   law, `restrict_frobenius`, and `T.level_frobenius_image` reduce it to the
   corresponding equality in `ZMod f.1`.

4. For compatibility when `h : m.1 ∣ n.1`, let
   `a := (T.level_galois_equiv n (restrict n σ)).toAdd.val`.  Injectivity of
   `T.level_galois_equiv n` expresses `restrict n σ` as the `a`-th power of
   finite Frobenius.  Restrict this pointwise equality to `T.level m` and use
   `T.level_frobenius_compatible`; applying `T.level_galois_equiv m` gives

       ZMod.castHom h (ZMod m.1) ((quotient n σ).toAdd) =
         (quotient m σ).toAdd.

   Apply `Multiplicative.toAdd.injective`/`ofAdd` to obtain precisely the
   `quotient_compatible` field.  This argument is important: arbitrary cyclic
   equivalences need not commute with restriction; normalization at the
   compatible Frobenius is what proves they do.

5. For separation, equality of every quotient implies equality of every
   `restrict f` by injectivity of `T.level_galois_equiv f`.  Every `x : U`
   lies in a finite level by the directed-union membership argument from step
   2, so the restriction equation and `Subtype.ext` give `σ x = τ x`; finish
   with `AlgEquiv.ext`.

6. For `x : Chapter07ProfiniteIntegerCompletion`, repeat the direct-union
   construction of step 2 using, on level `f`,

       (T.level_frobenius f) ^ (x.1 f).val.

   If levels divide, `x.2 m n h` says that the two exponents have the same
   image in `ZMod m.1`.  To prove equality of the corresponding powers, apply
   the injective `T.level_galois_equiv m`, use its map-power law and
   `T.level_frobenius_image`, and simplify in `ZMod`; no choice of integer
   exponent is required.  Use the lcm level for unrelated representatives.
   Addition of compatible residue families proves the multiplication law for
   the constructed automorphisms, and the family `-x` supplies the inverse.
   Call the resulting element `realize x : G`; its construction gives

       quotient f (realize x) = Multiplicative.ofAdd (x.1 f),

   which is `quotient_realizes`.

7. Take `arithmeticFrobenius := F`.  Step 2 and
   `T.level_frobenius_image` give every `arithmeticFrobenius_image`.  Assemble
   `Chapter07MaximalUnramifiedGaloisData` with the quotient maps and the four
   properties proved above.

Do not try to obtain compatible generators from `T.level_is_galois` plus
`chapter07_finite_residue_galois_group_is_cyclic`: that theorem returns an
independent generator/equivalence at each invocation, and supplies no
restriction compatibility.  Likewise, extending one finite automorphism at a
time proves finite surjectivity but cannot realize an arbitrary compatible
inverse-limit family.
-/
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
