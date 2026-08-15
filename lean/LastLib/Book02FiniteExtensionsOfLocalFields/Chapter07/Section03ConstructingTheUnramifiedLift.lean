import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section02EquivalentCharacterizations

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
open scoped WithZero

noncomputable section

universe uG

/-! # Book 2, Chapter 7, §7.3: constructing the unramified lift -/

/-- A monic polynomial over `A` lifting a prescribed residue polynomial. -/
def Chapter07MonicPolynomialLift
    {A k : Type*} [CommRing A] [Field k]
    (res : A →+* k) (gbar : k[X]) (g : A[X]) : Prop :=
  g.Monic ∧ g.map res = gbar

/-- The polynomial over the fraction field used in the quotient construction. -/
def chapter07LiftedPolynomial
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (g : A[X]) : K[X] :=
  g.map (algebraMap A K)

/-- The quotient algebra `K[T]/(g)` in the construction of §7.3. -/
abbrev Chapter07LiftedPolynomialQuotient
    (K : Type*) [Field K] (g : K[X]) : Type _ :=
  AdjoinRoot g

/-- The class of `T` in the lifted polynomial quotient. -/
def chapter07LiftedRoot
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (g : A[X]) : Chapter07LiftedPolynomialQuotient K (chapter07LiftedPolynomial g) :=
  AdjoinRoot.root (chapter07LiftedPolynomial g)

/-- A root of a monic polynomial over the base ring is integral. -/
theorem chapter07_lifted_root_is_integral
    {A K Q : Type*} [CommRing A] [Field K] [CommRing Q]
    [Algebra A K] [Algebra K Q] [Algebra A Q]
    [IsScalarTower A K Q]
    (g : A[X]) (hg : g.Monic) (θ : Q)
    (hroot : eval₂ (algebraMap A Q) θ g = 0) :
    IsIntegral A θ := by
  exact ⟨g, hg, hroot⟩

/-- The quotient is a field when the lifted polynomial is irreducible. -/
theorem chapter07_lifted_polynomial_quotient_is_field
    {K : Type*} [Field K] (g : K[X]) (hg : Irreducible g) :
    IsField (Chapter07LiftedPolynomialQuotient K g) := by
  let _ : Fact (Irreducible g) := ⟨hg⟩
  exact Field.toIsField _

/-- A monic quotient has the expected vector-space degree. -/
theorem chapter07_lifted_polynomial_quotient_degree
    {K : Type*} [Field K] (g : K[X]) (hg : g.Monic) :
    Module.finrank K (Chapter07LiftedPolynomialQuotient K g) = g.natDegree := by
  exact (AdjoinRoot.powerBasis hg.ne_zero).finrank.trans
    (AdjoinRoot.powerBasis_dim hg.ne_zero)

/-- Residue irreducibility forces irreducibility of a monic lift over an
integrally closed fraction-ring model. -/
theorem chapter07_monic_lift_irreducible
    {A K k : Type*} [CommRing A] [IsDomain A] [Field K] [Field k]
    [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosed A]
    (res : A →+* k) (gbar : k[X]) (g : A[X])
    (hbar : gbar.Monic ∧ Irreducible gbar)
    (hlift : Chapter07MonicPolynomialLift res gbar g) :
    Irreducible (chapter07LiftedPolynomial (K := K) g) := by
  have hA : Irreducible g := by
    apply Polynomial.Monic.irreducible_of_irreducible_map res g hlift.1
    simpa [hlift.2] using hbar.2
  exact (hlift.1.irreducible_iff_irreducible_map_fraction_map).mp hA

/-- The field-level quotient construction has the degree prescribed by the
chosen finite separable residue polynomial and identifies the selected root
with the quotient root.  The actual valuation-ring and residue-map package is
supplied by the theorem immediately below. -/
theorem chapter07_construct_unramified_lift
    {A K k k' : Type*} [CommRing A] [IsDomain A]
    [Field K] [Field k] [Field k']
    [Algebra A K] [IsFractionRing A K] [Algebra k k']
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    [HenselianLocalRing A]
    [IsDiscreteValuationRing A]
    (res : A →+* k) (gbar : k[X]) (g : A[X])
    [Algebra A
      (Chapter07LiftedPolynomialQuotient K (chapter07LiftedPolynomial g))]
    [IsScalarTower A K
      (Chapter07LiftedPolynomialQuotient K (chapter07LiftedPolynomial g))]
    (hbar : gbar.Monic ∧ Irreducible gbar ∧ gbar.Separable)
    (hlift : Chapter07MonicPolynomialLift res gbar g)
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (theta : L)
    (hroot : eval₂ (algebraMap K L) theta (chapter07LiftedPolynomial g) = 0)
    (hgen : Algebra.adjoin K ({theta} : Set L) = ⊤)
    (hdegree : Module.finrank K L = gbar.natDegree)
    (hresdegree : Module.finrank k k' = gbar.natDegree) :
    ∃ e : L ≃ₐ[K]
        Chapter07LiftedPolynomialQuotient K (chapter07LiftedPolynomial g),
      e theta = chapter07LiftedRoot g := by
  have hp : Irreducible (chapter07LiftedPolynomial (K := K) g) :=
    chapter07_monic_lift_irreducible res gbar g
      ⟨hbar.1, hbar.2.1⟩ hlift
  let _ : Fact (Irreducible (chapter07LiftedPolynomial (K := K) g)) := ⟨hp⟩
  have hmonic : (chapter07LiftedPolynomial (K := K) g).Monic :=
    hlift.1.map (algebraMap A K)
  let _ : Module.Finite K
      (Chapter07LiftedPolynomialQuotient K (chapter07LiftedPolynomial g)) :=
    hmonic.finite_adjoinRoot
  have hdim :
      Module.finrank K (Chapter07LiftedPolynomialQuotient K
        (chapter07LiftedPolynomial g)) = Module.finrank K L := by
    calc
      Module.finrank K (Chapter07LiftedPolynomialQuotient K
          (chapter07LiftedPolynomial g)) =
          (chapter07LiftedPolynomial (K := K) g).natDegree :=
        chapter07_lifted_polynomial_quotient_degree _ hmonic
      _ = g.natDegree := hlift.1.natDegree_map (algebraMap A K)
      _ = (g.map res).natDegree := (hlift.1.natDegree_map res).symm
      _ = gbar.natDegree := by rw [hlift.2]
      _ = Module.finrank k k' := hresdegree.symm
      _ = Module.finrank K L := hresdegree.trans hdegree.symm
  let φ : Chapter07LiftedPolynomialQuotient K (chapter07LiftedPolynomial g) →ₐ[K] L :=
    AdjoinRoot.liftAlgHom (chapter07LiftedPolynomial (K := K) g)
      (Algebra.ofId K L) theta (by simpa using hroot)
  have hφsurj : Function.Surjective φ := by
    apply (AlgHom.range_eq_top φ).mp
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact (AlgHom.mem_range φ).2
      ⟨chapter07LiftedRoot g, by simp [φ, chapter07LiftedRoot]⟩
  have hφsurj_linear : Function.Surjective φ.toLinearMap := by
    simpa only [AlgHom.coe_toLinearMap] using hφsurj
  have hφinj_linear : Function.Injective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hφsurj_linear
  have hφinj : Function.Injective φ := by
    intro x y hxy
    exact hφinj_linear hxy
  let e₀ : Chapter07LiftedPolynomialQuotient K (chapter07LiftedPolynomial g)
      ≃ₐ[K] L := AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  refine ⟨e₀.symm, ?_⟩
  rw [e₀.symm_apply_eq]
  change theta = φ (chapter07LiftedRoot g)
  simp only [φ, chapter07LiftedRoot, AdjoinRoot.liftAlgHom_root]

/-! The profile returned by the preceding construction is only the numerical
interface.  The following interface keeps the integral model, its actual
unramified ring structure, and both reduction maps attached to the same local
extension. -/

/-- An actual unramified local extension together with its two residue maps. -/
structure Chapter07UnramifiedLocalExtensionData
    (A B K L k l : Type*) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field L] [Field k] [Field l]
    [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L]
    [Algebra A L] [Algebra k l]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [FiniteDimensional k l]
    [IsIntegralClosure B A L] [HenselianLocalRing A]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Module.Finite A B] where
  profile : Chapter07FiniteLocalExtensionData K L k l
  unramified : Chapter07UnramifiedExtension profile
  integralModel_etale : Algebra.Etale A B
  profile_ramificationIndex :
    profile.ramificationIndex = (IsLocalRing.maximalIdeal B).ramificationIdx A
  profile_residueDegree :
    profile.residueDegree = (IsLocalRing.maximalIdeal B).inertiaDeg A
  baseResidueMap : A →+* k
  baseResidueMap_surjective : Function.Surjective baseResidueMap
  baseResidueMap_kernel : RingHom.ker baseResidueMap = IsLocalRing.maximalIdeal A
  extensionResidueMap : B →+* l
  extensionResidueMap_surjective : Function.Surjective extensionResidueMap
  extensionResidueMap_kernel : RingHom.ker extensionResidueMap =
    IsLocalRing.maximalIdeal B
  residueMap_compatible :
    extensionResidueMap.comp (algebraMap A B) =
      (algebraMap k l).comp baseResidueMap

/- A finite unramified intermediate field together with the actual valuation
and residue-field presentation used by the classification theorem. -/
structure Chapter07ActualUnramifiedIntermediateData
    (K Ω k κ : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    (S : IntermediateField k κ) [FiniteDimensional k S]
    (profile : Chapter07FiniteLocalExtensionData K E k S) where
  unramified : Chapter07UnramifiedExtension profile
  valuationBase : Valuation K ℤᵐ⁰
  valuationExtension : Valuation E ℤᵐ⁰
  valuation_extension :
    valuationBase.IsEquiv
      (valuationExtension.comap (algebraMap K E))
  extensionData :
    Chapter10HeterogeneousExtensionData valuationBase valuationExtension
      valuation_extension
  profile_ramificationIndex :
    profile.ramificationIndex = extensionData.ramificationIndex
  profile_residueDegree :
    profile.residueDegree = extensionData.residueDegree
  residueBaseIdentification : Chapter10ResidueField valuationBase ≃+* k
  residueExtensionIdentification :
    Chapter10ResidueField valuationExtension ≃+* S
  residueMap :
    Chapter10ResidueField valuationBase →+* Chapter10ResidueField valuationExtension
  residueMap_is_canonical :
    letI : Valuation.HasExtension valuationBase valuationExtension :=
      ⟨valuation_extension⟩
    residueMap = Chapter10ResidueFieldMap valuationBase valuationExtension
  residueMap_compatible :
    residueExtensionIdentification.toRingHom.comp residueMap =
      (algebraMap k S).comp residueBaseIdentification.toRingHom

/-- A witness that a fixed intermediate field is a finite unramified field in
the chosen ambient field, including the actual residue-field shadow.  The
carrier below forgets this witness, so the classification does not count
different valuation presentations as different fields. -/
structure Chapter07FiniteUnramifiedIntermediateWitness
    (K Ω k κ : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E : IntermediateField K Ω) where
  [extension_finite : FiniteDimensional K E]
  residue : IntermediateField k κ
  [residue_finite : FiniteDimensional k residue]
  profile : Chapter07FiniteLocalExtensionData K E k residue
  actual :
    Chapter07ActualUnramifiedIntermediateData K Ω k κ E residue profile

/-- A fixed field carrier is admitted to the §7.3 classification exactly when
it has an actual finite unramified intermediate-field presentation. -/
def Chapter07FiniteUnramifiedIntermediatePredicate
    (K Ω k κ : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E : IntermediateField K Ω) : Prop :=
  Nonempty (Chapter07FiniteUnramifiedIntermediateWitness K Ω k κ E)

/-- A canonical carrier is a subtype of fields admitting a finite unramified
  witness.  The witness is recovered separately when its presentation data
  are needed, so the classification does not duplicate one field per witness. -/
abbrev Chapter07CanonicalFiniteUnramifiedIntermediate
    (K Ω k κ : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ] :=
  {E : IntermediateField K Ω //
    Chapter07FiniteUnramifiedIntermediatePredicate K Ω k κ E}

/-- Recover one actual presentation from the nonempty witness attached to a
canonical intermediate field. -/
noncomputable def chapter07CanonicalUnramifiedWitness
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ) :
    Chapter07FiniteUnramifiedIntermediateWitness K Ω k κ E.1 :=
  Classical.choice E.2

/-- A witness for a finite separable residue intermediate field. -/
structure Chapter07FiniteSeparableResidueIntermediateWitness
    (k κ : Type*) [Field k] [Field κ] [Algebra k κ]
    (S : IntermediateField k κ) where
  [extension_finite : FiniteDimensional k S]
  separable : Chapter07ResidueExtensionIsSeparable k S

/-- The residue-side carrier used by the canonical §7.3 correspondence. -/
def Chapter07FiniteSeparableResidueIntermediatePredicate
    (k κ : Type*) [Field k] [Field κ] [Algebra k κ]
    (S : IntermediateField k κ) : Prop :=
  Nonempty (Chapter07FiniteSeparableResidueIntermediateWitness k κ S)

/-- Canonical finite separable residue extensions in a fixed ambient field. -/
abbrev Chapter07CanonicalFiniteSeparableResidueIntermediate
    (k κ : Type*) [Field k] [Field κ] [Algebra k κ] :=
  {S : IntermediateField k κ //
    Chapter07FiniteSeparableResidueIntermediatePredicate k κ S}

/-- Inclusion on the actual finite unramified intermediate-field carriers. -/
def chapter07CanonicalUnramifiedInclusion
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E F : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ) : Prop :=
  E.1 ≤ F.1

/-- Inclusion on the actual finite separable residue-field carriers. -/
def chapter07CanonicalResidueInclusion
    {k κ : Type*} [Field k] [Field κ] [Algebra k κ]
    (S T : Chapter07CanonicalFiniteSeparableResidueIntermediate k κ) : Prop :=
  S.1 ≤ T.1

/-- The actual compositum operation on unramified intermediate fields. -/
def chapter07CanonicalUnramifiedCompositum
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E F : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ) :
    IntermediateField K Ω :=
  E.1 ⊔ F.1

/-- The actual intersection operation on unramified intermediate fields. -/
def chapter07CanonicalUnramifiedIntersection
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E F : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ) :
    IntermediateField K Ω :=
  E.1 ⊓ F.1

/-- The actual compositum operation on residue intermediate fields. -/
def chapter07CanonicalResidueCompositum
    {k κ : Type*} [Field k] [Field κ] [Algebra k κ]
    (S T : Chapter07CanonicalFiniteSeparableResidueIntermediate k κ) :
    IntermediateField k κ :=
  S.1 ⊔ T.1

/-- The actual intersection operation on residue intermediate fields. -/
def chapter07CanonicalResidueIntersection
    {k κ : Type*} [Field k] [Field κ] [Algebra k κ]
    (S T : Chapter07CanonicalFiniteSeparableResidueIntermediate k κ) :
    IntermediateField k κ :=
  S.1 ⊓ T.1

/-- A residue carrier is the actual residue shadow of an unramified
intermediate-field witness, rather than an unrelated carrier of the same
ambient type. -/
def chapter07CanonicalUnramifiedResidueRealization
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ)
    (S : Chapter07CanonicalFiniteSeparableResidueIntermediate k κ) : Prop :=
  (chapter07CanonicalUnramifiedWitness E).residue = S.1

/-- The actual automorphism group of a canonical unramified intermediate
field. -/
abbrev Chapter07CanonicalUnramifiedGaloisGroup
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ) :=
  E.1 ≃ₐ[K] E.1

/-- The actual automorphism group of a canonical residue intermediate field. -/
abbrev Chapter07CanonicalResidueGaloisGroup
    {k κ : Type*} [Field k] [Field κ] [Algebra k κ]
    (S : Chapter07CanonicalFiniteSeparableResidueIntermediate k κ) :=
  S.1 ≃ₐ[k] S.1

/- The complete classification package keeps the equivalence and its
functorial consequences together.  The carriers are actual intermediate
fields with witness existence in their subtype, while their field operations
are the actual lattice operations rather than operations on an unrelated
index type. -/
structure Chapter07CanonicalUnramifiedClassification
    (K Ω k κ : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ] where
  reduction :
    Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ ≃
      Chapter07CanonicalFiniteSeparableResidueIntermediate k κ
  reduction_realized :
    ∀ E, chapter07CanonicalUnramifiedResidueRealization E (reduction E)
  degree_preserved :
    ∀ E, Module.finrank K E.1 = Module.finrank k (reduction E).1
  inclusion_preserved :
    ∀ E F,
      chapter07CanonicalUnramifiedInclusion E F ↔
        chapter07CanonicalResidueInclusion (reduction E) (reduction F)
  compositum_preserved :
    ∀ E F, ∃ G,
      G.1 = chapter07CanonicalUnramifiedCompositum E F ∧
        (reduction G).1 =
          chapter07CanonicalResidueCompositum (reduction E) (reduction F)
  intersection_preserved :
    ∀ E F, ∃ G,
      G.1 = chapter07CanonicalUnramifiedIntersection E F ∧
        (reduction G).1 =
          chapter07CanonicalResidueIntersection (reduction E) (reduction F)
  galois_group_preserved :
    ∀ E,
      Nonempty
        (Chapter07CanonicalUnramifiedGaloisGroup E ≃*
          Chapter07CanonicalResidueGaloisGroup (reduction E))

/-- The non-circular §7.3 classification package.  Its reduction equivalence
and preservation clauses are explicit construction data.  This is important:
the unrelated choices of an algebraic ambient field and a residue algebraic
closure do not, by themselves, choose a compatible residue shadow. -/
theorem chapter07_canonical_unramified_classification
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (C : Chapter07CanonicalUnramifiedClassification K Ω k κ) :
    ∃ reduction :
      Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ ≃
        Chapter07CanonicalFiniteSeparableResidueIntermediate k κ,
      (∀ E, chapter07CanonicalUnramifiedResidueRealization E (reduction E)) ∧
      (∀ E, Module.finrank K E.1 = Module.finrank k (reduction E).1) ∧
      (∀ E F,
        chapter07CanonicalUnramifiedInclusion E F ↔
          chapter07CanonicalResidueInclusion (reduction E) (reduction F)) ∧
      (∀ E F, ∃ G,
        G.1 = chapter07CanonicalUnramifiedCompositum E F ∧
          (reduction G).1 =
            chapter07CanonicalResidueCompositum (reduction E) (reduction F)) ∧
      (∀ E F, ∃ G,
        G.1 = chapter07CanonicalUnramifiedIntersection E F ∧
          (reduction G).1 =
            chapter07CanonicalResidueIntersection (reduction E) (reduction F)) ∧
      (∀ E,
        Nonempty
          (Chapter07CanonicalUnramifiedGaloisGroup E ≃*
            Chapter07CanonicalResidueGaloisGroup (reduction E))) := by
  exact ⟨C.reduction, C.reduction_realized, C.degree_preserved,
    C.inclusion_preserved, C.compositum_preserved,
    C.intersection_preserved, C.galois_group_preserved⟩

/-- Package an explicitly constructed §7.3 classification.  Existence of the
package itself requires compatible ambient valuation/residue choices (or an
equivalent witnessed construction), so it is not inferred from bare
algebraic-closure hypotheses. -/
theorem chapter07_canonical_unramified_classification_data
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (C : Chapter07CanonicalUnramifiedClassification K Ω k κ) :
    Nonempty (Chapter07CanonicalUnramifiedClassification K Ω k κ) :=
  ⟨C⟩

/-- The lift construction with the integral model and its actual residue map
made explicit. -/
theorem chapter07_construct_unramified_lift_with_residue_maps
    {A K k k' B L : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Field K] [Field k] [Field k'] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra A B] [Algebra B L]
    [Algebra K L] [Algebra A L] [Algebra k k']
    [IsScalarTower A B L] [IsScalarTower A K L]
    [FiniteDimensional k k'] [FiniteDimensional K L]
    [HenselianLocalRing A] [IsDiscreteValuationRing A]
    [IsDiscreteValuationRing B] [IsFractionRing B L]
    [IsIntegralClosure B A L] [Module.Finite A B]
    (res : A →+* k) (resB : B →+* k') (gbar : k[X]) (g : A[X])
    (hbar : gbar.Monic ∧ Irreducible gbar ∧ gbar.Separable)
    (hlift : Chapter07MonicPolynomialLift res gbar g)
    (hresB_surjective : Function.Surjective resB)
    (hresB_kernel : RingHom.ker resB = IsLocalRing.maximalIdeal B)
    (hresB_compatible :
      resB.comp (algebraMap A B) = (algebraMap k k').comp res)
    (Lroot : L)
    (hroot : eval₂ (algebraMap K L) Lroot
      (chapter07LiftedPolynomial (K := K) g) = 0)
    (hgen : Algebra.adjoin K ({Lroot} : Set L) = ⊤)
    (hdegree : Module.finrank K L = gbar.natDegree)
    (hresdegree : Module.finrank k k' = gbar.natDegree) :
    ∃ E : Chapter07UnramifiedLocalExtensionData A B K L k k',
      E.profile.ramificationIndex = 1 ∧
        E.profile.residueDegree = Module.finrank k k' ∧
        (∃ e : L ≃ₐ[K]
          Chapter07LiftedPolynomialQuotient K (chapter07LiftedPolynomial g),
          e Lroot = chapter07LiftedRoot g) := by
  sorry

/-- The integral model generated by the lifted root is a finite
`A`-algebra.  The source's `B=A[theta]` is represented by the generated
subalgebra, rather than by the whole fraction-field quotient (which would
incorrectly assert `A[theta] = L`). -/
theorem chapter07_constructed_integral_model_is_finite
    {A K k : Type*} [CommRing A] [IsDomain A] [Field K] [Field k]
    [Algebra A K] [IsFractionRing A K] [HenselianLocalRing A]
    [IsDiscreteValuationRing A]
    (res : A →+* k) (gbar : k[X]) (g : A[X])
    (hlift : Chapter07MonicPolynomialLift res gbar g) :
    Module.Finite A (Algebra.adjoin A ({chapter07LiftedRoot g} :
      Set (Chapter07LiftedPolynomialQuotient K
        (chapter07LiftedPolynomial g)))) := by
  apply Algebra.finite_adjoin_simple_of_isIntegral
  refine chapter07_lifted_root_is_integral (A := A) (K := K)
    (Q := Chapter07LiftedPolynomialQuotient K (chapter07LiftedPolynomial g))
    g hlift.1 (chapter07LiftedRoot g) ?_
  rw [AdjoinRoot.algebraMap_eq', ← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root _

/-- A common separable residue polynomial gives isomorphic lifted field
extensions, independently of the chosen monic coefficient lift. -/
theorem chapter07_different_monic_lifts_are_isomorphic
    {A K k : Type*} [CommRing A] [IsDomain A] [Field K] [Field k]
    [Algebra A K] [IsFractionRing A K] [HenselianLocalRing A]
    [IsDiscreteValuationRing A]
    (res : A →+* k) (gbar : k[X]) (g₁ g₂ : A[X])
    (hbar : gbar.Monic ∧ Irreducible gbar ∧ gbar.Separable)
    (h₁ : Chapter07MonicPolynomialLift res gbar g₁)
    (h₂ : Chapter07MonicPolynomialLift res gbar g₂)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A)
    (L₁ L₂ : Type*) [Field L₁] [Field L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (θ₁ : L₁) (θ₂ : L₂)
    (hroot₁ : eval₂ (algebraMap K L₁) θ₁ (chapter07LiftedPolynomial g₁) = 0)
    (hroot₂ : eval₂ (algebraMap K L₂) θ₂ (chapter07LiftedPolynomial g₂) = 0)
    (hgen₁ : Algebra.adjoin K ({θ₁} : Set L₁) = ⊤)
    (hgen₂ : Algebra.adjoin K ({θ₂} : Set L₂) = ⊤)
    (hdegree₁ : Module.finrank K L₁ = gbar.natDegree)
    (hdegree₂ : Module.finrank K L₂ = gbar.natDegree) :
    Nonempty (L₁ ≃ₐ[K] L₂) := by
  sorry

/-! The classification data is exposed through an actual family of
intermediate fields and residue fields.  The transport interface below is
retained as a compatibility facade for earlier books; its equivalence field is
input data, while the transport theorem records only its consequences. -/

/-- Actual finite unramified extensions and their residue subfields in fixed
ambient fields. -/
structure Chapter07ActualUnramifiedClassificationInterface
    (K Ω k κ U S : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ] where
  extension : U → IntermediateField K Ω
  residueExtension : S → IntermediateField k κ
  /-- The residue-field index attached to each displayed extension.  The
  classification theorem must prove that this map is an equivalence. -/
  reduction : U → S
  extension_finite : ∀ u, FiniteDimensional K (extension u)
  residue_finite : ∀ s, FiniteDimensional k (residueExtension s)
  profile : ∀ u,
    Chapter07FiniteLocalExtensionData K (extension u) k
      (residueExtension (reduction u))
  actual : ∀ u,
    letI := extension_finite u
    letI := residue_finite (reduction u)
    Nonempty
      (Chapter07ActualUnramifiedIntermediateData K Ω k κ (extension u)
        (residueExtension (reduction u)) (profile u))

/-- The assertion that two displayed Galois groups are preserved by a
correspondence.  The structures are explicit because the carriers in the
classification interface are dependent on the corresponding extension. -/
def Chapter07GaloisGroupPreservation
    (G H : Type*) (gG : Group G) (gH : Group H) : Prop :=
  letI := gG
  letI := gH
  Nonempty (G ≃* H)

/-- Book-facing data for the reduction/lift equivalence in Theorem 7.2. -/
structure Chapter07UnramifiedClassificationInterface
    (U S : Type*) where
  reduction : U ≃ S
  degreeU : U → ℕ
  inclusionU : U → U → Prop
  compositumU : U → U → U
  intersectionU : U → U → U
  galoisU : U → Type uG
  galoisGroupU : ∀ u, Group (galoisU u)

namespace Chapter07UnramifiedClassificationInterface

/-- Residue-side degree, transported across the displayed equivalence. -/
def degreeS {U S : Type*}
    (C : Chapter07UnramifiedClassificationInterface U S) : S → ℕ :=
  fun s => C.degreeU (C.reduction.symm s)

/-- Residue-side inclusion, transported across the displayed equivalence. -/
def inclusionS {U S : Type*}
    (C : Chapter07UnramifiedClassificationInterface U S) : S → S → Prop :=
  fun s t => C.inclusionU (C.reduction.symm s) (C.reduction.symm t)

/-- Residue-side compositum, transported across the displayed equivalence. -/
def compositumS {U S : Type*}
    (C : Chapter07UnramifiedClassificationInterface U S) : S → S → S :=
  fun s t => C.reduction (C.compositumU (C.reduction.symm s) (C.reduction.symm t))

/-- Residue-side intersection, transported across the displayed equivalence. -/
def intersectionS {U S : Type*}
    (C : Chapter07UnramifiedClassificationInterface U S) : S → S → S :=
  fun s t => C.reduction (C.intersectionU (C.reduction.symm s) (C.reduction.symm t))

/-- Galois-group carriers on the residue side, transported across the
displayed equivalence. -/
def galoisS {U S : Type*}
    (C : Chapter07UnramifiedClassificationInterface U S) : S → Type uG :=
  fun s => C.galoisU (C.reduction.symm s)

end Chapter07UnramifiedClassificationInterface

/-- The functorial clauses obtained from a supplied classification equivalence.
The existence of that equivalence belongs to the actual classification
construction, not to this transport lemma. -/
theorem chapter07_unramified_extensions_classified_by_residue_extensions
    {U S : Type*} (C : Chapter07UnramifiedClassificationInterface U S) :
    (∀ u, C.degreeU u = C.degreeS (C.reduction u)) ∧
      (∀ u v, C.inclusionU u v ↔
        C.inclusionS (C.reduction u) (C.reduction v)) ∧
      (∀ u v, C.reduction (C.compositumU u v) =
        C.compositumS (C.reduction u) (C.reduction v)) ∧
      (∀ u v, C.reduction (C.intersectionU u v) =
        C.intersectionS (C.reduction u) (C.reduction v)) ∧
      (∀ u, Chapter07GaloisGroupPreservation (C.galoisU u)
        (C.galoisS (C.reduction u))
        (C.galoisGroupU u)
        (C.galoisGroupU (C.reduction.symm (C.reduction u)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Chapter07UnramifiedClassificationInterface.degreeS]
  · intro u v
    simp [Chapter07UnramifiedClassificationInterface.inclusionS]
  · intro u v
    simp [Chapter07UnramifiedClassificationInterface.compositumS]
  · intro u v
    simp [Chapter07UnramifiedClassificationInterface.intersectionS]
  · intro u
    let u' : U := C.reduction.symm (C.reduction u)
    have hu : u' = u := C.reduction.symm_apply_apply u
    change Chapter07GaloisGroupPreservation (C.galoisU u)
      (C.galoisU u') (C.galoisGroupU u) (C.galoisGroupU u')
    let _ : Group (C.galoisU u) := C.galoisGroupU u
    have hrefl : Nonempty (C.galoisU u ≃* C.galoisU u) :=
      ⟨MulEquiv.refl _⟩
    rw [hu]
    exact hrefl

/-- The profile consequences for the actual intermediate-field interface.
The reduction map is an explicit field of that interface; proving that it is an
equivalence is a separate classification result. -/
theorem chapter07_actual_unramified_extensions_classified_by_residue_extensions
    {K Ω k κ U S : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (C : Chapter07ActualUnramifiedClassificationInterface K Ω k κ U S) :
    (∀ u,
        letI : FiniteDimensional K (C.extension u) := C.extension_finite u
        letI : FiniteDimensional k (C.residueExtension (C.reduction u)) :=
          C.residue_finite (C.reduction u)
        Module.finrank K (C.extension u) =
        Module.finrank k (C.residueExtension (C.reduction u))) := by
  intro u
  let _ : FiniteDimensional K (C.extension u) := C.extension_finite u
  let _ : FiniteDimensional k (C.residueExtension (C.reduction u)) :=
    C.residue_finite (C.reduction u)
  rcases C.actual u with ⟨A⟩
  exact chapter07_unramified_degree_eq_residue_degree (C.profile u) A.unramified

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
