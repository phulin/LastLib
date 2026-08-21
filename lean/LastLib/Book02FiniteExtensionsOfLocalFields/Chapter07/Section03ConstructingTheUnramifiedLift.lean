import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section02EquivalentCharacterizations

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
open scoped WithZero

noncomputable section

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
ambient type.  The witness is part of this proposition: using the global
`Classical.choice` made by `chapter07CanonicalUnramifiedWitness` here would
make the classification depend on an unrelated choice of presentation and
need not produce a bijective reduction map. -/
def chapter07CanonicalUnramifiedResidueRealization
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ)
    (S : Chapter07CanonicalFiniteSeparableResidueIntermediate k κ) : Prop :=
  ∃ W : Chapter07FiniteUnramifiedIntermediateWitness K Ω k κ E.1,
    W.residue = S.1

/-- The carrier predicate above deliberately forgets presentations.  An
existence theorem based on one valuation must therefore say that every
admitted carrier has a presentation based on that valuation and on the fixed
identification of its residue field. -/
def Chapter07CanonicalUnramifiedCarriersAreBasedAt
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (vK : Valuation K ℤᵐ⁰) (rho : Chapter10ResidueField vK ≃+* k) : Prop :=
  ∀ E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ,
    ∃ W : Chapter07FiniteUnramifiedIntermediateWitness K Ω k κ E.1,
      letI := W.extension_finite
      letI := W.residue_finite
      W.actual.valuationBase = vK ∧
        HEq W.actual.residueBaseIdentification rho

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
  extension_finite : ∀ E :
    Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ,
    FiniteDimensional K E.1
  residue_finite : ∀ S :
    Chapter07CanonicalFiniteSeparableResidueIntermediate k κ,
    FiniteDimensional k S.1
  reduction_realized :
    ∀ E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ,
      chapter07CanonicalUnramifiedResidueRealization E (reduction E)
  degree_preserved :
    ∀ E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ,
      letI := extension_finite E
      letI := residue_finite (reduction E)
      Module.finrank K E.1 = Module.finrank k (reduction E).1
  inclusion_preserved :
    ∀ (E F : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ),
      chapter07CanonicalUnramifiedInclusion E F ↔
        chapter07CanonicalResidueInclusion (reduction E) (reduction F)
  compositum_preserved :
    ∀ (E F : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ), ∃ G,
      G.1 = chapter07CanonicalUnramifiedCompositum E F ∧
        (reduction G).1 =
          chapter07CanonicalResidueCompositum (reduction E) (reduction F)
  intersection_preserved :
    ∀ (E F : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ), ∃ G,
      G.1 = chapter07CanonicalUnramifiedIntersection E F ∧
        (reduction G).1 =
          chapter07CanonicalResidueIntersection (reduction E) (reduction F)
  galois_preserved :
    ∀ E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ,
      IsGalois K E.1 ↔ IsGalois k (reduction E).1
  galois_group_preserved :
    ∀ E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ,
      Nonempty
        (Chapter07CanonicalUnramifiedGaloisGroup E ≃*
          Chapter07CanonicalResidueGaloisGroup (reduction E))

/-- A carrier based at the fixed valuation has an actual finite separable
residue shadow.  The realization retains the particular witness supplied by
`hcarriers`, rather than making an unrelated global choice of presentation. -/
theorem chapter07_based_unramified_residue_shadow
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (vK : Valuation K ℤᵐ⁰) (rho : Chapter10ResidueField vK ≃+* k)
    (hcarriers : Chapter07CanonicalUnramifiedCarriersAreBasedAt
      (Ω := Ω) (κ := κ) vK rho)
    (E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ) :
    ∃ S : Chapter07CanonicalFiniteSeparableResidueIntermediate k κ,
      chapter07CanonicalUnramifiedResidueRealization E S := by
  obtain ⟨W, _hvaluation, _hresidue⟩ := hcarriers E
  let _ : FiniteDimensional K E.1 := W.extension_finite
  let _ : FiniteDimensional k W.residue := W.residue_finite
  let S : Chapter07CanonicalFiniteSeparableResidueIntermediate k κ :=
    ⟨W.residue, ⟨
      { separable := W.actual.unramified.2 }
    ⟩⟩
  exact ⟨S, W, rfl⟩

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
      (∀ E,
        letI := C.extension_finite E
        letI := C.residue_finite (C.reduction E)
        Module.finrank K E.1 = Module.finrank k (reduction E).1) ∧
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
      (∀ E, IsGalois K E.1 ↔ IsGalois k (reduction E).1) ∧
      (∀ E,
        Nonempty
          (Chapter07CanonicalUnramifiedGaloisGroup E ≃*
            Chapter07CanonicalResidueGaloisGroup (reduction E))) := by
  exact ⟨C.reduction, C.reduction_realized, C.degree_preserved,
    C.inclusion_preserved, C.compositum_preserved,
    C.intersection_preserved, C.galois_preserved,
    C.galois_group_preserved⟩

/- The fixed-closure classification is an existence theorem under the local
valuation and algebraic-closure hypotheses.  The structure above records the
actual reduction equivalence and its consequences; it is not itself a
substitute for this theorem. -/
theorem chapter07_canonical_unramified_classification_exists
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [IsAlgClosed κ] [Algebra.IsAlgebraic k κ]
    (vK : Valuation K ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (residueIdentification : Chapter10ResidueField vK ≃+* k)
    (hcarriers : Chapter07CanonicalUnramifiedCarriersAreBasedAt
      (Ω := Ω) (κ := κ) vK residueIdentification) :
    Nonempty (Chapter07CanonicalUnramifiedClassification K Ω k κ) := by
  /-
  Proof roadmap (after repairing `reduction_realized` to retain its witness).

  The original hypotheses were not sufficient for the stated carrier type:
  `Chapter07FiniteUnramifiedIntermediatePredicate` admits a field witnessed
  using *any* valuation on `K` and any residue identification, whereas `vK`
  controls only one valuation.  The added `hcarriers` hypothesis is the
  minimal compatibility condition needed without globally reparameterizing
  every carrier by `(vK, residueIdentification)`.  Put
  `A := vK.valuationSubring`, and install the rank-one-discrete valuation-ring
  and DVR instances on `A`.  The completeness hypothesis is the input for
  the henselian lift; the relevant earlier results are
  `Chapter09.complete_separated_local_ring_has_simple_root_henselianity` in
  Book01/Chapter09/Section04HenselianLocalRings.lean (after proving the
  separated instance for the DVR), or the valued-field formulation
  `Chapter09.complete_valued_field_is_henselian` in
  Book01/Chapter09/Section06AlgebraicConsequences.lean after converting adic
  completeness to the induced `CompleteSpace` instance.

  1. First prove a focused finite-level lifting helper, before this theorem,
     with the following mathematical interface: for every

         S : Chapter07CanonicalFiniteSeparableResidueIntermediate k κ

     it returns `E : IntermediateField K Ω`, instances
     `FiniteDimensional K E` and `FiniteDimensional k S.1`, and
     `W : Chapter07FiniteUnramifiedIntermediateWitness K Ω k κ E` with
     `W.residue = S.1`.  Recover the residue finiteness from
     `Classical.choice S.2`; recover separability from its `separable` field.
     Use `IsAlgClosed.lift` from
     Mathlib/FieldTheory/IsAlgClosed/Basic.lean to embed the finite separable
     residue extension in `κ`, and similarly embed the lifted finite
     algebraic field in `Ω` (take the `fieldRange` of the resulting
     `AlgHom`).  Both uses of `IsAlgClosed.lift` should leave the source and
     target universes inferred independently (`S.1 : Type _`, `κ : Type _`
     and the lifted quotient `L : Type _`, `Ω : Type _`); `fieldRange`
     produces an `IntermediateField` without any same-universe assumption.

  2. Construct the lift at the valuation-ring level, not just at the field
     quotient level.  Choose a primitive-element polynomial for `S.1`, lift
     its coefficients through the quotient map corresponding to
     `residueIdentification`, and
     use `chapter07_monic_lift_irreducible` and
     `chapter07_construct_unramified_lift` above for the field quotient and
     degree.  The integral closure in that quotient must then be equipped
     with its quotient residue map.  Feed those maps to
     `chapter07_construct_unramified_lift_with_residue_maps` below; it supplies
     the `Chapter07UnramifiedExtension`, `Algebra.Etale`, and the two profile
     equalities required by `Chapter07ActualUnramifiedIntermediateData`.
     Finally use `chapter01_theorem_1_1_finite` from
     Book02/Chapter01/Section02ExistenceUniquenessAndCompleteness.lean for the
     unique extension valuation and its rank-one-discrete normalization, and
     `chapter10_heterogeneous_extension_data_exists` from
     Book01/Chapter10/Section04RamificationIndexAndResidueDegree.lean for
     `extensionData`.

  3. Prove the converse finite-level helper: for
     `E : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ`, extract a
     witness from `hcarriers E` (not merely from `E.2`); its two compatibility
     equalities identify its base valuation and residue map with the fixed
     inputs.  Its `residue`, finite instance, and the separability
     clause `W.actual.unramified.2` give an element of the residue subtype.
     (The theorem `chapter07_unramified_is_separable` in
     Section01IsolatingResidueGrowth.lean instead proves separability of the
     extension upstairs.)  Do not use `chapter07CanonicalUnramifiedWitness`
     to define the correspondence: the repaired realization proposition
     existentially retains the particular witness used by the lift.

  4. Establish uniqueness on both sides.  Two lifts of the same embedded
     residue field are equal as intermediate fields in `Ω`: apply the
     henselian uniqueness of the finite etale lift, transport its `K`-algebra
     equivalence into `Ω`, and prove that the resulting *unramified
     subextensions with the fixed residue embedding* coincide.  Generic
     embeddings into an algebraic closure are not unique, so
     `IsAlgClosed.lift` alone cannot prove this equality.  Conversely, residue
     shadows of one actual
     unramified intermediate field are equal in `κ` after transporting the
     compatible residue identifications.  These statements must also prove
     compatibility with inclusions.  They are what makes the two finite-level
     maps inverse and should be exposed as helper lemmas, rather than hidden
     in an `Equiv.ofBijective` proof.

  5. Define `reduction` from the converse helper and `reduction.symm` from the
     lift helper.  Fill `reduction_realized E` with the extracted witness and
     its residue equality.  Fill `extension_finite` and `residue_finite` from
     the stored witnesses.  Degree preservation follows from
     `chapter07_unramified_degree_eq_residue_degree` in
     Section01IsolatingResidueGrowth.lean; inclusion preservation is the compatibility
     lemma from step 4.  Apply inclusion preservation and lattice
     extensionality to obtain the compositum and intersection clauses.
     Transport separability/Galoisness through the residue construction for
     `galois_preserved`, and construct `galois_group_preserved` from the
     reduction action as in `Chapter06UnramifiedGaloisReduction` in
     Chapter06/Section02FrobeniusInAnUnramifiedExtension.lean.

  Current API obstruction: steps 2 and 4 are not packaged by any imported
  declaration.  In particular, `chapter07_construct_unramified_lift` only
  identifies an already supplied field with an `AdjoinRoot`, and
  `chapter07_construct_unramified_lift_with_residue_maps` verifies an already
  supplied integral closure and residue maps.  The normal proof stage must
  first add the finite integral/residue construction and the uniqueness/
  functoriality helpers described above; `IsAlgClosed.lift` and finrank
  equality alone cannot manufacture the required reduction equivalence.
  -/
  sorry

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
  let : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
  let : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  let : Module.IsTorsionFree A B :=
    (Module.isTorsionFree_iff_faithfulSMul).mpr inferInstance
  have hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A := by
    ext a
    constructor
    · intro ha
      have hz : resB (algebraMap A B a) = 0 := by
        calc
          resB (algebraMap A B a) = algebraMap k k' (res a) :=
            DFunLike.congr_fun hresB_compatible a
          _ = 0 := by rw [ha]; simp
      have hmem : algebraMap A B a ∈ IsLocalRing.maximalIdeal B := by
        rw [← hresB_kernel]
        exact (RingHom.mem_ker).mpr hz
      have hcomap : a ∈ (IsLocalRing.maximalIdeal B).comap
          (algebraMap A B) := hmem
      rw [IsLocalRing.maximalIdeal_comap] at hcomap
      exact hcomap
    · intro ha
      have hmem : algebraMap A B a ∈ IsLocalRing.maximalIdeal B :=
        map_nonunit (algebraMap A B) a ha
      have hz : resB (algebraMap A B a) = 0 := by
        apply (RingHom.mem_ker).mp
        rw [hresB_kernel]
        exact hmem
      apply (RingHom.injective (algebraMap k k'))
      simpa using (show algebraMap k k' (res a) = 0 by
        calc
          algebraMap k k' (res a) = resB (algebraMap A B a) :=
            (DFunLike.congr_fun hresB_compatible a).symm
          _ = 0 := hz)
  let resbar : (A ⧸ IsLocalRing.maximalIdeal A) →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) res (by
      intro a ha
      exact (RingHom.mem_ker).mp (by rw [hres_kernel]; exact ha))
  let resbar' : (A ⧸ IsLocalRing.maximalIdeal A) →+* k' :=
    (algebraMap k k').comp resbar
  let : Algebra (A ⧸ IsLocalRing.maximalIdeal A) k' := resbar'.toAlgebra
  let eB : (B ⧸ IsLocalRing.maximalIdeal B) ≃+* k' := by
    exact
      (Ideal.quotEquivOfEq hresB_kernel.symm).trans
        (RingHom.quotientKerEquivOfSurjective hresB_surjective)
  let eBAlg : (B ⧸ IsLocalRing.maximalIdeal B) ≃ₐ[A ⧸ IsLocalRing.maximalIdeal A] k' :=
    AlgEquiv.ofRingEquiv (f := eB) (by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change resB (algebraMap A B a) =
        algebraMap k k' (resbar (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a))
      simpa [resbar] using DFunLike.congr_fun hresB_compatible a)
  let : (IsLocalRing.maximalIdeal A).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal A
  let : (IsLocalRing.maximalIdeal B).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal B
  have hinertia :
      (IsLocalRing.maximalIdeal B).inertiaDeg A =
        Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k' := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal
      (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)]
    exact eBAlg.toLinearEquiv.finrank_eq
  let : Algebra (A ⧸ IsLocalRing.maximalIdeal A) k := resbar.toAlgebra
  have hresbar_inj : Function.Injective resbar := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).2
    have hab : res a = res b := by
      simpa [resbar] using hxy
    have hz : res (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    rw [← hres_kernel]
    exact (RingHom.mem_ker).mpr hz
  let : FaithfulSMul (A ⧸ IsLocalRing.maximalIdeal A) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hresbar_inj
  let : IsScalarTower (A ⧸ IsLocalRing.maximalIdeal A) k k' :=
    IsScalarTower.of_algebraMap_eq (by intro x; rfl)
  have hresidue_degree_tower :
      Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k' =
        Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k *
          Module.finrank k k' := by
    exact (Module.finrank_mul_finrank' k').symm
  have hfund :
      (IsLocalRing.maximalIdeal B).ramificationIdx A *
          (IsLocalRing.maximalIdeal B).inertiaDeg A =
        Module.finrank K L := by
    have hsum :=
      Ideal.sum_ramification_inertia_eq_finrank
        (p := IsLocalRing.maximalIdeal A) (S := B)
    have hq_eq (q : (IsLocalRing.maximalIdeal A).primesOver B) :
        q.1 = IsLocalRing.maximalIdeal B := by
      exact IsLocalRing.eq_maximalIdeal
        (q.2.1.isMaximal (Ideal.ne_bot_of_mem_primesOver
          (IsDiscreteValuationRing.not_a_field A) q.2))
    let : Unique ((IsLocalRing.maximalIdeal A).primesOver B) :=
      { default := Ideal.primesOver.mk
          (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
        uniq := fun q => Subtype.ext (hq_eq q) }
    have hdefault :
        (default : (IsLocalRing.maximalIdeal A).primesOver B).1 =
          IsLocalRing.maximalIdeal B := hq_eq default
    rw [Fintype.sum_unique,
      (IsFractionRing.finrank_eq A K B L).symm] at hsum
    simpa only [hdefault] using hsum
  have hprod :
      (IsLocalRing.maximalIdeal B).ramificationIdx A *
          (Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k *
            Module.finrank k k') = Module.finrank k k' := by
    calc
      (IsLocalRing.maximalIdeal B).ramificationIdx A *
          (Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k *
            Module.finrank k k') =
          (IsLocalRing.maximalIdeal B).ramificationIdx A *
            Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k' := by
              rw [hresidue_degree_tower]
      _ = (IsLocalRing.maximalIdeal B).ramificationIdx A *
            (IsLocalRing.maximalIdeal B).inertiaDeg A := by
              rw [hinertia]
      _ = Module.finrank K L := hfund
      _ = Module.finrank k k' := hdegree.trans hresdegree.symm
  have hprod_one :
      (IsLocalRing.maximalIdeal B).ramificationIdx A *
          Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k = 1 := by
    have hpos : 0 < Module.finrank k k' := Module.finrank_pos
    apply Nat.mul_right_cancel hpos
    calc
      ((IsLocalRing.maximalIdeal B).ramificationIdx A *
          Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k) *
          Module.finrank k k' =
        (IsLocalRing.maximalIdeal B).ramificationIdx A *
          (Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k *
            Module.finrank k k') := by rw [Nat.mul_assoc]
      _ = Module.finrank k k' := hprod
      _ = 1 * Module.finrank k k' := by simp
  have hram : (IsLocalRing.maximalIdeal B).ramificationIdx A = 1 := by
    exact Nat.eq_one_of_dvd_one ⟨
      Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k,
      hprod_one.symm⟩
  have hbase_degree : Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k = 1 := by
    exact Nat.eq_one_of_dvd_one ⟨
      (IsLocalRing.maximalIdeal B).ramificationIdx A,
      by simpa [Nat.mul_comm] using hprod_one.symm⟩
  have hres_surjective : Function.Surjective res := by
    let R := A ⧸ IsLocalRing.maximalIdeal A
    have hsurj' : Function.Surjective (Algebra.linearMap R k) :=
      (letI : (IsLocalRing.maximalIdeal A).IsMaximal :=
          IsLocalRing.maximalIdeal.isMaximal A
       letI : Field R := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
       let f : R →ₗ[R] k := Algebra.linearMap R k
       let hinj' : Function.Injective f := by
         intro x y hxy
         apply hresbar_inj
         change resbar x = resbar y at hxy
         exact hxy
       let hdim : Module.finrank R R = Module.finrank R k := by
         simp [R, hbase_degree]
       letI : Module.Finite R k :=
         Module.finite_of_finrank_eq_succ (by simpa [R] using hbase_degree)
       (LinearMap.linearEquivOfInjective f hinj' hdim).surjective)
    intro y
    obtain ⟨x, hx⟩ := hsurj' y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_⟩
    change resbar (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) = y at hx
    rw [Ideal.Quotient.lift_mk] at hx
    exact hx
  have hrootA : eval₂ (algebraMap A L) Lroot g = 0 := by
    simpa [chapter07LiftedPolynomial, Polynomial.eval₂_map,
      IsScalarTower.algebraMap_eq A K L] using hroot
  have hLroot_integral : IsIntegral A Lroot := by
    exact ⟨g, hlift.1, by simpa [aeval_def] using hrootA⟩
  obtain ⟨b, hb⟩ :=
    (IsIntegralClosure.isIntegral_iff (R := A) (A := B) (B := L)).mp
      hLroot_integral
  have hrootB : eval₂ (algebraMap A B) b g = 0 := by
    apply IsFractionRing.injective B L
    rw [Polynomial.hom_eval₂, hb]
    simpa [IsScalarTower.algebraMap_eq A B L] using hrootA
  have hrootbar :
      eval₂ (algebraMap k k') (resB b) gbar = 0 := by
    have h := congrArg resB hrootB
    rw [← hlift.2, Polynomial.eval₂_map]
    simpa only [Polynomial.hom_eval₂, hresB_compatible, map_zero] using h
  have hminbar : gbar = minpoly k (resB b) := by
    exact minpoly.eq_of_irreducible_of_monic (A := k)
      hbar.2.1 hrootbar hbar.1
  have hb_integral : IsIntegral k (resB b) :=
    IsIntegral.of_finite k (resB b)
  have hres_adjoin_finrank :
      Module.finrank k (IntermediateField.adjoin k ({resB b} : Set k')) =
        gbar.natDegree := by
    rw [IntermediateField.adjoin.finrank hb_integral, hminbar]
  have hres_adjoin_top :
      IntermediateField.adjoin k ({resB b} : Set k') = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [hres_adjoin_finrank, IntermediateField.finrank_top']
    exact hresdegree.symm
  have hsep_residue_element : IsSeparable k (resB b) := by
    change (minpoly k (resB b)).Separable
    rw [← hminbar]
    exact hbar.2.2
  have hsep_residue_adjoin :
      Algebra.IsSeparable k
        (IntermediateField.adjoin k ({resB b} : Set k')) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k k').mpr
      hsep_residue_element
  let eres : IntermediateField.adjoin k ({resB b} : Set k') ≃ₐ[k] k' :=
    (IntermediateField.equivOfEq hres_adjoin_top).trans
      IntermediateField.topEquiv
  have hsep_residue : Algebra.IsSeparable k k' := by
    exact
      (Algebra.IsSeparable.iff_of_equiv_equiv
        (RingEquiv.refl k) eres.toRingEquiv (by ext; simp)).mp
        hsep_residue_adjoin
  have hinertia_k :
      (IsLocalRing.maximalIdeal B).inertiaDeg A = Module.finrank k k' := by
    calc
      (IsLocalRing.maximalIdeal B).inertiaDeg A =
          Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k' := hinertia
      _ = Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) k *
          Module.finrank k k' := hresidue_degree_tower
      _ = Module.finrank k k' := by rw [hbase_degree, Nat.one_mul]
  let profile : Chapter07FiniteLocalExtensionData K L k k' :=
    { ramificationIndex := 1
      ramificationIndex_pos := Nat.zero_lt_one
      residueDegree := Module.finrank k k'
      residueDegree_pos := Module.finrank_pos
      degree_eq_ramification_residue := by
        rw [hdegree.trans hresdegree.symm]
        simp
      residueDegree_eq := rfl }
  let : Algebra.IsSeparable k k' := hsep_residue
  have hprofile_unramified : Chapter07UnramifiedExtension profile := by
    refine ⟨rfl, ?_⟩
    intro x
    exact Algebra.IsSeparable.isSeparable k x
  have hcriteria :=
    chapter07_unramified_criteria profile
      (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B) res
      rfl rfl hres_surjective hres_kernel resB hresB_surjective
      hresB_kernel hresB_compatible (by
        change 1 = (IsLocalRing.maximalIdeal B).ramificationIdx A
        exact hram.symm) (by
        change Module.finrank k k' =
          (IsLocalRing.maximalIdeal B).inertiaDeg A
        exact hinertia_k.symm)
  have hfiniteEtale : Chapter07FiniteEtaleExtension A B :=
    hcriteria.2.2.mp hprofile_unramified
  have hEtale : Algebra.Etale A B := hfiniteEtale.2
  let E : Chapter07UnramifiedLocalExtensionData A B K L k k' :=
    { profile := profile
      unramified := hprofile_unramified
      integralModel_etale := hEtale
      profile_ramificationIndex := by
        change 1 = (IsLocalRing.maximalIdeal B).ramificationIdx A
        exact hram.symm
      profile_residueDegree := by
        change Module.finrank k k' =
          (IsLocalRing.maximalIdeal B).inertiaDeg A
        exact hinertia_k.symm
      baseResidueMap := res
      baseResidueMap_surjective := hres_surjective
      baseResidueMap_kernel := hres_kernel
      extensionResidueMap := resB
      extensionResidueMap_surjective := hresB_surjective
      extensionResidueMap_kernel := hresB_kernel
      residueMap_compatible := hresB_compatible }
  obtain ⟨e, he⟩ :=
    chapter07_construct_unramified_lift res gbar g hbar hlift
      L Lroot hroot hgen hdegree hresdegree
  exact ⟨E, rfl, rfl, ⟨e, he⟩⟩

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
extensions, independently of the chosen monic coefficient lift.  The
corresponding root of the first lift in the second field is explicit, so the
isomorphism records the root identification used by the construction. -/
theorem chapter07_different_monic_lifts_are_isomorphic
    {A K k : Type*} [CommRing A] [IsDomain A] [Field K] [Field k]
    [Algebra A K] [IsFractionRing A K] [HenselianLocalRing A]
    [IsDiscreteValuationRing A]
    (res : A →+* k) (gbar : k[X]) (g₁ g₂ : A[X])
    (hbar : gbar.Monic ∧ Irreducible gbar ∧ gbar.Separable)
    (h₁ : Chapter07MonicPolynomialLift res gbar g₁)
    (_h₂ : Chapter07MonicPolynomialLift res gbar g₂)
    (_hres_surjective : Function.Surjective res)
    (_hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A)
    (L₁ L₂ : Type*) [Field L₁] [Field L₂]
    [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (θ₁ : L₁) (θ₂ : L₂)
    (hroot₁ : eval₂ (algebraMap K L₁) θ₁ (chapter07LiftedPolynomial g₁) = 0)
    (_hroot₂ : eval₂ (algebraMap K L₂) θ₂ (chapter07LiftedPolynomial g₂) = 0)
    (θ₂' : L₂)
    (hroot₂' : eval₂ (algebraMap K L₂) θ₂'
      (chapter07LiftedPolynomial g₁) = 0)
    (hgen₁ : Algebra.adjoin K ({θ₁} : Set L₁) = ⊤)
    (_hgen₂ : Algebra.adjoin K ({θ₂} : Set L₂) = ⊤)
    (hdegree₁ : Module.finrank K L₁ = gbar.natDegree)
    (hdegree₂ : Module.finrank K L₂ = gbar.natDegree) :
    ∃ e : L₁ ≃ₐ[K] L₂, e θ₁ = θ₂' := by
  have hp₁ : Irreducible (chapter07LiftedPolynomial (K := K) g₁) :=
    chapter07_monic_lift_irreducible res gbar g₁
      ⟨hbar.1, hbar.2.1⟩ h₁
  have hmonic₁ :
      (chapter07LiftedPolynomial (K := K) g₁).Monic :=
    h₁.1.map (algebraMap A K)
  let _ : Fact (Irreducible (chapter07LiftedPolynomial (K := K) g₁)) := ⟨hp₁⟩
  let φ₁ : AdjoinRoot (chapter07LiftedPolynomial (K := K) g₁) →ₐ[K] L₁ :=
    AdjoinRoot.liftAlgHom (chapter07LiftedPolynomial (K := K) g₁)
      (Algebra.ofId K L₁) θ₁ (by simpa using hroot₁)
  have hφ₁surj : Function.Surjective φ₁ := by
    apply (AlgHom.range_eq_top φ₁).mp
    apply top_unique
    rw [← hgen₁]
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact (AlgHom.mem_range φ₁).2
      ⟨AdjoinRoot.root (chapter07LiftedPolynomial (K := K) g₁), by
        simp [φ₁]⟩
  let _ : Module.Finite K (AdjoinRoot (chapter07LiftedPolynomial (K := K) g₁)) :=
    hmonic₁.finite_adjoinRoot
  have hdim₁ :
      Module.finrank K (AdjoinRoot (chapter07LiftedPolynomial (K := K) g₁)) =
        Module.finrank K L₁ := by
    calc
      Module.finrank K (AdjoinRoot (chapter07LiftedPolynomial (K := K) g₁)) =
          (chapter07LiftedPolynomial (K := K) g₁).natDegree :=
        chapter07_lifted_polynomial_quotient_degree _ hmonic₁
      _ = g₁.natDegree := h₁.1.natDegree_map (algebraMap A K)
      _ = (g₁.map res).natDegree := (h₁.1.natDegree_map res).symm
      _ = gbar.natDegree := by rw [h₁.2]
      _ = Module.finrank K L₁ := hdegree₁.symm
  have hφ₁surj_linear : Function.Surjective φ₁.toLinearMap := by
    simpa only [AlgHom.coe_toLinearMap] using hφ₁surj
  have hφ₁inj_linear : Function.Injective φ₁.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim₁).mpr
      hφ₁surj_linear
  have hφ₁inj : Function.Injective φ₁ := by
    intro x y hxy
    exact hφ₁inj_linear hxy
  let e₁ : AdjoinRoot (chapter07LiftedPolynomial (K := K) g₁) ≃ₐ[K] L₁ :=
    AlgEquiv.ofBijective φ₁ ⟨hφ₁inj, hφ₁surj⟩
  let φ₂ : AdjoinRoot (chapter07LiftedPolynomial (K := K) g₁) →ₐ[K] L₂ :=
    AdjoinRoot.liftAlgHom (chapter07LiftedPolynomial (K := K) g₁)
      (Algebra.ofId K L₂) θ₂' (by simpa using hroot₂')
  have hθ₂'_integral : IsIntegral K θ₂' := by
    exact ⟨chapter07LiftedPolynomial (K := K) g₁, hmonic₁, hroot₂'⟩
  have hmin₂' : minpoly K θ₂' =
      chapter07LiftedPolynomial (K := K) g₁ := by
    exact (minpoly.eq_of_irreducible_of_monic hp₁ hroot₂' hmonic₁).symm
  have hθ₂'_adjoin_finrank :
      Module.finrank K (IntermediateField.adjoin K ({θ₂'} : Set L₂)) =
        gbar.natDegree := by
    rw [IntermediateField.adjoin.finrank hθ₂'_integral, hmin₂']
    calc
      (chapter07LiftedPolynomial (K := K) g₁).natDegree = g₁.natDegree :=
        h₁.1.natDegree_map (algebraMap A K)
      _ = (g₁.map res).natDegree := (h₁.1.natDegree_map res).symm
      _ = gbar.natDegree := by rw [h₁.2]
  have hθ₂'_adjoin : IntermediateField.adjoin K ({θ₂'} : Set L₂) = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [hθ₂'_adjoin_finrank, IntermediateField.finrank_top']
    exact hdegree₂.symm
  have hθ₂'_adjoin_alg : Algebra.adjoin K ({θ₂'} : Set L₂) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      hθ₂'_integral.isAlgebraic, hθ₂'_adjoin,
      IntermediateField.top_toSubalgebra]
  have hφ₂surj : Function.Surjective φ₂ := by
    apply (AlgHom.range_eq_top φ₂).mp
    apply top_unique
    rw [← hθ₂'_adjoin_alg]
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact (AlgHom.mem_range φ₂).2
      ⟨AdjoinRoot.root (chapter07LiftedPolynomial (K := K) g₁), by
        simp [φ₂]⟩
  have hdim₂ :
      Module.finrank K (AdjoinRoot (chapter07LiftedPolynomial (K := K) g₁)) =
        Module.finrank K L₂ := by
    calc
      Module.finrank K (AdjoinRoot (chapter07LiftedPolynomial (K := K) g₁)) =
          (chapter07LiftedPolynomial (K := K) g₁).natDegree :=
        chapter07_lifted_polynomial_quotient_degree _ hmonic₁
      _ = g₁.natDegree := h₁.1.natDegree_map (algebraMap A K)
      _ = (g₁.map res).natDegree := (h₁.1.natDegree_map res).symm
      _ = gbar.natDegree := by rw [h₁.2]
      _ = Module.finrank K L₂ := hdegree₂.symm
  have hφ₂surj_linear : Function.Surjective φ₂.toLinearMap := by
    simpa only [AlgHom.coe_toLinearMap] using hφ₂surj
  have hφ₂inj_linear : Function.Injective φ₂.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim₂).mpr
      hφ₂surj_linear
  have hφ₂inj : Function.Injective φ₂ := by
    intro x y hxy
    exact hφ₂inj_linear hxy
  let e₂ : AdjoinRoot (chapter07LiftedPolynomial (K := K) g₁) ≃ₐ[K] L₂ :=
    AlgEquiv.ofBijective φ₂ ⟨hφ₂inj, hφ₂surj⟩
  refine ⟨e₁.symm.trans e₂, ?_⟩
  have he₁root : e₁ (AdjoinRoot.root (chapter07LiftedPolynomial (K := K) g₁)) = θ₁ := by
    change φ₁ (AdjoinRoot.root (chapter07LiftedPolynomial (K := K) g₁)) = θ₁
    simp [φ₁]
  have he₁symm : e₁.symm θ₁ =
      AdjoinRoot.root (chapter07LiftedPolynomial (K := K) g₁) := by
    apply e₁.injective
    rw [e₁.apply_symm_apply, he₁root]
  rw [AlgEquiv.trans_apply, he₁symm]
  change φ₂ (AdjoinRoot.root (chapter07LiftedPolynomial (K := K) g₁)) = θ₂'
  simp [φ₂]

/-! The classification data is exposed through an actual family of
intermediate fields and residue fields. -/

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
  reduction_bijective : Function.Bijective reduction
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

/-- The profile consequences for the actual intermediate-field interface.
The reduction map is an explicit field of that interface; proving that it is an
equivalence is a separate classification result. -/
theorem chapter07_actual_unramified_degree_matches_residue_degree
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
