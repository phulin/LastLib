import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Book 10, Chapter 14: shared interfaces

The pinned Mathlib tree contains the absolute affine-envelope map
`Scheme.toSpecΓ`, the absolute `Scheme.IsQuasiAffine` predicate, and the
descent theorem for open immersions.  It does not contain the relative
`Spec_S(f_* 𝒪_X)` construction used by this chapter.  This file records the
relative vocabulary once, with the relative affine envelope and the
commutative-ring structure on its pushforward marked as local construction
interfaces.
-/

noncomputable section

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

/-! ## Relative quasi-affineness -/

/-- A relative affine presentation of a morphism. -/
structure Chapter14QuasiAffinePresentation {X S : Scheme.{u}} (f : X ⟶ S) where
  ambient : Scheme.{u}
  ambientMap : ambient ⟶ S
  ambientAffine : IsAffineHom ambientMap
  embedding : X ⟶ ambient
  embeddingOpen : IsOpenImmersion embedding
  overBase : embedding ≫ ambientMap = f

/-- `f : X ⟶ S` is quasi-affine when it has an open immersion into an affine
`S`-scheme.  The ambient scheme and the map to `S` remain available through
`Chapter14QuasiAffinePresentation`. -/
def chapter14QuasiAffine {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Nonempty (Chapter14QuasiAffinePresentation f)

theorem chapter14_quasiAffine_iff_exists_presentation {X S : Scheme.{u}} (f : X ⟶ S) :
    chapter14QuasiAffine f ↔ Nonempty (Chapter14QuasiAffinePresentation f) :=
  Iff.rfl

theorem chapter14_quasiAffine_mk {X S ambient : Scheme.{u}} (f : X ⟶ S)
    (ambientMap : ambient ⟶ S) (hAffine : IsAffineHom ambientMap)
    (embedding : X ⟶ ambient) (hOpen : IsOpenImmersion embedding)
    (hOver : embedding ≫ ambientMap = f) :
    chapter14QuasiAffine f := by
  exact ⟨⟨ambient, ambientMap, hAffine, embedding, hOpen, hOver⟩⟩

theorem chapter14QuasiAffinePresentation.embedding {X S : Scheme.{u}} {f : X ⟶ S}
    (h : chapter14QuasiAffine f) :
    ∃ (ambient : Scheme) (ambientMap : ambient ⟶ S) (embedding : X ⟶ ambient),
      IsAffineHom ambientMap ∧ IsOpenImmersion embedding ∧ embedding ≫ ambientMap = f := by
  rcases h with ⟨h⟩
  exact ⟨h.ambient, h.ambientMap, h.embedding, h.ambientAffine, h.embeddingOpen, h.overBase⟩

/-! ## Canonical absolute comparison -/

/-- The absolute affine envelope supplied by Mathlib. -/
noncomputable def chapter14AbsoluteAffineEnvelope (X : Scheme.{u}) : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of Γ(X, ⊤))

/-- Its canonical evaluation map. -/
def chapter14AbsoluteAffineEnvelopeEvaluation (X : Scheme.{u}) :
    X ⟶ chapter14AbsoluteAffineEnvelope X :=
  X.toSpecΓ

theorem chapter14_absolute_affine_envelope_evaluation_eq_toSpecΓ (X : Scheme.{u}) :
    chapter14AbsoluteAffineEnvelopeEvaluation X = X.toSpecΓ :=
  rfl

theorem chapter14_absolute_quasiAffine_iff_affine_envelope_open
    (X : Scheme.{u}) [CompactSpace X] :
    Scheme.IsQuasiAffine X ↔
      IsOpenImmersion (chapter14AbsoluteAffineEnvelopeEvaluation X) := by
  sorry

/-! ## Relative global functions -/

/-- The module underlying the relative direct image of the structure sheaf. -/
def chapter14RelativeGlobalFunctions {X S : Scheme.{u}} (f : X ⟶ S) : S.Modules :=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)

theorem chapter14_relative_global_functions_pushforward_formula
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) :
    Γ(chapter14RelativeGlobalFunctions f, U) =
      Γ(SheafOfModules.unit X.ringCatSheaf, f ⁻¹ᵁ U) := by
  rfl

/-- A finite affine cover with finite affine refinements of all overlaps.  It
is the exact finite equalizer input used for quasi-coherence of `f_* 𝒪_X`. -/
structure Chapter14FiniteAffineEqualizerCover (X : Scheme.{u}) where
  index : Type u
  finiteIndex : Finite index
  chart : index → X.Opens
  chartAffine : ∀ i, IsAffineOpen (chart i)
  chartCovers : ∀ x : X, ∃ i, x ∈ chart i
  overlap : ∀ i j, Finset X.Opens
  overlapAffine : ∀ (i j) (U), U ∈ overlap i j → IsAffineOpen U
  overlapContained : ∀ (i j) (U), U ∈ overlap i j → U ≤ chart i ⊓ chart j
  overlapCovers : ∀ (i j) (x : X), x ∈ chart i → x ∈ chart j →
    ∃ U, U ∈ overlap i j ∧ x ∈ U

theorem chapter14_finite_affine_equalizer_cover_exists (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (Chapter14FiniteAffineEqualizerCover X) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the canonical multiplication on the pushforward of
the structure sheaf is not exposed by the pinned `Scheme.Modules` API.  The
following record keeps the underlying pushforward module and its local ring
operations explicit; it is the interface consumed by relative `Spec`. -/
structure Chapter14RelativeFunctionAlgebra {X S : Scheme.{u}} (f : X ⟶ S) where
  carrier : S.Modules
  carrier_eq_pushforward : carrier = chapter14RelativeGlobalFunctions f
  isQuasicoherent : carrier.IsQuasicoherent
  sectionsCommRing : ∀ U : S.Opens, CommRing Γ(carrier, U)
  restrictionRingHom :
    ∀ {U V : S.Opens} (i : U ⟶ V),
      letI := sectionsCommRing U
      letI := sectionsCommRing V
      Γ(carrier, V) →+* Γ(carrier, U)
  restrictionRingHom_apply :
    ∀ {U V : S.Opens} (i : U ⟶ V) (x : Γ(carrier, V)),
      letI := sectionsCommRing U
      letI := sectionsCommRing V
      restrictionRingHom i x = carrier.presheaf.map i.op x
  scalarRingHom :
    ∀ U : S.Opens,
      letI := sectionsCommRing U
      Γ(S, U) →+* Γ(carrier, U)
  scalar_action :
    ∀ (U : S.Opens) (r : Γ(S, U)) (x : Γ(carrier, U)),
      letI := sectionsCommRing U
      scalarRingHom U r * x = r • x

theorem chapter14_relative_function_algebra_exists {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    Nonempty (Chapter14RelativeFunctionAlgebra f) := by
  sorry

noncomputable def chapter14RelativeFunctionAlgebra {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] : Chapter14RelativeFunctionAlgebra f :=
  Classical.choice (chapter14_relative_function_algebra_exists f)

theorem chapter14_relative_function_algebra_carrier_eq_pushforward
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    (chapter14RelativeFunctionAlgebra f).carrier = chapter14RelativeGlobalFunctions f := by
  exact (chapter14RelativeFunctionAlgebra f).carrier_eq_pushforward

theorem chapter14_relative_function_algebra_is_quasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    (chapter14RelativeFunctionAlgebra f).isQuasicoherent := by
  exact (chapter14RelativeFunctionAlgebra f).isQuasicoherent

theorem chapter14_relative_global_functions_is_quasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    (chapter14RelativeGlobalFunctions f).IsQuasicoherent := by
  sorry

/-! ## The relative affine envelope interface -/

/- LOCAL_DEPENDENCY_GUESS: pinned Mathlib has no relative `Spec` of a sheaf of
commutative algebras.  This record is the canonical construction interface;
the open-immersion property is deliberately not a field, so the later
quasi-affine theorem remains a genuine statement about the envelope. -/
structure Chapter14AffineEnvelope {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] where
  functionAlgebra : Chapter14RelativeFunctionAlgebra f
  functionAlgebra_canonical :
    functionAlgebra = chapter14RelativeFunctionAlgebra f
  envelope : Scheme.{u}
  structureMap : envelope ⟶ S
  affine : IsAffineHom structureMap
  evaluation : X ⟶ envelope
  evaluation_over_base : evaluation ≫ structureMap = f

theorem chapter14_affine_envelope_exists {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] : Nonempty (Chapter14AffineEnvelope f) := by
  sorry

noncomputable def chapter14AffineEnvelope {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] : Chapter14AffineEnvelope f :=
  Classical.choice (chapter14_affine_envelope_exists f)

abbrev chapter14AffineEnvelopeScheme {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] : Scheme.{u} :=
  (chapter14AffineEnvelope f).envelope

abbrev chapter14AffineEnvelopeMap {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14AffineEnvelopeScheme f ⟶ S :=
  (chapter14AffineEnvelope f).structureMap

abbrev chapter14AffineEnvelopeEvaluation {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] : X ⟶ chapter14AffineEnvelopeScheme f :=
  (chapter14AffineEnvelope f).evaluation

theorem chapter14_affine_envelope_is_affine {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    IsAffineHom (chapter14AffineEnvelopeMap f) := by
  exact (chapter14AffineEnvelope f).affine

theorem chapter14_affine_envelope_evaluation_over_base {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14AffineEnvelopeEvaluation f ≫ chapter14AffineEnvelopeMap f = f := by
  exact (chapter14AffineEnvelope f).evaluation_over_base

/-! ## Base change and fpqc vocabulary -/

noncomputable def chapter14BaseChange {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) : Scheme :=
  pullback f g

abbrev chapter14BaseChangeToSource {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) : chapter14BaseChange f g ⟶ X :=
  pullback.fst f g

abbrev chapter14BaseChangeToBase {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) : chapter14BaseChange f g ⟶ T :=
  pullback.snd f g

def chapter14Fpqc {T S : Scheme.{u}} (g : T ⟶ S) : Prop :=
  Surjective g ∧ Flat g ∧ QuasiCompact g

theorem chapter14_fpqc_iff {T S : Scheme.{u}} (g : T ⟶ S) :
    chapter14Fpqc g ↔ Surjective g ∧ Flat g ∧ QuasiCompact g :=
  Iff.rfl

/-! ## Relative restriction and principal opens -/

noncomputable def chapter14RestrictionToOpen {X S : Scheme.{u}}
    (f : X ⟶ S) (U : S.Opens) : Scheme :=
  pullback f U.ι

abbrev chapter14RestrictionToOpenMap {X S : Scheme.{u}}
    (f : X ⟶ S) (U : S.Opens) : chapter14RestrictionToOpen f U ⟶ U.toScheme :=
  pullback.snd f U.ι

abbrev chapter14RelativeFunctionsOnOpen {X S : Scheme.{u}}
    (f : X ⟶ S) (U : S.Opens) :=
  Γ(chapter14RestrictionToOpen f U, ⊤)

def chapter14PrincipalOpen {X : Scheme.{u}} (g : Γ(X, ⊤)) : X.Opens :=
  X.basicOpen g

theorem chapter14_mem_principalOpen_iff {X : Scheme.{u}} (g : Γ(X, ⊤)) (x : X) :
    x ∈ chapter14PrincipalOpen g ↔
      IsUnit (X.presheaf.germ ⊤ x trivial g) := by
  exact Scheme.mem_basicOpen_top g x

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14
