import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.Flat.Equalizer
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Section01TheoremAndHypotheses

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
  rw [chapter14_absolute_affine_envelope_evaluation_eq_toSpecΓ]
  constructor
  · intro h
    exact @AlgebraicGeometry.Scheme.instIsOpenImmersionToSpecΓOfIsQuasiAffine X h
  · intro h
    exact @Scheme.IsQuasiAffine.mk X inferInstance
      (@AlgebraicGeometry.IsImmersion.instOfIsOpenImmersion _ _ X.toSpecΓ h)

/-! ## Base change of an evaluation map -/

/-- The base change of a map into an affine envelope.  This is kept in the
shared interface so that the local affine-envelope charts below can state
their compatibility with the evaluation map without depending on the later
descent section. -/
def chapter14EvaluationBaseChange {X S E T : Scheme.{u}}
    (f : X ⟶ S) (p : E ⟶ S) (e : X ⟶ E) (g : T ⟶ S)
    (he : e ≫ p = f) : pullback f g ⟶ pullback p g := by
  refine pullback.lift (pullback.fst f g ≫ e) (pullback.snd f g) ?_
  rw [Category.assoc, he]
  exact pullback.condition

/-- The canonical affine map to an affine base open for the absolute envelope
of a restriction. -/
def chapter14AbsoluteAffineEnvelopeStructureMap
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (hU : IsAffineOpen U) :
    chapter14AbsoluteAffineEnvelope (pullback f U.ι) ⟶ U.toScheme :=
  Spec.map (pullback.snd f U.ι).appTop ≫ Spec.map U.topIso.inv ≫ hU.isoSpec.inv

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
  overlap : index → index → Finset X.Opens
  overlapAffine : ∀ (i j) (U), U ∈ overlap i j → IsAffineOpen U
  overlapContained : ∀ (i j) (U), U ∈ overlap i j → U ≤ chart i ⊓ chart j
  overlapCovers : ∀ (i j) (x : X), x ∈ chart i → x ∈ chart j →
    ∃ U, U ∈ overlap i j ∧ x ∈ U

theorem chapter14_finite_affine_equalizer_cover_exists (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (Chapter14FiniteAffineEqualizerCover X) := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  let chart (i : 𝒰.I₀) : X.Opens := (𝒰.f i).opensRange
  have chartAffine (i : 𝒰.I₀) : IsAffineOpen (chart i) := by
    exact isAffineOpen_opensRange (𝒰.f i)
  have chartCovers (x : X) : ∃ i, x ∈ chart i := by
    obtain ⟨i, hi⟩ := 𝒰.exists_eq x
    exact ⟨i, hi⟩
  have hcompact (i j : 𝒰.I₀) :
      IsCompact ((chart i ⊓ chart j : X.Opens) : Set X) := by
    change IsCompact ((chart i : Set X) ∩ (chart j : Set X))
    exact
      (quasiSeparatedSpace_iff_forall_affineOpens.mp inferInstance
        ⟨chart i, chartAffine i⟩ ⟨chart j, chartAffine j⟩)
  choose s hs hse using fun i j ↦
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X)
      (U := chart i ⊓ chart j)).mp (hcompact i j)
  let overlap (i j : 𝒰.I₀) : Finset X.Opens :=
    (hs i j).toFinset.image (fun V : X.affineOpens ↦ (V : X.Opens))
  refine ⟨{
    index := 𝒰.I₀
    finiteIndex := inferInstance
    chart := chart
    chartAffine := chartAffine
    chartCovers := chartCovers
    overlap := overlap
    overlapAffine := ?_
    overlapContained := ?_
    overlapCovers := ?_ }⟩
  · intro i j U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    exact V.property
  · intro i j U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    rw [hse i j]
    have hV' : V ∈ s i j := by simpa using hV
    exact le_iSup_of_le V (le_iSup_of_le hV' le_rfl)
  · intro i j x hxi hxj
    have hx : x ∈ (chart i ⊓ chart j : X.Opens) := ⟨hxi, hxj⟩
    rw [hse i j] at hx
    obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hV, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV
    refine ⟨(V : X.Opens), ?_, hxV⟩
    exact Finset.mem_image.mpr ⟨V, by simpa using hV, rfl⟩

/-! ## The relative function algebra -/

/-- The commutative-algebra interface on the pushforward of the structure
sheaf.  The carrier is kept together with its canonical pushforward
identification, while the sectionwise ring, restriction, and scalar maps are
all recorded explicitly for the relative `Spec` construction. -/
structure Chapter14RelativeFunctionAlgebra {X S : Scheme.{u}} (f : X ⟶ S) where
  carrier : S.Modules
  carrier_eq_pushforward : carrier = chapter14RelativeGlobalFunctions f
  pushforward_isQuasicoherent :
    ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent
  isQuasicoherent : carrier.IsQuasicoherent
  sectionsCommRing : ∀ U : S.Opens, CommRing Γ(carrier, U)
  sectionsRingEquiv :
    ∀ U : S.Opens,
      letI := sectionsCommRing U
      CommRingCat.of Γ(carrier, U) ≅ CommRingCat.of Γ(X, f ⁻¹ᵁ U)
  restrictionRingHom :
    ∀ {U V : S.Opens} (_i : U ⟶ V),
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
  sectionsRingEquiv_restriction :
    ∀ {U V : S.Opens} (i : U ⟶ V),
      letI := sectionsCommRing U
      letI := sectionsCommRing V
      CommRingCat.ofHom (restrictionRingHom i) ≫ (sectionsRingEquiv U).hom =
        (sectionsRingEquiv V).hom ≫
          X.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op
  sectionsRingEquiv_scalar :
    ∀ U : S.Opens,
      letI := sectionsCommRing U
      CommRingCat.ofHom (scalarRingHom U) ≫ (sectionsRingEquiv U).hom = f.app U
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
    (chapter14RelativeFunctionAlgebra f).carrier.IsQuasicoherent := by
  exact (chapter14RelativeFunctionAlgebra f).isQuasicoherent

theorem chapter14_relative_global_functions_is_quasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    (chapter14RelativeGlobalFunctions f).IsQuasicoherent := by
  simpa [chapter14RelativeGlobalFunctions] using
    (chapter14RelativeFunctionAlgebra f).pushforward_isQuasicoherent

/-! ## The relative affine envelope interface -/

/-- A relative `Spec`/affine-envelope interface.  Its local charts identify
the pullback over every affine base open with the absolute affine envelope of
the restricted source, and the comparison carries evaluation to the
canonical evaluation map. -/
structure Chapter14AffineEnvelopeLocalChart
    {X S E : Scheme.{u}} (f : X ⟶ S) (p : E ⟶ S) (e : X ⟶ E)
    (he : e ≫ p = f) (U : S.Opens) (hU : IsAffineOpen U) where
  comparison :
    pullback p U.ι ≅ chapter14AbsoluteAffineEnvelope (pullback f U.ι)
  comparison_over_base :
    comparison.hom ≫ chapter14AbsoluteAffineEnvelopeStructureMap f U hU =
      pullback.snd p U.ι
  comparison_evaluation :
    chapter14EvaluationBaseChange f p e U.ι he ≫ comparison.hom =
      chapter14AbsoluteAffineEnvelopeEvaluation (pullback f U.ι)

structure Chapter14RelativeSpec {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] where
  functionAlgebra : Chapter14RelativeFunctionAlgebra f
  functionAlgebra_canonical :
    functionAlgebra = chapter14RelativeFunctionAlgebra f
  envelope : Scheme.{u}
  structureMap : envelope ⟶ S
  affine : IsAffineHom structureMap
  evaluation : X ⟶ envelope
  evaluation_over_base : evaluation ≫ structureMap = f
  /-- The relative affine envelope represents maps from `X` to affine
  `S`-schemes.  This is the universal-property link between the envelope
  and the relative global-function algebra. -/
  universal :
    ∀ {Y : Scheme.{u}} (q : Y ⟶ S), IsAffineHom q →
      ∀ (k : X ⟶ Y), k ≫ q = f →
        ∃! u : envelope ⟶ Y,
          u ≫ q = structureMap ∧ evaluation ≫ u = k
  localChart : ∀ (U : S.Opens) (hU : IsAffineOpen U),
    Nonempty (Chapter14AffineEnvelopeLocalChart f structureMap evaluation
      evaluation_over_base U hU)

/- The established affine-envelope name is retained as an abbreviation, so
all existing projections and downstream statements remain definitionally
unchanged. -/
abbrev Chapter14AffineEnvelope {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] := Chapter14RelativeSpec f

theorem chapter14_affine_envelope_exists {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] : Nonempty (Chapter14AffineEnvelope f) := by
  sorry

noncomputable def chapter14AffineEnvelope {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] : Chapter14AffineEnvelope f :=
  Classical.choice (chapter14_affine_envelope_exists f)

noncomputable def chapter14RelativeSpec {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] : Chapter14RelativeSpec f :=
  chapter14AffineEnvelope f

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

theorem chapter14_affine_envelope_universal {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] {Y : Scheme.{u}} (q : Y ⟶ S)
    (hAffine : IsAffineHom q) (k : X ⟶ Y) (hk : k ≫ q = f) :
    ∃! u : chapter14AffineEnvelopeScheme f ⟶ Y,
      u ≫ q = chapter14AffineEnvelopeMap f ∧
        chapter14AffineEnvelopeEvaluation f ≫ u = k := by
  exact (chapter14AffineEnvelope f).universal q hAffine k hk

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

/-! ## Sheaf and affine-envelope base-change interfaces -/

/-- The sheaf-level flat base-change comparison for relative global
functions.  Since `comparison` lives in `T.Modules`, its morphism already
contains the compatible maps on all restrictions of sections. -/
structure Chapter14RelativeGlobalFunctionsBaseChangeData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] where
  comparison :
    (Scheme.Modules.pullback g).obj (chapter14RelativeGlobalFunctions f) ≅
      chapter14RelativeGlobalFunctions (chapter14BaseChangeToBase f g)
  comparison_restriction :
    ∀ {U V : T.Opens} (i : U ⟶ V),
      ((Scheme.Modules.pullback g).obj (chapter14RelativeGlobalFunctions f)).val.map i.op ≫
          (ModuleCat.restrictScalars
            (RingCat.Hom.hom (T.ringCatSheaf.obj.map i.op))).map
            (comparison.hom.val.app (.op U)) =
        comparison.hom.val.app (.op V) ≫
          (chapter14RelativeGlobalFunctions (chapter14BaseChangeToBase f g)).val.map i.op

/-- The base-change of the affine-envelope evaluation map. -/
def chapter14AffineEnvelopeEvaluationBaseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14BaseChange f g ⟶
      pullback (chapter14AffineEnvelopeMap f) g := by
  refine pullback.lift
    (chapter14BaseChangeToSource f g ≫ chapter14AffineEnvelopeEvaluation f)
    (chapter14BaseChangeToBase f g) ?_
  rw [Category.assoc, chapter14_affine_envelope_evaluation_over_base]
  exact pullback.condition

/-- The affine-envelope comparison after flat base change, together with its
compatibility over the base and with evaluation. -/
structure Chapter14AffineEnvelopeBaseChangeData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] [Flat g] where
  comparison :
    pullback (chapter14AffineEnvelopeMap f) g ≅
      (chapter14AffineEnvelope (chapter14BaseChangeToBase f g)).envelope
  comparison_over_base :
    comparison.hom ≫ chapter14AffineEnvelopeMap (chapter14BaseChangeToBase f g) =
      pullback.snd (chapter14AffineEnvelopeMap f) g
  comparison_evaluation :
    chapter14AffineEnvelopeEvaluationBaseChange f g ≫ comparison.hom =
      chapter14AffineEnvelopeEvaluation (chapter14BaseChangeToBase f g)

abbrev chapter14Fpqc {T S : Scheme.{u}} (g : T ⟶ S) : Prop :=
  LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11.Scheme.IsFpqcMorphism g

theorem chapter14_fpqc_iff {T S : Scheme.{u}} (g : T ⟶ S) :
    chapter14Fpqc g ↔ Flat g ∧ Surjective g ∧ QuasiCompact g :=
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
  exact Scheme.mem_basicOpen_top X g x

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14
