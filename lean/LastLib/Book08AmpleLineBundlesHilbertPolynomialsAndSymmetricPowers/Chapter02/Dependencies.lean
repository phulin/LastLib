import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory

/-!
## Shared interfaces for Chapter 2

The pinned Mathlib checkout contains affine `Proj`, sheaves of modules, pullback, and the
canonical notions of quasi-coherence, local freeness, finite presentation, and closed immersion.
It does not yet expose the relative Proj of a quasi-coherent module, its universal quotient, or a
tensor product of sheaves of modules.  The interfaces below keep those book-facing constructions
bundled and make the missing dependencies explicit.  They are propositions or data interfaces,
never axioms asserting a desired theorem.
-/

/-- A quasi-coherent `𝒪_S`-module, bundled for the relative Proj interfaces. -/
structure Chapter02QuasiCoherentModule (S : Scheme.{u}) where
  carrier : S.Modules
  is_quasi_coherent : carrier.IsQuasicoherent

/-- Pullback of the underlying sheaf of modules. -/
def chapter02PullbackModule {S T : Scheme.{u}} (f : T ⟶ S)
    (E : Chapter02QuasiCoherentModule S) : T.Modules :=
  (Scheme.Modules.pullback f).obj E.carrier

/-- The book-facing quasi-coherent pullback; the preservation proof is supplied by the later API. -/
def chapter02PullbackQuasiCoherentModule {S T : Scheme.{u}} (f : T ⟶ S)
    (E : Chapter02QuasiCoherentModule S) : Chapter02QuasiCoherentModule T where
  carrier := chapter02PullbackModule f E
  is_quasi_coherent := by sorry

/-!
`LocalGeneratorsData` is the canonical Mathlib interface for local presentations.  Requiring
each free generator to have an index set equivalent to `Fin n` records the constant finite rank
condition without choosing a trivialization globally.
-/
def Chapter02LocallyFreeRank {S : Scheme.{u}} (E : S.Modules) (n : ℕ) : Prop :=
  ∃ q : E.LocalGeneratorsData.{u},
    q.IsLocallyFreeData ∧ ∀ i, Nonempty ((q.generators i).I ≃ Fin n)

def Chapter02InvertibleModule {S : Scheme.{u}} (L : S.Modules) : Prop :=
  Chapter02LocallyFreeRank L 1

/-- A line bundle is an invertible sheaf of modules. -/
structure Chapter02LineBundle (S : Scheme.{u}) where
  carrier : S.Modules
  invertible : Chapter02InvertibleModule carrier

/-- An invertible quotient of a quasi-coherent module. -/
structure Chapter02InvertibleQuotientPair {S : Scheme.{u}} (E : S.Modules) where
  line : Chapter02LineBundle S
  quotient : E ⟶ line.carrier
  quotient_is_epi : Epi quotient

/-- Isomorphism of quotient pairs, with the quotient square as its compatibility equation. -/
def chapter02QuotientPairEquivalent
    {S : Scheme.{u}} {E : S.Modules}
    (p q : Chapter02InvertibleQuotientPair E) : Prop :=
  ∃ e : p.line.carrier ≅ q.line.carrier, p.quotient ≫ e.hom = q.quotient

instance {S : Scheme.{u}} {E : S.Modules} : Setoid (Chapter02InvertibleQuotientPair E) where
  r := chapter02QuotientPairEquivalent
  iseqv := by
    sorry

abbrev Chapter02InvertibleQuotientClass {S : Scheme.{u}} (E : S.Modules) :=
  Quotient (inferInstance : Setoid (Chapter02InvertibleQuotientPair E))

def chapter02QuotientClassMk {S : Scheme.{u}} {E : S.Modules}
    (p : Chapter02InvertibleQuotientPair E) : Chapter02InvertibleQuotientClass E :=
  Quotient.mk _ p

theorem chapter02QuotientClass_eq_iff {S : Scheme.{u}} {E : S.Modules}
    (p q : Chapter02InvertibleQuotientPair E) :
    chapter02QuotientClassMk p = chapter02QuotientClassMk q ↔
      chapter02QuotientPairEquivalent p q := by
  sorry

/-- Pullback preserves the line-bundle condition. -/
def chapter02PullbackLineBundle {S T : Scheme.{u}} (f : T ⟶ S)
    (L : Chapter02LineBundle S) : Chapter02LineBundle T where
  carrier := (Scheme.Modules.pullback f).obj L.carrier
  invertible := by sorry

def chapter02PullbackInvertibleQuotientPair
    {S T : Scheme.{u}} (f : T ⟶ S) {E : S.Modules}
    (p : Chapter02InvertibleQuotientPair E) :
    Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback f).obj E) where
  line := chapter02PullbackLineBundle f p.line
  quotient := (Scheme.Modules.pullback f).map p.quotient
  quotient_is_epi := by sorry

/-!
The relative projective bundle package records exactly the scheme, structure morphism, twisting
line bundle, and universal quotient used in the book.  The existence theorem is the one natural
dependency not supplied by pinned Mathlib: affine `Proj` is available, but relative `Proj_S(Sym E)`
and its universal quotient are not.
-/
structure Chapter02ProjectiveBundleData
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) where
  scheme : Scheme.{u}
  projection : scheme ⟶ S
  twistingLineBundle : Chapter02LineBundle scheme
  universalQuotient :
    (Scheme.Modules.pullback projection).obj E.carrier ⟶ twistingLineBundle.carrier
  universalQuotient_is_epi : Epi universalQuotient
  /-- The representability statement that identifies this package with relative Proj. -/
  universalProperty : ∀ {T : Scheme.{u}} (f : T ⟶ S),
    {u : T ⟶ scheme // u ≫ projection = f} ≃
      Chapter02InvertibleQuotientClass ((Scheme.Modules.pullback f).obj E.carrier)
  /-- The universal equivalence is normalized by the displayed universal quotient. -/
  universalProperty_compatible :
    ∀ {T : Scheme.{u}} (f : T ⟶ S)
      (u : {u : T ⟶ scheme // u ≫ projection = f}),
      ∃ p : Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback f).obj E.carrier),
        universalProperty f u = chapter02QuotientClassMk p ∧
          ∃ e : p.line.carrier ≅ (Scheme.Modules.pullback u.1).obj twistingLineBundle.carrier,
            p.quotient ≫ e.hom =
              (Scheme.Modules.pullbackCongr u.2).inv.app E.carrier ≫
                (Scheme.Modules.pullbackComp u.1 projection).inv.app E.carrier ≫
                (Scheme.Modules.pullback u.1).map universalQuotient

/- LOCAL_DEPENDENCY_GUESS: relative Proj of a quasi-coherent module and the universal quotient. -/
theorem chapter02_relative_projective_bundle_exists
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Nonempty (Chapter02ProjectiveBundleData S E) := by
  sorry

noncomputable def chapter02ProjectiveBundleData
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Chapter02ProjectiveBundleData S E :=
  Classical.choice (chapter02_relative_projective_bundle_exists S E)

abbrev chapter02ProjectiveBundle
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) : Scheme.{u} :=
  (chapter02ProjectiveBundleData S E).scheme

abbrev chapter02ProjectiveBundleProjection
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    chapter02ProjectiveBundle S E ⟶ S :=
  (chapter02ProjectiveBundleData S E).projection

abbrev chapter02ProjectiveBundleTwistingLine
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Chapter02LineBundle (chapter02ProjectiveBundle S E) :=
  (chapter02ProjectiveBundleData S E).twistingLineBundle

abbrev chapter02ProjectiveBundleOOne
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    Chapter02LineBundle (chapter02ProjectiveBundle S E) :=
  chapter02ProjectiveBundleTwistingLine S E

abbrev chapter02ProjectiveBundleUniversalQuotient
    (S : Scheme.{u}) (E : Chapter02QuasiCoherentModule S) :
    (Scheme.Modules.pullback (chapter02ProjectiveBundleProjection S E)).obj E.carrier ⟶
      (chapter02ProjectiveBundleTwistingLine S E).carrier :=
  (chapter02ProjectiveBundleData S E).universalQuotient

def chapter02ProjectiveBundleMapOver
    {S T : Scheme.{u}} {E : Chapter02QuasiCoherentModule S}
    (f : T ⟶ S) (u : T ⟶ chapter02ProjectiveBundle S E) : Prop :=
  u ≫ chapter02ProjectiveBundleProjection S E = f

noncomputable def chapter02PullbackCompositionIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    ((Scheme.Modules.pullback (f ≫ g)).obj M) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackComp f g).symm.app M

/-!
The canonical comparison also transports an invertible quotient along a composite.  Keeping this
pair-level map explicit prevents later quotient-class maps from silently choosing unrelated
representatives.
-/
def chapter02PullbackInvertibleQuotientPairAlongComposition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {E : Z.Modules}
    (p : Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback g).obj E)) :
    Chapter02InvertibleQuotientPair ((Scheme.Modules.pullback (f ≫ g)).obj E) where
  line := chapter02PullbackLineBundle f p.line
  quotient :=
    (chapter02PullbackCompositionIso f g E).hom ≫
      (Scheme.Modules.pullback f).map p.quotient
  quotient_is_epi := by sorry

/-!
Mathlib's `free` sheaf gives the canonical free module and its global-section equivalence.  The
quasi-coherence proof is intentionally kept here so all later sections use the same free module.
-/
def chapter02FreeQuasiCoherentModule (S : Scheme.{u}) (I : Type u) :
    Chapter02QuasiCoherentModule S where
  carrier := SheafOfModules.free (R := S.ringCatSheaf) I
  is_quasi_coherent := by sorry

/-- The zero global section. -/
noncomputable def chapter02ZeroSection {S : Scheme.{u}} (M : S.Modules) : M.sections :=
  M.val.sectionsMk (fun X => 0) (by
    intro X Y f
    exact (M.val.map f).hom.map_zero)

/-!
Pullback of global sections is a useful book-facing bridge.  The actual construction depends on
the inverse-image/sheafification implementation, which is not exposed as a named map in the
pinned module API; its underlying function is isolated here rather than duplicated in section
statements.
-/
structure Chapter02PullbackSectionData
    {S T : Scheme.{u}} (f : T ⟶ S) (M : S.Modules) where
  map : M.sections → ((Scheme.Modules.pullback f).obj M).sections

/- LOCAL_DEPENDENCY_GUESS: canonical pullback on global sections. -/
theorem chapter02_pullback_section_data_exists
    {S T : Scheme.{u}} (f : T ⟶ S) (M : S.Modules) :
    Nonempty (Chapter02PullbackSectionData f M) := by
  sorry

noncomputable def chapter02PullbackSectionData
    {S T : Scheme.{u}} (f : T ⟶ S) (M : S.Modules) :
    Chapter02PullbackSectionData f M :=
  Classical.choice (chapter02_pullback_section_data_exists f M)

/-!
The pinned checkout has no monoidal structure for sheaves of modules.  This is the minimal
book-facing tensor-power carrier needed for `L^d` in homogeneous evaluation statements; later
proof work should replace it by the actual sheaf tensor powers and coherence.
-/
structure Chapter02LineBundlePowerData {S : Scheme.{u}} (L : Chapter02LineBundle S) where
  power : ℕ → S.Modules
  power_invertible : ∀ d, Chapter02InvertibleModule (power d)
  power_zero : power 0 ≅ SheafOfModules.unit S.ringCatSheaf
  power_one : power 1 ≅ L.carrier

/- LOCAL_DEPENDENCY_GUESS: tensor powers of an invertible sheaf. -/
theorem chapter02_line_bundle_power_data_exists
    {S : Scheme.{u}} (L : Chapter02LineBundle S) :
    Nonempty (Chapter02LineBundlePowerData L) := by
  sorry

noncomputable def chapter02LineBundlePowerData
    {S : Scheme.{u}} (L : Chapter02LineBundle S) : Chapter02LineBundlePowerData L :=
  Classical.choice (chapter02_line_bundle_power_data_exists L)

def chapter02LineBundlePower {S : Scheme.{u}} (L : Chapter02LineBundle S) (d : ℕ) : S.Modules :=
  (chapter02LineBundlePowerData L).power d

def chapter02LineBundlePowerBundle
    {S : Scheme.{u}} (L : Chapter02LineBundle S) (d : ℕ) : Chapter02LineBundle S where
  carrier := chapter02LineBundlePower L d
  invertible := (chapter02LineBundlePowerData L).power_invertible d

/-!
`Chapter02GradedAlgebra` is a small wrapper around Mathlib's canonical `GradedAlgebra` class.  The
wrapper lets us put the grading in data so that `Proj` can be used without a global instance leak.
-/
structure Chapter02GradedAlgebra
    (R A : Type u) [CommSemiring R] [Semiring A] [Algebra R A] where
  component : ℕ → Submodule R A
  graded : GradedAlgebra component

def chapter02ProjOfGradedAlgebra
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) : Scheme.{u} := by
  letI : GradedAlgebra G.component := G.graded
  exact AlgebraicGeometry.Proj G.component

/-!
The degree-zero projection supplies the canonical structure morphism of a graded `R`-algebra.
This is the ring-level bridge used by both ordinary projective space and homogeneous quotients.
-/
noncomputable def chapter02GradedAlgebraToSpec
    (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (G : Chapter02GradedAlgebra R A) :
    chapter02ProjOfGradedAlgebra G ⟶ AlgebraicGeometry.Spec (CommRingCat.of R) := by
  letI : GradedAlgebra G.component := G.graded
  exact AlgebraicGeometry.Proj.toSpecZero G.component ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' G.component).comp (algebraMap R A)))

/- LOCAL_DEPENDENCY_GUESS: the pinned API has `SymmetricAlgebra` but no canonical internal grading. -/
theorem chapter02_symmetric_algebra_grading_exists
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Nonempty (Chapter02GradedAlgebra R (SymmetricAlgebra R M)) := by
  sorry

noncomputable def chapter02SymmetricAlgebraGrading
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Chapter02GradedAlgebra R (SymmetricAlgebra R M) :=
  Classical.choice (chapter02_symmetric_algebra_grading_exists R M)

def chapter02SymmetricAlgebraProj
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] : Scheme.{u} :=
  chapter02ProjOfGradedAlgebra (chapter02SymmetricAlgebraGrading R M)

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
