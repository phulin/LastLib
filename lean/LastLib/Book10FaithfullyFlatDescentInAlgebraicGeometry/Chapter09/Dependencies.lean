import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09

noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

/-! ## Book-facing finite locally free and fpqc interfaces -/

/-- A finite locally free module sheaf of the constant rank `r`.

`LocalGeneratorsData` is Mathlib's finite local presentation interface; requiring every
generator index to be equivalent to `Fin r` records the constant rank without choosing a global
basis.
-/
def chapter09FiniteLocallyFreeOfRank {X : Scheme.{u}} (M : X.Modules) (r : ℕ) : Prop :=
  M.IsFiniteType ∧
    ∃ q : M.LocalGeneratorsData.{u},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty ((q.generators i).I ≃ Fin r)

/-- A rank-`r` vector bundle, with its finite locally free carrier exposed. -/
structure Chapter09VectorBundle (X : Scheme.{u}) (r : ℕ) where
  carrier : X.Modules
  locallyFree : chapter09FiniteLocallyFreeOfRank carrier r

/-- A line bundle is a rank-one vector bundle. -/
abbrev Chapter09LineBundle (X : Scheme.{u}) := Chapter09VectorBundle X 1

instance {X : Scheme.{u}} {r : ℕ} : Coe (Chapter09VectorBundle X r) X.Modules :=
  ⟨Chapter09VectorBundle.carrier⟩

/-- Morphisms of vector bundles are morphisms of their module sheaves. -/
abbrev Chapter09VectorBundleMorphism
    {X : Scheme.{u}} {r s : ℕ}
    (E : Chapter09VectorBundle X r) (F : Chapter09VectorBundle X s) :=
  E.carrier ⟶ F.carrier

/-- Isomorphism of vector bundles through their underlying module sheaves. -/
def chapter09VectorBundleIsomorphic
    {X : Scheme.{u}} {r : ℕ}
    (E F : Chapter09VectorBundle X r) : Prop :=
  Nonempty (E.carrier ≅ F.carrier)

/-- An fpqc morphism used as a single-cover descent datum. -/
structure Chapter09FpqcCover {S T : Scheme.{u}} (p : T ⟶ S) : Prop where
  flat : Flat p
  quasiCompact : QuasiCompact p
  surjective : Surjective p

abbrev Chapter09PullbackModule
    {S T : Scheme.{u}} (p : T ⟶ S) (M : S.Modules) : T.Modules :=
  (Scheme.Modules.pullback p).obj M

/-- Pullback preserves the vector-bundle carrier; the preservation proof is the local module
descent bridge used by this chapter. -/
noncomputable def chapter09PullbackVectorBundle
    {S T : Scheme.{u}} (p : T ⟶ S)
    {r : ℕ} (E : Chapter09VectorBundle S r) : Chapter09VectorBundle T r where
  carrier := Chapter09PullbackModule p E.carrier
  locallyFree := by sorry

noncomputable def chapter09PullbackLineBundle
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle S) : Chapter09LineBundle T :=
  chapter09PullbackVectorBundle p L

noncomputable def chapter09PullbackCompositionIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    Chapter09PullbackModule (f ≫ g) M ≅ Chapter09PullbackModule f (Chapter09PullbackModule g M) :=
  (Scheme.Modules.pullbackComp f g).symm.app M

noncomputable def chapter09PullbackIdentityIso
    {X : Scheme.{u}} (M : X.Modules) :
    Chapter09PullbackModule (𝟙 X) M ≅ M :=
  (Scheme.Modules.pullbackId X).app M

/-! ## Čech nerve and descent data -/

abbrev Chapter09DoubleOverlap {S T : Scheme.{u}} (p : T ⟶ S) :=
  pullback p p

noncomputable def chapter09DoubleFirst
    {S T : Scheme.{u}} (p : T ⟶ S) : Chapter09DoubleOverlap p ⟶ T :=
  pullback.fst p p

noncomputable def chapter09DoubleSecond
    {S T : Scheme.{u}} (p : T ⟶ S) : Chapter09DoubleOverlap p ⟶ T :=
  pullback.snd p p

/-- A chosen triple-overlap part of the Čech nerve of `p`.

The three equations identify the first, second, and third coordinates.  Keeping the maps and
their equations explicit makes the order of the cocycle equation visible to later matrix and
sheaf statements.
-/
structure Chapter09CechNerve {S T : Scheme.{u}} (p : T ⟶ S) where
  triple : Scheme.{u}
  pair12 : triple ⟶ Chapter09DoubleOverlap p
  pair23 : triple ⟶ Chapter09DoubleOverlap p
  pair13 : triple ⟶ Chapter09DoubleOverlap p
  pair12_first : pair12 ≫ chapter09DoubleFirst p = pair13 ≫ chapter09DoubleFirst p
  pair12_second : pair12 ≫ chapter09DoubleSecond p = pair23 ≫ chapter09DoubleFirst p
  pair23_second : pair23 ≫ chapter09DoubleSecond p = pair13 ≫ chapter09DoubleSecond p

/- LOCAL_DEPENDENCY_GUESS: the pinned scheme API does not package the full chosen Čech nerve. -/
theorem chapter09_cech_nerve_exists
    {S T : Scheme.{u}} (p : T ⟶ S) : Nonempty (Chapter09CechNerve p) := by
  sorry

noncomputable def chapter09CanonicalCechNerve
    {S T : Scheme.{u}} (p : T ⟶ S) : Chapter09CechNerve p :=
  Classical.choice (chapter09_cech_nerve_exists p)

/- LOCAL_DEPENDENCY_GUESS: comparison isomorphisms for iterated module-sheaf pullbacks. -/
def chapter09CechCocycleCondition
    {S T : Scheme.{u}} (p : T ⟶ S) (N : Chapter09CechNerve p)
    {M : T.Modules}
    (φ : Chapter09PullbackModule (chapter09DoubleFirst p) M ≅
      Chapter09PullbackModule (chapter09DoubleSecond p) M) : Prop := by
  sorry

/-- A vector-bundle descent datum consists of the object upstairs, its overlap identification, and
the triple-overlap cocycle equation. -/
structure Chapter09ModuleDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) (r : ℕ) where
  nerve : Chapter09CechNerve p
  upstairs : Chapter09VectorBundle T r
  overlapIso :
    Chapter09PullbackModule (chapter09DoubleFirst p) upstairs.carrier ≅
      Chapter09PullbackModule (chapter09DoubleSecond p) upstairs.carrier
  cocycle : chapter09CechCocycleCondition p nerve overlapIso

abbrev Chapter09VectorBundleDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) (r : ℕ) :=
  Chapter09ModuleDescentDatum p r

abbrev Chapter09LineBundleDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) :=
  Chapter09ModuleDescentDatum p 1

/- LOCAL_DEPENDENCY_GUESS: comparison of a descended object with the prescribed overlap datum. -/
def chapter09DescentComparisonCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09VectorBundle S r)
    (e : (chapter09PullbackVectorBundle p E).carrier ≅ D.upstairs.carrier) : Prop := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: compatibility of a morphism with the two overlap pullbacks. -/
def chapter09DescentMorphismCompatible
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s)
    (f : D.upstairs.carrier ⟶ E.upstairs.carrier) : Prop := by
  sorry

/-- An effective descent result, including the comparison with the upstairs object. -/
structure Chapter09VectorBundleDescentResult
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09ModuleDescentDatum p r) where
  downstairs : Chapter09VectorBundle S r
  comparison :
    (chapter09PullbackVectorBundle p downstairs).carrier ≅ D.upstairs.carrier
  compatible : chapter09DescentComparisonCompatible D downstairs comparison

structure Chapter09DescentMorphism
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s) where
  map : D.upstairs.carrier ⟶ E.upstairs.carrier
  compatible : chapter09DescentMorphismCompatible D E map

end
end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09
