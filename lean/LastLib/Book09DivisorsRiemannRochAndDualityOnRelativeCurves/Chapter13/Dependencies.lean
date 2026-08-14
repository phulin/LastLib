import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Section01EvaluationAndGlobalGeneration
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Section02VeryAmplenessAndSeparation
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Section04SerreCriteria
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Section05TensorPowersAndOperations
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Dependencies

/-!
# Book 9, Chapter 13: relative Riemann--Roch and cohomology in families

The pinned Mathlib snapshot supplies scheme pullbacks, module sheaves, scalar
extension, and the canonical absolute cohomology object.  The relative-curve
dimension predicate, determinant line, arithmetic genus, first higher direct
image, and the module structure on fiber cohomology are kept as named
interfaces below because those combinations are not exposed by one earlier
declaration.  Each interface is independent of the conclusion it is used to
prove.
-/

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

noncomputable section

universe u v

/-! ## Elementary numerical predicates -/

/-- A pointwise local-constancy predicate for the invariants of a family. -/
def Chapter13LocallyConstant {α β : Type*} [TopologicalSpace α] (g : α → β) : Prop :=
  ∀ x, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, g y = g x

/-- Upper semicontinuity for a function with values in `ℕ`. -/
def Chapter13UpperSemicontinuous {α : Type*} [TopologicalSpace α]
    (g : α → ℕ) : Prop :=
  ∀ n : ℕ, IsOpen {x | g x < n}

/-- The degree threshold appearing in the smooth-curve vanishing theorem. -/
def chapter13CanonicalDegreeBound (g : ℕ) : ℤ :=
  2 * (g : ℤ) - 2

/-- The degree threshold for global generation on a smooth genus-`g` curve. -/
def chapter13GlobalGenerationDegreeBound (g : ℕ) : ℤ :=
  2 * (g : ℤ)

/-- The degree threshold for very ampleness on a smooth genus-`g` curve. -/
def chapter13VeryAmplenessDegreeBound (g : ℕ) : ℤ :=
  2 * (g : ℤ) + 1

/-! ## Affine one-dimensional fibers -/

/-- An affine chart of Krull dimension one. -/
structure Chapter13AffineDimensionOneChart (Y : Scheme.{u}) where
  U : Y.Opens
  affine : IsAffineOpen U
  A : Type u
  commRingA : CommRing A
  chart : U.toScheme ≅ Spec (.of A)
  dimension_one : ringKrullDim A = 1

/-- A local affine-cover formulation of a one-dimensional scheme. -/
structure Chapter13OneDimensionalScheme (Y : Scheme.{u}) where
  charts : Set (Chapter13AffineDimensionOneChart Y)
  covers : ∀ y : Y, ∃ c, c ∈ charts ∧ y ∈ c.U

/- LOCAL_DEPENDENCY_GUESS: the pinned snapshot has the affine Krull-dimension
primitive but no scheme-level pure-dimensional-one predicate in the form used
by the chapter.  This cover is the weakest local interface needed here. -/

/-- A projective flat relative curve over a locally noetherian base. -/
structure Chapter13RelativeCurve where
  S : Scheme.{u}
  X : Scheme.{u}
  f : X ⟶ S
  base_locally_noetherian : IsLocallyNoetherian S
  projective : chapter04Projective f
  flat : Flat f
  locally_of_finite_presentation : LocallyOfFinitePresentation f
  fiber_is_one_dimensional : ∀ s : S,
    Chapter13OneDimensionalScheme (f.fiber s)

namespace Chapter13RelativeCurve

instance (C : Chapter13RelativeCurve) : IsLocallyNoetherian C.S :=
  C.base_locally_noetherian

instance (C : Chapter13RelativeCurve) : Flat C.f :=
  C.flat

instance (C : Chapter13RelativeCurve) : LocallyOfFinitePresentation C.f :=
  C.locally_of_finite_presentation

end Chapter13RelativeCurve

/-! ## Vector bundles and their canonical pullbacks -/

/-- Constant rank expressed by locally free generators indexed by `Fin r`. -/
def Chapter13HasConstantRank {X : Scheme.{u}} (M : X.Modules) (r : ℕ) : Prop :=
  ∃ q : M.LocalGeneratorsData,
    q.IsLocallyFreeData ∧
      ∀ i : q.I, Nonempty ((q.generators i).I ≃ Fin r)

/-- A finite-rank vector bundle in the module-sheaf presentation. -/
structure Chapter13VectorBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  locally_free : sheaf.IsLocallyFree
  finite_type : sheaf.IsFiniteType
  rank : ℕ
  rank_spec : Chapter13HasConstantRank sheaf rank
  determinant : Chapter04LineBundle X

/-- The canonical restriction of a module sheaf to a scheme-theoretic fiber. -/
def chapter13FiberModule {C : Chapter13RelativeCurve} (M : C.X.Modules)
    (s : C.S) : (C.f.fiber s).Modules :=
  (Scheme.Modules.pullback (C.f.fiberι s)).obj M

/-- The canonical restriction of a line bundle to a scheme-theoretic fiber. -/
noncomputable def chapter13FiberLineBundle {C : Chapter13RelativeCurve}
    (L : Chapter04LineBundle C.X) (s : C.S) :
    Chapter04LineBundle (C.f.fiber s) :=
  chapter04PullbackLineBundle (C.f.fiberι s) L

/-- Pullback preserves the book-facing vector-bundle package. -/
noncomputable def chapter13PullbackVectorBundle {X Y : Scheme.{u}}
    (g : Y ⟶ X) (E : Chapter13VectorBundle X) : Chapter13VectorBundle Y :=
  { sheaf := (Scheme.Modules.pullback g).obj E.sheaf
    locally_free := by sorry
    finite_type := by sorry
    rank := E.rank
    rank_spec := by sorry
    determinant := chapter04PullbackLineBundle g E.determinant }

/-- The vector-bundle restriction to a geometric fiber. -/
noncomputable def chapter13FiberVectorBundle {C : Chapter13RelativeCurve}
    (E : Chapter13VectorBundle C.X) (s : C.S) :
    Chapter13VectorBundle (C.f.fiber s) :=
  chapter13PullbackVectorBundle (C.f.fiberι s) E

/- LOCAL_DEPENDENCY_GUESS: exterior powers of finite locally free module sheaves
are not yet packaged as a determinant-line constructor in the preceding book.
The `determinant` field is the book-facing determinant line and is discharged by
the later determinant reconciliation. -/

/-- The determinant line attached to a vector bundle. -/
noncomputable def chapter13DeterminantLine {X : Scheme.{u}}
    (E : Chapter13VectorBundle X) : Chapter04LineBundle X :=
  E.determinant

/-! ## Base change and canonical fiber cohomology -/

/-- The base-changed total scheme of a family along `T ⟶ S`. -/
def chapter13BaseChangeTotal {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) : Scheme :=
  pullback f g

/-- Projection from a base-changed family to its original total space. -/
abbrev chapter13BaseChangeToSource {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    chapter13BaseChangeTotal f g ⟶ X :=
  pullback.fst f g

/-- Projection from a base-changed family to the test scheme. -/
abbrev chapter13BaseChangeToTest {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    chapter13BaseChangeTotal f g ⟶ T :=
  pullback.snd f g

@[simp, reassoc]
theorem chapter13BaseChange_condition {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    chapter13BaseChangeToSource f g ≫ f = chapter13BaseChangeToTest f g ≫ g :=
  pullback.condition

/-- Pullback of a coefficient sheaf to a base-changed total scheme. -/
def chapter13BaseChangeSheaf {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (M : X.Modules) : (chapter13BaseChangeTotal f g).Modules :=
  (Scheme.Modules.pullback (chapter13BaseChangeToSource f g)).obj M

/-- The base-changed relative-curve structure. -/
noncomputable def chapter13BaseChangedRelativeCurve
    (C : Chapter13RelativeCurve) {T : Scheme} (g : T ⟶ C.S) : Chapter13RelativeCurve :=
  { S := T
    X := chapter13BaseChangeTotal C.f g
    f := chapter13BaseChangeToTest C.f g
    base_locally_noetherian := by sorry
    projective := by sorry
    flat := by sorry
    locally_of_finite_presentation := by sorry
    fiber_is_one_dimensional := by sorry }

/-- The pullback of a vector bundle to a base-changed relative curve. -/
noncomputable def chapter13BaseChangedVectorBundle
    (C : Chapter13RelativeCurve) (E : Chapter13VectorBundle C.X)
    {T : Scheme} (g : T ⟶ C.S) :
    Chapter13VectorBundle (chapter13BaseChangeTotal C.f g) :=
  chapter13PullbackVectorBundle (chapter13BaseChangeToSource C.f g) E

/-- The fiber of a base-changed family over a point of the test scheme. -/
def chapter13BaseChangedFiberToSource {X S T : Scheme.{u}} (f : X ⟶ S)
    (g : T ⟶ S) (t : T) : ((chapter13BaseChangeTotal f g).fiber t) ⟶ X :=
  (chapter13BaseChangeTotal f g).fiberι t ≫ chapter13BaseChangeToSource f g

/-- Canonical cohomology of a pulled-back coefficient sheaf. -/
noncomputable def chapter13BaseChangeCohomology {C : Chapter13RelativeCurve}
    (E : Chapter13VectorBundle C.X) {T : Scheme.{u}} (g : T ⟶ C.S)
    (i : ℕ) : AddCommGrpCat.{u + 1} :=
  chapter04Cohomology (chapter13BaseChangeSheaf C.f g E.sheaf) i

/-- Cohomology of the actual fiber, using the canonical fiber morphism. -/
noncomputable def chapter13FiberCohomology {C : Chapter13RelativeCurve}
    (E : Chapter13VectorBundle C.X) (s : C.S) (i : ℕ) : AddCommGrpCat.{u + 1} :=
  chapter04Cohomology (chapter13FiberModule E.sheaf s) i

/-- The pushforward sheaf occurring in degree zero. -/
noncomputable def chapter13Pushforward {C : Chapter13RelativeCurve}
    (E : Chapter13VectorBundle C.X) : C.S.Modules :=
  (Scheme.Modules.pushforward C.f).obj E.sheaf

/-- Pushforward of an arbitrary module sheaf on the relative curve. -/
noncomputable def chapter13PushforwardModule {C : Chapter13RelativeCurve}
    (M : C.X.Modules) : C.S.Modules :=
  (Scheme.Modules.pushforward C.f).obj M

/-! ## Affine charts and scalar extension -/

/-- An affine chart `U = Spec A` on the base. -/
structure Chapter13AffineBase (C : Chapter13RelativeCurve) where
  U : C.S.Opens
  A : Type u
  commRingA : CommRing A
  chart : U.toScheme ≅ Spec (.of A)

/-- An arbitrary algebra over a fixed affine coordinate ring. -/
structure Chapter13AAlgebra (A : Type u) [CommRing A] where
  B : Type u
  commRingB : CommRing B
  algebraAB : Algebra A B

/-- The structure morphism from an affine test scheme to the base. -/
def Chapter13AffineBase.mapToBase {C : Chapter13RelativeCurve}
    (U : Chapter13AffineBase C) (B : Chapter13AAlgebra U.A) :
    Spec (.of B.B) ⟶ C.S := by
  letI := U.commRingA
  letI := B.commRingB
  letI := B.algebraAB
  exact Scheme.Spec.map (CommRingCat.ofHom (algebraMap U.A B.B)).op ≫
      U.chart.inv.hom ≫ U.U.ι

/-- Extension of scalars in the category of modules. -/
def chapter13ExtendScalars {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B :=
  ModuleCat.extendScalars φ

/-- A finite free module with its rank and a chosen finite basis type. -/
structure Chapter13FiniteFreeModule (A : Type u) [CommRing A] where
  carrier : ModuleCat.{u} A
  finite : Module.Finite A (carrier : Type u)
  free : Module.Free A (carrier : Type u)
  rank : ℕ
  basis : Nonempty (carrier ≅ ModuleCat.of A (Fin rank →₀ A))

namespace Chapter13FiniteFreeModule

/-- Scalar extension of a finite free module. -/
noncomputable def baseChange {A : Type u} [CommRing A]
    (M : Chapter13FiniteFreeModule A) (B : Chapter13AAlgebra A) :
    Chapter13FiniteFreeModule B.B := by
  letI := B.commRingB
  letI := B.algebraAB
  refine
    { carrier := (ModuleCat.extendScalars (algebraMap A B.B)).obj M.carrier
      finite := by infer_instance
      free := by infer_instance
      rank := M.rank
      basis := ?_ }
  sorry

end Chapter13FiniteFreeModule

/-- A finite free two-term complex over an affine base ring. -/
structure Chapter13TwoTermModel (A : Type u) [CommRing A] where
  K0 : Chapter13FiniteFreeModule A
  K1 : Chapter13FiniteFreeModule A
  d : K0.carrier ⟶ K1.carrier

namespace Chapter13TwoTermModel

/-- Base change of the matrix `K⁰ ⟶ K¹`. -/
noncomputable def baseChange {A : Type u} [CommRing A]
    (M : Chapter13TwoTermModel A) (B : Chapter13AAlgebra A) :
    Chapter13TwoTermModel B.B := by
  letI := B.commRingB
  letI := B.algebraAB
  exact
    { K0 := M.K0.baseChange B
      K1 := M.K1.baseChange B
      d := (ModuleCat.extendScalars (algebraMap A B.B)).map M.d }

end Chapter13TwoTermModel

/- The module-category kernel and cokernel are named explicitly so the two-term
model exposes the two cohomology groups without conflating a kernel with a
fiberwise dimension statement. -/

noncomputable def chapter13Kernel {A : Type u} [CommRing A]
    {K0 K1 : ModuleCat.{u} A} (d : K0 ⟶ K1) : ModuleCat.{u} A := by
  letI : HasKernels (ModuleCat A) := ModuleCat.hasKernels_moduleCat
  exact kernel d

noncomputable def chapter13Cokernel {A : Type u} [CommRing A]
    {K0 K1 : ModuleCat.{u} A} (d : K0 ⟶ K1) : ModuleCat.{u} A := by
  letI : HasCokernels (ModuleCat A) := ModuleCat.hasCokernels_moduleCat
  exact cokernel d

abbrev chapter13TwoTermH0 {A : Type u} [CommRing A]
    (d : ModuleCat.{u} A ⟶ ModuleCat.{u} A) : AddCommGrpCat.{u + 1} :=
  (AddCommGrpCat.uliftFunctor.{u, u + 1}).obj
    (AddCommGrpCat.of (chapter13Kernel d : Type u))

abbrev chapter13TwoTermH1 {A : Type u} [CommRing A]
    (d : ModuleCat.{u} A ⟶ ModuleCat.{u} A) : AddCommGrpCat.{u + 1} :=
  (AddCommGrpCat.uliftFunctor.{u, u + 1}).obj
    (AddCommGrpCat.of (chapter13Cokernel d : Type u))

/-! ## Fiber cohomology as finite modules over residue fields -/

/-- A finite residue-field module realizing one canonical fiber cohomology group. -/
structure Chapter13FiberCohomologyModule {C : Chapter13RelativeCurve}
    (M : C.X.Modules) (s : C.S) (i : ℕ) where
  module : ModuleCat.{u} (C.S.residueField s)
  finite : Module.Finite (C.S.residueField s) (module : Type u)
  additive_identification :
    (AddCommGrpCat.uliftFunctor.{u, u + 1}).obj
        (AddCommGrpCat.of (module : Type u)) ≅
      chapter04Cohomology (chapter13FiberModule M s) i

noncomputable def chapter13FiberCohomologyDimension
    {C : Chapter13RelativeCurve} {M : C.X.Modules} {s : C.S} {i : ℕ}
    (H : Chapter13FiberCohomologyModule M s i) : ℕ :=
  Module.finrank (C.S.residueField s) H.module

/- LOCAL_DEPENDENCY_GUESS: the pinned cohomology object is constructed as an
additive group, while the residue-field module structure and its compatibility
with scheme-theoretic base change are not yet bundled. -/

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter13
