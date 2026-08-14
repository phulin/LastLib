import Mathlib.LinearAlgebra.TensorProduct.Basic
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09.Section02TransitionMatricesAndCocycles
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09.Section03DeterminantsSectionsAndForms

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct

universe u v

/-! ## 9.4 Why local triviality is not descent data -/

/- LOCAL_DEPENDENCY_GUESS: the finite direct sum of copies of the structure sheaf is not exposed
as a single named module-sheaf constructor in the pinned API. -/
noncomputable def chapter09TrivialRankModule
    (X : Scheme.{u}) (r : ℕ) : X.Modules := by
  sorry

structure Chapter09VectorBundleTrivialization
    {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r) where
  basis : E.carrier ≅ chapter09TrivialRankModule X r

/-- The information that a rank-`r` vector bundle is trivial after the cover, without any overlap
identification. -/
def chapter09LocalTrivialityOnly
    {S T : Scheme.{u}} (p : T ⟶ S) (r : ℕ) : Prop :=
  ∃ E : Chapter09VectorBundle T r, Nonempty (Chapter09VectorBundleTrivialization E)

/-- A trivialized object together with the missing overlap identification and cocycle. -/
structure Chapter09TrivializedDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) (r : ℕ) where
  descent : Chapter09ModuleDescentDatum p r
  trivialization : Chapter09VectorBundleTrivialization descent.upstairs

theorem chapter09_descent_data_forgets_to_local_triviality
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09TrivializedDescentDatum p r) :
    chapter09LocalTrivialityOnly p r := by
  exact ⟨D.descent.upstairs, ⟨D.trivialization⟩⟩

theorem chapter09_descent_data_includes_overlap_identification
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09TrivializedDescentDatum p r) :
    Nonempty
      (Chapter09PullbackModule (chapter09DoubleFirst p) D.descent.upstairs.carrier ≅
        Chapter09PullbackModule (chapter09DoubleSecond p) D.descent.upstairs.carrier) := by
  exact ⟨D.descent.overlapIso⟩

/-! ### Forms over a field extension -/

structure Chapter09FieldExtensionForm
    (K L V W : Type*) [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module K W] where
  comparison : Nonempty (L ⊗[K] W ≃ₗ[L] V)

def chapter09FieldExtensionVectorSpaceHasKForm
    (K L V : Type*) [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module L V] : Prop :=
  ∃ (W : Type v) (instW : AddCommGroup W) (moduleW : Module K W),
    Nonempty (@Chapter09FieldExtensionForm K L V W _ _ _ _ _ instW moduleW)

theorem chapter09_field_extension_vector_space_has_a_form
    (K L V : Type*) [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module L V] [Module.Finite L V] :
    chapter09FieldExtensionVectorSpaceHasKForm K L V := by
  sorry

/-! The existence statement above has no chosen witness.  A chosen form is additional data, just
as an overlap isomorphism is additional data in `Chapter09TrivializedDescentDatum`. -/
structure Chapter09SelectedFieldExtensionForm
    (K L V W : Type*) [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module K W] where
  form : Chapter09FieldExtensionForm K L V W

def chapter09AdditionalTensorDescentObstruction (compatibleTensor : Prop) : Prop :=
  ¬ compatibleTensor

/-! ### Ample line bundles and the missing cocycle -/

/- LOCAL_DEPENDENCY_GUESS: the earlier ample-line-bundle API is relative and does not expose the
absolute predicate in the form needed by this warning. -/
def chapter09AmpleLineBundle {X : Scheme.{u}} (L : Chapter09LineBundle X) : Prop := by
  sorry

def chapter09LineBundleDescends
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T) : Prop :=
  ∃ L₀ : Chapter09LineBundle S,
    Nonempty ((chapter09PullbackLineBundle p L₀).carrier ≅ L.carrier)

def chapter09LineBundleCarriesCocycle
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T) : Prop :=
  ∃ D : Chapter09LineBundleDescentDatum p, Nonempty (D.upstairs.carrier ≅ L.carrier)

theorem chapter09_line_bundle_descent_requires_cocycle
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T)
    (hL : chapter09LineBundleDescends p L) :
    chapter09LineBundleCarriesCocycle p L := by
  sorry

theorem chapter09_ample_line_bundle_descent_requires_cocycle
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T)
    (hample : chapter09AmpleLineBundle L)
    (hL : chapter09LineBundleDescends p L) :
    chapter09LineBundleCarriesCocycle p L := by
  exact chapter09_line_bundle_descent_requires_cocycle p L hL

def chapter09UnitTripleDefect
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (u : Dˣ) : Prop :=
  Units.map N.pair23.toMonoidHom u * Units.map N.pair12.toMonoidHom u ≠
    Units.map N.pair13.toMonoidHom u

theorem chapter09_unit_triple_defect_is_exact_cocycle_failure
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (u : Dˣ) :
    chapter09UnitTripleDefect N u ↔
      ¬ chapter09UnitCocycleCondition N u := by
  rfl

/-! ### Polarized descent and descendable powers or norms -/

structure Chapter09PolarizedDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) (r : ℕ) where
  vectorBundleDatum : Chapter09ModuleDescentDatum p r
  lineBundleDatum : Chapter09LineBundleDescentDatum p

theorem chapter09_polarized_descent_includes_line_bundle_datum
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09PolarizedDescentDatum p r) :
    Nonempty (Chapter09LineBundleDescentDatum p) := by
  exact ⟨D.lineBundleDatum⟩

/- LOCAL_DEPENDENCY_GUESS: a norm construction for line bundles is not packaged in the pinned
descent API; the declaration isolates it from the power alternative. -/
noncomputable def chapter09LineBundleNorm
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T) : Chapter09LineBundle S := by
  sorry

def chapter09DescendablePowerOrNorm
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T) : Prop :=
  (∃ n : ℕ, 0 < n ∧ ∃ L₀ : Chapter09LineBundle S,
    Nonempty ((chapter09PullbackLineBundle p L₀).carrier ≅
      (chapter09LineBundleTensorPower L n).carrier)) ∨
    Nonempty ((chapter09PullbackLineBundle p (chapter09LineBundleNorm p L)).carrier ≅ L.carrier)

theorem chapter09_polarized_descent_datum_carries_line_cocycle
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09PolarizedDescentDatum p r) :
    chapter09LineBundleCarriesCocycle p D.lineBundleDatum.upstairs := by
  exact ⟨D.lineBundleDatum, ⟨Iso.refl _⟩⟩

end
end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09
