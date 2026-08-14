import Mathlib.LinearAlgebra.TensorProduct.Basic
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09.Section01DescentOfLocalFreeness
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09.Section02TransitionMatricesAndCocycles
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09.Section03DeterminantsSectionsAndForms

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct

universe u v uK uL uV

/-! ## 9.4 Why local triviality is not descent data -/

/- The free module sheaf on `Fin r` is the finite direct sum of `r` copies of
the structure sheaf, so it is the canonical trivial rank-`r` carrier. -/
noncomputable def chapter09TrivialRankModule
    (X : Scheme.{u}) (r : ℕ) : X.Modules := by
  exact SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))

structure Chapter09VectorBundleTrivialization
    {X : Scheme.{u}} {r : ℕ} (E : Chapter09VectorBundle X r) where
  basis : E.carrier ≅ chapter09TrivialRankModule X r

/-- The information that a rank-`r` vector bundle is trivial after the cover, without any overlap
identification. -/
def chapter09LocalTrivialityOnly
    {S T : Scheme.{u}} (_p : T ⟶ S) {r : ℕ} (E : Chapter09VectorBundle T r) : Prop :=
  Nonempty (Chapter09VectorBundleTrivialization E)

/-- A trivialized object together with the missing overlap identification and cocycle. -/
structure Chapter09TrivializedDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) (r : ℕ) where
  descent : Chapter09ModuleDescentDatum p r
  trivialization : Chapter09VectorBundleTrivialization descent.upstairs

theorem chapter09_descent_data_forgets_to_local_triviality
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09TrivializedDescentDatum p r) :
    chapter09LocalTrivialityOnly p D.descent.upstairs := by
  exact ⟨D.trivialization⟩

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
  comparison : L ⊗[K] W ≃ₗ[L] V

def chapter09FieldExtensionVectorSpaceHasKForm
    (K : Type uK) (L : Type uL) (V : Type uV) [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module L V] : Prop :=
  ∃ (W : Type uK) (instW : AddCommGroup W) (moduleW : Module K W),
    Nonempty (@Chapter09FieldExtensionForm K L V W _ _ _ _ _ instW moduleW)

theorem chapter09_field_extension_vector_space_has_a_form
    (K : Type uK) (L : Type uL) (V : Type uV) [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module L V] [Module.Finite L V] :
    chapter09FieldExtensionVectorSpaceHasKForm K L V := by
  let n := Module.finrank L V
  let W : Type uK := Fin n → K
  let bV : Module.Basis (Fin n) L V := Module.finBasis L V
  let bW : Module.Basis (Fin n) K W := Pi.basisFun K (Fin n)
  refine ⟨W, inferInstance, inferInstance, ?_⟩
  exact ⟨{ comparison :=
    ((Algebra.TensorProduct.basis L bW).equivFun).trans bV.equivFun.symm }⟩

/-! The existence statement above has no chosen witness.  A chosen form is additional data, just
as an overlap isomorphism is additional data in `Chapter09TrivializedDescentDatum`. -/
structure Chapter09SelectedFieldExtensionForm
    (K L V W : Type*) [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module K W] where
  form : Chapter09FieldExtensionForm K L V W

/-! ### Ample line bundles and the missing cocycle -/

/- Absolute ampleness is relative ampleness for the identity morphism.  The carrier adapter is
kept in `Dependencies.lean` so all later positivity statements use the same rank-one object. -/
def chapter09AmpleLineBundle {X : Scheme.{u}} (L : Chapter09LineBundle X) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04Ample
    (𝟙 X) (chapter09AsChapter04LineBundle L)

def chapter09LineBundleDescends
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T) : Prop :=
  ∃ L₀ : Chapter09LineBundle S,
    Nonempty ((chapter09PullbackLineBundle p L₀).carrier ≅ L.carrier)

/- A cocycle is data on the actual line bundle upstairs, not merely an
   isomorphism of its carrier with the upstairs object of another datum. -/
structure Chapter09LineBundleCocycle
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T) where
  nerve : Chapter09CechNerve p
  overlapIso :
    Chapter09PullbackModule (chapter09DoubleFirst p) L.carrier ≅
      Chapter09PullbackModule (chapter09DoubleSecond p) L.carrier
  cocycle : chapter09CechCocycleCondition p nerve overlapIso

def chapter09LineBundleCarriesCocycle
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T) : Prop :=
  Nonempty (Chapter09LineBundleCocycle p L)

theorem chapter09_line_bundle_descent_requires_cocycle
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T)
    (hL : chapter09LineBundleDescends p L) :
    chapter09LineBundleCarriesCocycle p L := by
  sorry

theorem chapter09_ample_line_bundle_descent_requires_cocycle
    {S T : Scheme.{u}} (p : T ⟶ S) (L : Chapter09LineBundle T)
    (_hample : chapter09AmpleLineBundle L)
    (hL : chapter09LineBundleDescends p L) :
    chapter09LineBundleCarriesCocycle p L := by
  exact chapter09_line_bundle_descent_requires_cocycle p L hL

theorem chapter09_line_bundle_descends_of_cocycle
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    (L : Chapter09LineBundle T) (D : Chapter09LineBundleCocycle p L) :
    chapter09LineBundleDescends p L := by
  let MD : Chapter09LineBundleDescentDatum p :=
    { nerve := D.nerve
      upstairs := L
      overlapIso := D.overlapIso
      cocycle := D.cocycle }
  let R : Chapter09VectorBundleDescentResult MD :=
    Classical.choice (chapter09_line_bundle_effective_fpqc_descent p hp MD)
  exact ⟨R.downstairs, ⟨R.comparison⟩⟩

theorem chapter09_line_bundle_descends_iff_cocycle
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    (L : Chapter09LineBundle T) :
    chapter09LineBundleDescends p L ↔ chapter09LineBundleCarriesCocycle p L := by
  constructor
  · exact chapter09_line_bundle_descent_requires_cocycle p L
  · rintro ⟨D⟩
    exact chapter09_line_bundle_descends_of_cocycle p hp L D

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

/-! ### Polarized descent data -/

structure Chapter09PolarizedDescentDatum
    {S T : Scheme.{u}} (p : T ⟶ S) (r : ℕ) where
  vectorBundleDatum : Chapter09ModuleDescentDatum p r
  lineBundleDatum : Chapter09LineBundleDescentDatum p
  ample : chapter09AmpleLineBundle lineBundleDatum.upstairs

theorem chapter09_polarized_descent_includes_line_bundle_datum
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09PolarizedDescentDatum p r) :
    Nonempty (Chapter09LineBundleDescentDatum p) := by
  exact ⟨D.lineBundleDatum⟩

theorem chapter09_polarized_descent_datum_carries_line_cocycle
    {S T : Scheme.{u}} {p : T ⟶ S} {r : ℕ}
    (D : Chapter09PolarizedDescentDatum p r) :
    chapter09LineBundleCarriesCocycle p D.lineBundleDatum.upstairs := by
  exact ⟨{
    nerve := D.lineBundleDatum.nerve
    overlapIso := D.lineBundleDatum.overlapIso
    cocycle := D.lineBundleDatum.cocycle
  }⟩

end
end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09
