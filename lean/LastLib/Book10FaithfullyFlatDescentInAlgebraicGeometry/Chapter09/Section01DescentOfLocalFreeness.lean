import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

/-! ## 9.1 Descent of local freeness -/

/-- Stalkwise flatness of a module sheaf, with the canonical stalk module structure made explicit. -/
def chapter09StalkwiseFlat {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X,
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := by
      change Module (X.presheaf.stalk x) (↑(TopCat.Presheaf.stalk M.val.presheaf x))
      exact
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) M.val x
    Module.Flat (X.presheaf.stalk x) (M.presheaf.stalk x)

/-- The direct local-freeness criterion used in the chapter: a quasicoherent sheaf that is of
finite presentation and flat, after a faithfully flat cover on which the fixed finite rank is
locally free. -/
theorem chapter09_finite_locally_free_of_faithfully_flat_pullback
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    {M : S.Modules} (r : ℕ)
    (hqc : M.IsQuasicoherent)
    (hfp : M.IsFinitePresentation)
    (hflat : chapter09StalkwiseFlat M)
    (hupstairs : chapter09FiniteLocallyFreeOfRank
      (Chapter09PullbackModule p M) r) :
    chapter09FiniteLocallyFreeOfRank M r := by
  sorry

/-- Pullback of a finite locally free sheaf has the same constant rank. -/
theorem chapter09_pullback_preserves_finite_locally_free_rank
    {S T : Scheme.{u}} (p : T ⟶ S) {M : S.Modules} {r : ℕ}
    (hM : chapter09FiniteLocallyFreeOfRank M r) :
    chapter09FiniteLocallyFreeOfRank (Chapter09PullbackModule p M) r := by
  sorry

/-- A finite locally free rank condition is detected after a faithfully flat base change. -/
theorem chapter09_finite_locally_free_iff_of_fpqc
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    {M : S.Modules} {r : ℕ}
    (hqc : M.IsQuasicoherent)
    (hfp : M.IsFinitePresentation)
    (hflat : chapter09StalkwiseFlat M) :
    chapter09FiniteLocallyFreeOfRank M r ↔
      chapter09FiniteLocallyFreeOfRank (Chapter09PullbackModule p M) r := by
  constructor
  · exact chapter09_pullback_preserves_finite_locally_free_rank p
  · exact chapter09_finite_locally_free_of_faithfully_flat_pullback p hp r hqc hfp hflat

/- LOCAL_DEPENDENCY_GUESS: effective fpqc descent for module sheaves with the explicit Čech
   comparison fields from Dependencies.lean. -/
theorem chapter09_vector_bundle_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    {r : ℕ} (D : Chapter09VectorBundleDescentDatum p r) :
    Nonempty (Chapter09VectorBundleDescentResult D) := by
  sorry

/-! The rank-one instance is named separately so later sections can depend on the line-bundle
statement without unfolding the abbreviation. -/
theorem chapter09_line_bundle_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    (D : Chapter09LineBundleDescentDatum p) :
    Nonempty (Chapter09VectorBundleDescentResult D) := by
  exact chapter09_vector_bundle_effective_fpqc_descent p hp D

def chapter09DescendedMorphismMatches
    {S T : Scheme.{u}} {p : T ⟶ S} {r s : ℕ}
    (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s)
    (RD : Chapter09VectorBundleDescentResult D)
    (RE : Chapter09VectorBundleDescentResult E)
    (f : D.upstairs.carrier ⟶ E.upstairs.carrier)
    (f₀ : RD.downstairs.carrier ⟶ RE.downstairs.carrier) : Prop := by
  exact
    (Scheme.Modules.pullback p).map f₀ ≫ RE.comparison.hom =
      RD.comparison.hom ≫ f

/-- Compatible morphisms of vector bundles descend uniquely after the descended objects are fixed. -/
theorem chapter09_vector_bundle_morphism_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    {r s : ℕ} (D : Chapter09ModuleDescentDatum p r)
    (E : Chapter09ModuleDescentDatum p s)
    (RD : Chapter09VectorBundleDescentResult D)
    (RE : Chapter09VectorBundleDescentResult E)
    (f : D.upstairs.carrier ⟶ E.upstairs.carrier)
    (hf : chapter09DescentMorphismCompatible D E f) :
    ∃! f₀ : RD.downstairs.carrier ⟶ RE.downstairs.carrier,
      chapter09DescendedMorphismMatches D E RD RE f f₀ := by
  sorry

/- Effective descent is unique up to the unique isomorphism whose pullback
   identifies the two comparison isomorphisms. -/
theorem chapter09_vector_bundle_descent_result_unique
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p)
    {r : ℕ} (D : Chapter09ModuleDescentDatum p r)
    (R R' : Chapter09VectorBundleDescentResult D) :
    ∃! e : R.downstairs.carrier ≅ R'.downstairs.carrier,
      chapter09DescentResultsIsoCompatible R R' e := by
  sorry

/-- Effective fpqc descent applies simultaneously to vector bundles, line bundles, and their
morphisms. -/
def chapter09EffectiveFpqcDescentForVectorBundles
    {S T : Scheme.{u}} (p : T ⟶ S) (_hp : Chapter09FpqcCover p) : Prop :=
  (∀ (r : ℕ) (D : Chapter09VectorBundleDescentDatum p r),
      Nonempty (Chapter09VectorBundleDescentResult D)) ∧
    (∀ (r s : ℕ) (D : Chapter09ModuleDescentDatum p r)
      (E : Chapter09ModuleDescentDatum p s)
      (RD : Chapter09VectorBundleDescentResult D)
      (RE : Chapter09VectorBundleDescentResult E)
      (f : D.upstairs.carrier ⟶ E.upstairs.carrier),
      chapter09DescentMorphismCompatible D E f →
        ∃! f₀ : RD.downstairs.carrier ⟶ RE.downstairs.carrier,
          chapter09DescendedMorphismMatches D E RD RE f f₀) ∧
    (∀ (r : ℕ) (D : Chapter09VectorBundleDescentDatum p r)
      (R R' : Chapter09VectorBundleDescentResult D),
      ∃! e : R.downstairs.carrier ≅ R'.downstairs.carrier,
        chapter09DescentResultsIsoCompatible R R' e)

theorem chapter09_effective_fpqc_descent_for_vector_bundles
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter09FpqcCover p) :
    chapter09EffectiveFpqcDescentForVectorBundles p hp := by
  constructor
  · intro r D
    exact chapter09_vector_bundle_effective_fpqc_descent p hp D
  · constructor
    · intro r s D E RD RE f hf
      exact chapter09_vector_bundle_morphism_descends p hp D E RD RE f hf
    · intro r D R R'
      exact chapter09_vector_bundle_descent_result_unique p hp D R R'

end
end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09
