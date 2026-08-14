import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17.Section02TheReusableTheoremPackage

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter11
open scoped AlgebraicGeometry TensorProduct

universe u v

/-! ### 17.3 Conclusion -/

/- The following record is the formal “unique global object” conclusion.  The comparison map is
   the returned global object, while full faithfulness supplies uniqueness of every compatible
   map and hence of every compatible structured isomorphism. -/
def CompatibleEffectiveIso
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type v} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {D : F.DescentData f} (A B : EffectiveDescent F f D) :=
  { e : A.descended ≅ B.descended //
      A.comparison.hom ≫ (F.toDescentData f).map e.hom = B.comparison.hom }

theorem effective_descent_unique_up_to_unique_iso
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type v} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {D : F.DescentData f} (A B : EffectiveDescent F f D)
    (hfullyFaithful : IsFullyFaithfulDescent F f) :
    Nonempty (CompatibleEffectiveIso F A B) ∧
      ∀ e₁ e₂ : CompatibleEffectiveIso F A B, e₁ = e₂ := by
  sorry

structure SynthesisConclusion
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type v} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) : Prop where
  effective : IsEffectiveDescent F f
  fullyFaithful : IsFullyFaithfulDescent F f

structure StructuredSynthesisConclusion
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type v} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) : Prop where
  descent : StructuredFpqcDescentPackage F f
  morphismProperties : FpqcMorphismDescentPackage.{u}

/- LOCAL_DEPENDENCY_GUESS: the generic `EffectiveDescent` record in this synthesis chapter and
   Chapter 11's scheme-specific `Effective` record need a canonical fieldwise bridge before this
   packaging theorem can use the earlier scheme theorem without a proof gap. -/
theorem scheme_synthesis_conclusion
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : FpqcMorphism p) :
    SynthesisConclusion
      Chapter11.SchemeDescent.overPseudofunctor (fun _ : PUnit => p) := by
  sorry

theorem scheme_effectivity_has_no_object_finiteness_assumptions
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : FpqcMorphism p) :
    Chapter11.SchemeDescent.IsEffective (fun _ : PUnit => p) := by
  exact Chapter11.SchemeDescent.effective_without_object_finiteness_assumptions p hp

theorem scheme_global_object_is_unique_up_to_unique_iso
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : FpqcMorphism p)
    {D : Chapter11.SchemeDescent.Datum p}
    (A B : Chapter11.SchemeDescent.Effective (fun _ : PUnit => p) D) :
    Nonempty (Chapter11.SchemeDescent.CompatibleIso A B) ∧
      ∀ e₁ e₂ : Chapter11.SchemeDescent.CompatibleIso A B, e₁ = e₂ := by
  exact descended_scheme_unique_up_to_unique_iso p hp A B

/- The concrete diagram declarations in `Dependencies` and the exactness/cocycle theorems in
   Section 1 are the formal version of the final local-to-global mechanism: overlaps compare,
   triples compose, faithful flatness detects equality, flatness transports relations, and finite
   affine reduction keeps the descended geometry finite. -/
theorem synthesis_retains_maps_equations_and_structure
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type v} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    (hF : StructuredFpqcDescentPackage F f) :
    IsEffectiveDescent F f ∧ IsFullyFaithfulDescent F f := by
  exact structured_objects_and_structure_maps_descend F hF

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter17
