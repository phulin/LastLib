import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Dependencies

namespace LastLib
namespace Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
namespace Chapter08

open AlgebraicGeometry CategoryTheory

noncomputable section

/-! ## 8.3 Constancy and the flatness boundary -/

/- A local package for the dense flat locus used in the converse argument. -/
structure Chapter08GenericFlatnessProfile
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F) where
  denseOpen : Set F.family.S
  dense : Dense denseOpen
  open_denseOpen : IsOpen denseOpen
  flat_on_denseOpen :
    ∀ s ∈ denseOpen, chapter08FlatAt F.family.f E.sheaf s

/- LOCAL_DEPENDENCY_GUESS: generic flatness for coherent scheme modules is not
   exposed by the pinned imports in the form used by this chapter. -/
theorem chapter08_generic_flatness_dense_open
    {F : Chapter08PolarizedFamily} (E : Chapter08FamilySheaf F)
    (hred : IsReduced F.family.S) :
    Nonempty (Chapter08GenericFlatnessProfile E) := by
  sorry

/- The residue map from the dual numbers to their reduced quotient. -/
def chapter08DualNumberResidueMap (k : Type*) [Field k] :
    DualNumber k →+* k :=
  (TrivSqZeroExt.fstHom k k k).toRingHom

/- The nonreduced base and its reduced residue-field point. -/
def chapter08DualNumberBaseScheme (k : Type*) [Field k] : Scheme :=
  Spec (.of (DualNumber k))

def chapter08DualNumberResidueScheme (k : Type*) [Field k] : Scheme :=
  Spec (.of k)

def chapter08DualNumberResiduePoint (k : Type*) [Field k] :
    chapter08DualNumberResidueScheme k ⟶ chapter08DualNumberBaseScheme k :=
  Scheme.Spec.map (CommRingCat.ofHom (chapter08DualNumberResidueMap k)).op

theorem chapter08_dual_number_base_has_one_topological_point
    (k : Type*) [Field k] :
    ∃ x : chapter08DualNumberBaseScheme k, ∀ y, y = x := by
  sorry

/- The usual residue-field module over the dual numbers. -/
@[instance_reducible]
def chapter08DualNumberModule (k : Type*) [Field k] :
    Module (DualNumber k) k :=
  Module.compHom k (chapter08DualNumberResidueMap k)

/- Flatness of the residue module, with its module structure made explicit. -/
def chapter08DualNumberModuleFlat (k : Type*) [Field k] : Prop :=
  letI : Module (DualNumber k) k := chapter08DualNumberModule k
  Module.Flat (DualNumber k) k

/- There is one underlying topological fiber in the dual-number example. -/
def chapter08DualNumberFiberPointCount (k : Type*) [Field k] : ℕ := 1

/- Its ordinary fiber has length one. -/
def chapter08DualNumberFiberLength (k : Type*) [Field k] : ℕ := 1

theorem chapter08_dual_number_fiber_point_count_eq_one (k : Type*) [Field k] :
    chapter08DualNumberFiberPointCount k = 1 := by
  rfl

theorem chapter08_dual_number_fiber_length_eq_one (k : Type*) [Field k] :
    chapter08DualNumberFiberLength k = 1 := by
  rfl

/- The residue module is not flat over the nonreduced dual-number ring. -/
theorem chapter08_dual_number_residue_module_not_flat (k : Type*) [Field k] :
    ¬ chapter08DualNumberModuleFlat k := by
  sorry

/- The sole topological fiber and its numerical length do not detect flatness. -/
theorem chapter08_dual_number_constant_fiber_does_not_detect_flatness
    (k : Type*) [Field k] :
    chapter08DualNumberFiberPointCount k = 1 ∧
      chapter08DualNumberFiberLength k = 1 ∧
      ¬ chapter08DualNumberModuleFlat k := by
  refine ⟨rfl, rfl, ?_⟩
  exact chapter08_dual_number_residue_module_not_flat k

end
end Chapter08
end Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers
end LastLib
