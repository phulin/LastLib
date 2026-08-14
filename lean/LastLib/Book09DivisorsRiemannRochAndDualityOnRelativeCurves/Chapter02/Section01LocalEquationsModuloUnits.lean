import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

universe u v

/-!
### 2.1 Local equations modulo units
-/

def chapter02CartierDivisor.zero {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] : Chapter02CartierDivisor X where
  index := PUnit
  openSet _ := ⊤
  cover := by simp
  equation _ := 1
  equationClass _ := Quotient.mk' 1
  equationClass_eq _ := rfl
  transition _ _ := by
    refine ⟨1, ?_⟩
    simp

noncomputable def chapter02CartierDivisor.neg {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) :
    Chapter02CartierDivisor X where
  index := D.index
  openSet := D.openSet
  cover := D.cover
  equation i := (D.equation i)⁻¹
  equationClass i := Quotient.mk' ((D.equation i)⁻¹)
  equationClass_eq i := rfl
  transition := by sorry

noncomputable def chapter02CartierDivisor.add {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D E : Chapter02CartierDivisor X) :
    Chapter02CartierDivisor X where
  index := D.index × E.index
  openSet p := D.openSet p.1 ⊓ E.openSet p.2
  cover := by sorry
  equation p :=
    chapter02MeromorphicRestrictionUnit X inf_le_left (D.equation p.1) *
      chapter02MeromorphicRestrictionUnit X inf_le_right (E.equation p.2)
  equationClass p := Quotient.mk'
    (chapter02MeromorphicRestrictionUnit X inf_le_left (D.equation p.1) *
      chapter02MeromorphicRestrictionUnit X inf_le_right (E.equation p.2))
  equationClass_eq p := rfl
  transition := by sorry

@[simp]
theorem chapter02_cartier_zero_equation {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] :
    (chapter02CartierDivisor.zero (X := X)).equation PUnit.unit = 1 := rfl

theorem chapter02_cartier_zero_is_zero {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] :
    (chapter02CartierDivisor.zero (X := X)).IsZero := by
  intro i
  refine ⟨1, ?_⟩
  simp [chapter02CartierDivisor.zero]

theorem chapter02_cartier_neg_equation {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) (i : D.index) :
    (D.neg.equation i : Chapter02MeromorphicSection X (D.openSet i)) =
      (D.equation i : Chapter02MeromorphicSection X (D.openSet i))⁻¹ := by
  rfl

theorem chapter02_cartier_add_equation {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D E : Chapter02CartierDivisor X)
    (i : D.index) (j : E.index) :
    (D.add E).equation (i, j) =
      chapter02MeromorphicRestrictionUnit X inf_le_left (D.equation i) *
        chapter02MeromorphicRestrictionUnit X inf_le_right (E.equation j) := by
  rfl

def chapter02CartierDivisor.IsEffective {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) : Prop :=
  ∀ i, ∃ f : Γ(X, D.openSet i),
    f ∈ nonZeroDivisors (Γ(X, D.openSet i)) ∧
      chapter02RegularSectionMap X (D.openSet i) f = D.equation i

def chapter02CartierDivisor.IsZero {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) : Prop :=
  ∀ i, ∃ u : (Γ(X, D.openSet i))ˣ,
    chapter02RegularUnitMap X (D.openSet i) u = D.equation i

def chapter02CartierDivisor.HasSignedDecomposition {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) : Prop :=
  ∃ E F : Chapter02CartierDivisor X,
    E.IsEffective ∧ F.IsEffective ∧ D = E.add F.neg

def chapter02CartierDivisor.support {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (D : Chapter02CartierDivisor X) : Set X :=
  {x | ∀ i (hx : x ∈ D.openSet i),
    ¬ IsUnit ((K.carrier.presheaf.germ (D.openSet i) x hx).hom (D.equation i))}

theorem chapter02_cartier_support_closed {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] [IsNoetherian X]
    (D : Chapter02CartierDivisor X) :
    IsClosed D.support := by
  sorry

theorem chapter02_cartier_support_omits_generic_point {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] [IsNoetherian X] [IsIntegral X]
    (D : Chapter02CartierDivisor X) :
    genericPoint X ∉ D.support := by
  sorry

theorem chapter02_regular_element_iff_injective_multiplication
    (R : Type u) [CommRing R] (f : R) :
    f ∈ nonZeroDivisors R ↔ Function.Injective (fun x : R => f * x) := by
  sorry

theorem chapter02_nonzero_divisor_not_component
    (R : Type u) [CommRing R] (f : R)
    (hf : f ∈ nonZeroDivisors R) :
    ∀ x : R, f * x = 0 → x = 0 := by
  intro x hx
  exact (chapter02_regular_element_iff_injective_multiplication R f).mp hf
    (by simpa using hx)

/- The following are book-facing descriptions of the two standard total
   quotient-ring special cases.  The actual sheaf-level comparison is left as
   a reusable interface because it is not in the pinned Mathlib API. -/
def Chapter02MeromorphicSheaf.IsConstantOnNonemptyOpens {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] [IsIntegral X] : Prop :=
  ∀ U : X.Opens, U.Nonempty →
    Nonempty (Chapter02MeromorphicSection X U ≃+* X.functionField)

theorem chapter02_total_quotient_constant_on_integral_scheme
    (X : Scheme.{u}) [K : Chapter02MeromorphicSheaf X]
    [IsIntegral X] [IsLocallyNoetherian X] :
    Chapter02MeromorphicSheaf.IsConstantOnNonemptyOpens (X := X) := by
  sorry

def Chapter02MeromorphicSheaf.IsFiniteProductOfFunctionFields {X : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (ι : Type u) (F : ι → Type u)
    [∀ i, Field (F i)] : Prop :=
  ∀ U : X.Opens, U.Nonempty →
    Nonempty (Chapter02MeromorphicSection X U ≃+* (∀ i, F i))

theorem chapter02_irreducible_components_finite
    (X : Scheme.{u}) [IsNoetherian X] :
    (irreducibleComponents X).Finite :=
  finite_irreducibleComponents_of_isNoetherian

/- LOCAL_DEPENDENCY_GUESS: the pinned API does not yet expose the function
   field attached to each irreducible component or the comparison with the
   total quotient sheaf.  Package those canonical component fields together
   with the comparison instead of allowing an arbitrary family of fields. -/
structure Chapter02FiniteComponentFunctionFieldData
    (X : Scheme.{u}) [K : Chapter02MeromorphicSheaf X]
    [IsReduced X] [IsLocallyNoetherian X]
    [Finite (irreducibleComponents X)] where
  field : irreducibleComponents X → Type u
  field_isField : ∀ i, Field (field i)
  product : @Chapter02MeromorphicSheaf.IsFiniteProductOfFunctionFields X K
    (irreducibleComponents X) field field_isField

theorem chapter02_total_quotient_product_of_reduced_finite_components
    (X : Scheme.{u}) [K : Chapter02MeromorphicSheaf X] [IsReduced X]
    [IsLocallyNoetherian X] [Finite (irreducibleComponents X)] :
    Nonempty (Chapter02FiniteComponentFunctionFieldData X) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02
