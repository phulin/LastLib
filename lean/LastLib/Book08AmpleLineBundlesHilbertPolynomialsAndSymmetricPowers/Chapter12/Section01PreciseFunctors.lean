import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

/-! ## 12.1. Precise functors -/

/-- The Hilbert functor with fixed fiber Hilbert polynomial. -/
def chapter12HilbertFunctor
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial) :
    (Chapter12SchemeOver D.base)ᵒᵖ ⥤ Type _ where
  obj T := Chapter12HilbertFamily D H T.unop P
  map := fun {T U} (g : T ⟶ U) =>
    TypeCat.ofHom (fun (Z : Chapter12HilbertFamily D H T.unop P) =>
      chapter12PullbackFamily D H (P := P) g.unop Z)
  map_id := by
    intro X
    ext Z
    simpa using chapter12PullbackFamily_id D H Z
  map_comp := by
    intro X Y Z f g
    ext Z
    change chapter12PullbackFamily D H ((f ≫ g).unop) Z =
      chapter12PullbackFamily D H g.unop
        (chapter12PullbackFamily D H f.unop Z)
    rw [CategoryTheory.unop_comp]
    symm
    exact chapter12PullbackFamily_comp D H g.unop f.unop Z

@[simp]
theorem chapter12HilbertFunctor_obj
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial)
    (T : Chapter12SchemeOver D.base) :
    (chapter12HilbertFunctor D H P).obj (Opposite.op T) =
      Chapter12HilbertFamily D H T P :=
  rfl

@[simp]
theorem chapter12HilbertFunctor_map
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial)
    {T U : Chapter12SchemeOver D.base} (g : T ⟶ U)
    (Z : Chapter12HilbertFamily D H U P) :
    (chapter12HilbertFunctor D H P).map g.op Z =
      chapter12PullbackFamily D H g Z := by
  change chapter12PullbackFamily D H (P := P) (g.op).unop Z =
    chapter12PullbackFamily D H (P := P) g Z
  simp only [Quiver.Hom.unop_op]

/-- A closed-immersion automorphism over the ambient scheme is trivial. -/
theorem chapter12_closed_subscheme_no_nontrivial_automorphism
    (D : Chapter12ProjectiveFamilySetup)
    {T : Chapter12SchemeOver D.base} (Z : Chapter12ClosedFamily D T)
    (e : Z.ideal.subscheme ⟶ Z.ideal.subscheme)
    (h : e ≫ Z.ideal.subschemeι = Z.ideal.subschemeι) :
    e = 𝟙 _ := by
  apply (cancel_mono Z.ideal.subschemeι).1
  simpa using h

/-- Equality of ideal sheaves is the extensionality principle for family objects. -/
@[ext]
theorem chapter12ClosedFamily_ext
    (D : Chapter12ProjectiveFamilySetup)
    {T : Chapter12SchemeOver D.base} (Z Z' : Chapter12ClosedFamily D T)
    (h : Z.ideal = Z'.ideal) : Z = Z' := by
  cases Z
  cases Z'
  simp_all

/-- Constant fiber Hilbert polynomial is equivalent to finite locally free rank. -/
theorem chapter12_constant_polynomial_iff_finite_locally_free
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (K : Chapter12HilbertLengthCompatibility D H)
    {T : Chapter12SchemeOver D.base} (d : ℕ)
    (Z : Chapter12ClosedFamily D T) :
      (∀ t : Chapter12GeometricPoint T.left,
      chapter12HasFiberHilbertPolynomial H Z t (chapter12ConstantPolynomial d)) ↔
      Chapter12FiniteLocallyFreeRank (chapter12FamilyProjection D T Z.ideal) d := by
  sorry

/-- The length-`d` Hilbert objects form the finite-locally-free subfunctor. -/
noncomputable def chapter12_hilbertFamily_constant_polynomial_equiv
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (K : Chapter12HilbertLengthCompatibility D H)
    {T : Chapter12SchemeOver D.base} (d : ℕ) :
    Chapter12HilbertFamily D H T (chapter12ConstantPolynomial d) ≃
      {Z : Chapter12ClosedFamily D T //
        Chapter12FiniteLocallyFreeRank (chapter12FamilyProjection D T Z.ideal) d} := by
  let hiff := chapter12_constant_polynomial_iff_finite_locally_free
    D H K (T := T) d
  refine
    { toFun := fun Z =>
        ⟨Z.closed, (hiff Z.closed).mp Z.fiber_polynomial⟩
      invFun := fun Z =>
        { closed := Z.1
          fiber_polynomial := fun t =>
            (K.polynomial_iff_fiber_length Z.1 t d).mpr (Z.2.rank t.basePoint) }
      left_inv := ?_
      right_inv := ?_ }
  · intro Z
    rfl
  · intro Z
    rfl

/-- The quotient remembered by a Hilbert object has an ideal kernel. -/
theorem chapter12_hilbertFamily_is_ideal_quotient
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    {T : Chapter12SchemeOver D.base} {P : Chapter12NumericalPolynomial}
    (Z : Chapter12HilbertFamily D H T P) :
    (chapter12FamilyInclusion D T Z.closed).ker = Z.closed.ideal := by
  exact chapter12_family_ideal_kernel D Z.closed

/-- The family type is a set of ideal sheaves, not a groupoid of presentations. -/
theorem chapter12_hilbertFunctor_map_id_family
    (D : Chapter12ProjectiveFamilySetup)
    (H : Chapter12HilbertPolynomialTheory D)
    (P : Chapter12NumericalPolynomial)
    {T : Chapter12SchemeOver D.base}
    (Z : Chapter12HilbertFamily D H T P) :
    (chapter12HilbertFunctor D H P).map (𝟙 (Opposite.op T)) Z = Z := by
  change chapter12PullbackFamily D H ((𝟙 (Opposite.op T)).unop) Z = Z
  simpa using chapter12PullbackFamily_id D H Z

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter12
