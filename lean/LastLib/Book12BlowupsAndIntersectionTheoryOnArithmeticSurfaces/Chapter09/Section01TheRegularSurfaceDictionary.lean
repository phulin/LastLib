import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Order TopologicalSpace
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 9.1. The regular-surface dictionary -/

/-- Every codimension-one local ring on a regular noetherian integral surface
is a discrete valuation ring. -/
theorem chapter09_regular_surface_codimOne_stalk_isDVR
    (X : Chapter09RegularNoetherianIntegralSurface)
    (ξ : Chapter09CodimensionOnePoint X.carrier) :
    IsDiscreteValuationRing (Chapter09CodimOneStalk X ξ) := by
  sorry

/-- The codimension-one stalk assertion in a form convenient for finite
families of prime curves. -/
theorem chapter09_regular_surface_all_codimOne_stalks_areDVR
    (X : Chapter09RegularNoetherianIntegralSurface) :
    ∀ ξ : Chapter09CodimensionOnePoint X.carrier,
      IsDiscreteValuationRing (Chapter09CodimOneStalk X ξ) := by
  intro ξ
  exact chapter09_regular_surface_codimOne_stalk_isDVR X ξ

/-- The local valuation is the order used by the principal-divisor
coefficient interface. -/
theorem chapter09_primeCurve_order_is_additive
    (X : Chapter09RegularNoetherianIntegralSurface)
    (C : Chapter09PrimeCurve X) (f g : chapter09RationalFunction X) :
    C.order (f * g) = C.order f + C.order g := by
  exact C.order_mul f g

@[simp]
theorem chapter09_primeCurve_order_one
    (X : Chapter09RegularNoetherianIntegralSurface)
    (C : Chapter09PrimeCurve X) : C.order 1 = 0 := by
  exact C.order_one

/-! ### Weil divisors, Cartier divisors, and line bundles -/

/-- A Weil divisor is a finite integer sum of prime curves. -/
theorem chapter09_weil_divisor_has_finite_support
    (X : Chapter09RegularNoetherianIntegralSurface)
    (D : Chapter09WeilDivisor X) :
    (D.support : Set (Chapter09PrimeCurve X)).Finite := by
  sorry

@[simp]
theorem chapter09_weil_divisor_coeff_zero
    (X : Chapter09RegularNoetherianIntegralSurface)
    (C : Chapter09PrimeCurve X) : (0 : Chapter09WeilDivisor X) C = 0 := by
  rfl

theorem chapter09_weil_divisor_coeff_add
    (X : Chapter09RegularNoetherianIntegralSurface)
    (D E : Chapter09WeilDivisor X) (C : Chapter09PrimeCurve X) :
    (D + E) C = D C + E C := by
  rfl

theorem chapter09_weil_divisor_coeff_sub
    (X : Chapter09RegularNoetherianIntegralSurface)
    (D E : Chapter09WeilDivisor X) (C : Chapter09PrimeCurve X) :
    (D - E) C = D C - E C := by
  rfl

/-- The regular-surface dictionary exists: Cartier local equations, Weil
prime-curve coefficients, and line bundles with rational sections encode the
same divisor data. -/
theorem chapter09_regular_surface_dictionary_exists
    (X : Chapter09RegularNoetherianIntegralSurface) :
    Nonempty (Chapter09RegularSurfaceDictionary X) := by
  sorry

/- A reusable choice of the dictionary is useful to later sections, while the
existence theorem above keeps the construction noncanonical at this stage. -/
noncomputable def chapter09RegularSurfaceDictionary
    (X : Chapter09RegularNoetherianIntegralSurface) :
    Chapter09RegularSurfaceDictionary X :=
  Classical.choice (chapter09_regular_surface_dictionary_exists X)

theorem chapter09_regular_surface_dictionary_nonempty
    (X : Chapter09RegularNoetherianIntegralSurface) :
    Nonempty (Chapter09CartierPresentation X) := by
  let T := chapter09RegularSurfaceDictionary X
  rcases T.cartierRealizes 0 with ⟨P, _hP⟩
  exact ⟨P⟩

/-- Every Weil divisor admits a Cartier local-equation presentation. -/
theorem chapter09_weil_divisor_is_cartier
    (X : Chapter09RegularNoetherianIntegralSurface)
    (D : Chapter09WeilDivisor X) :
    ∃ P : Chapter09CartierPresentation X, P.divisor = D := by
  let T := chapter09RegularSurfaceDictionary X
  rcases T.cartierRealizes D with ⟨P, hP⟩
  exact ⟨P, (T.cartierToWeil_eq_divisor P).symm.trans hP⟩

noncomputable def chapter09CartierPresentationOf
    (X : Chapter09RegularNoetherianIntegralSurface)
    (D : Chapter09WeilDivisor X) : Chapter09CartierPresentation X :=
  Classical.choose (chapter09_weil_divisor_is_cartier X D)

theorem chapter09CartierPresentationOf_divisor
    (X : Chapter09RegularNoetherianIntegralSurface)
    (D : Chapter09WeilDivisor X) :
    (chapter09CartierPresentationOf X D).divisor = D := by
  exact Classical.choose_spec (chapter09_weil_divisor_is_cartier X D)

/-- The line-bundle/rational-section presentation is available for every
Cartier presentation. -/
theorem chapter09_cartier_presentation_has_lineBundle_section
    (X : Chapter09RegularNoetherianIntegralSurface)
    (P : Chapter09CartierPresentation X) :
    ∃ L : Chapter09LineBundleRationalSection X,
      L.lineBundle = P.associatedLineBundle ∧
        L.rationalSection = P.rationalSection := by
  refine ⟨chapter09LineBundleRationalSectionOfPresentation P, rfl, rfl⟩

/-! ### Zero-cycles and their degree -/

/-- The support of a zero-cycle is finite because it is represented by a
`Finsupp`. -/
theorem chapter09_zeroCycle_has_finite_support
    {X : Scheme.{u}} (z : Chapter09ZeroCycle X) :
    (z.support : Set (Chapter09ClosedPoint X)).Finite := by
  sorry

@[ext]
theorem chapter09_closedPoint_ext
    {X : Scheme.{u}} {x y : Chapter09ClosedPoint X}
    (h : x.point = y.point) : x = y := by
  cases x
  cases y
  cases h
  rfl

@[ext]
theorem chapter09_zeroCycle_ext
    {X : Scheme.{u}} {z w : Chapter09ZeroCycle X}
    (h : ∀ x, z x = w x) : z = w := by
  exact Finsupp.ext h

@[simp]
theorem chapter09_zeroCycleCoeff_zero
    {X : Scheme.{u}} (x : Chapter09ClosedPoint X) :
    (0 : Chapter09ZeroCycle X) x = 0 := by
  rfl

theorem chapter09_zeroCycleCoeff_add
    {X : Scheme.{u}} (z w : Chapter09ZeroCycle X)
    (x : Chapter09ClosedPoint X) :
    (z + w) x = z x + w x := by
  rfl

theorem chapter09_zeroCycle_mem_support_iff
    {X : Scheme.{u}} (z : Chapter09ZeroCycle X)
    (x : Chapter09ClosedPoint X) :
    x ∈ z.support ↔ z x ≠ 0 := by
  exact Finsupp.mem_support_iff

/-- Degree over a chosen base point is the sum of coefficients weighted by
the residue-field degrees. -/
theorem chapter09_zeroCycle_degree_is_residueWeighted_sum
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (z : Chapter09ZeroCycle X)
    (hz : chapter09ZeroCycleSupportedOver f s z) :
    chapter09ZeroCycleDegree f z =
      ∑ x in z.support, z x * (f.residueDegree x.point : ℤ) := by
  exact chapter09_zeroCycle_degree_formula f s z hz

theorem chapter09_zeroCycle_degree_add
    {X S : Scheme.{u}} (f : X ⟶ S)
    (z w : Chapter09ZeroCycle X) :
    chapter09ZeroCycleDegree f (z + w) =
      chapter09ZeroCycleDegree f z + chapter09ZeroCycleDegree f w := by
  sorry

/-! ### Canonical and book-facing formulations -/

/-- The book's prime-curve coefficient is the coefficient of the associated
finite cycle summand. -/
theorem chapter09_divisor_coeff_iff_mem_support
    (X : Chapter09RegularNoetherianIntegralSurface)
    (D : Chapter09WeilDivisor X) (C : Chapter09PrimeCurve X) :
    C ∈ D.support ↔ D C ≠ 0 := by
  exact Finsupp.mem_support_iff

@[ext]
theorem chapter09_weil_divisor_ext
    {X : Chapter09RegularNoetherianIntegralSurface}
    {D E : Chapter09WeilDivisor X}
    (h : ∀ C, D C = E C) : D = E := by
  exact Finsupp.ext h

/-- The local Cartier presentation and the finite prime-curve coefficient
presentation are equivalent on a regular surface. -/
theorem chapter09_cartier_iff_weil_presentation
    (X : Chapter09RegularNoetherianIntegralSurface)
    (D : Chapter09WeilDivisor X) :
    (∃ P : Chapter09CartierPresentation X, P.divisor = D) ↔
      (∃ P : Chapter09CartierPresentation X,
        (chapter09RegularSurfaceDictionary X).cartierToWeil P = D) := by
  let T := chapter09RegularSurfaceDictionary X
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P, (T.cartierToWeil_eq_divisor P).trans hP⟩
  · rintro ⟨P, hP⟩
    exact ⟨P, (T.cartierToWeil_eq_divisor P).symm.trans hP⟩

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter09
