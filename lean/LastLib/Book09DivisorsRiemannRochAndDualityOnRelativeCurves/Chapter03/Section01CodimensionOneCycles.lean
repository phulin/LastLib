import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/-! ## 3.1. Codimension-one cycles -/

/-- The function field used for rational functions on an integral scheme. -/
abbrev Chapter03RationalFunction (X : Scheme.{u}) [IsIntegral X] := X.functionField

/-- The support of the closed subscheme underlying a prime divisor is closed. -/
theorem chapter03_primeDivisor_support_isClosed {X : Scheme.{u}}
    (P : Chapter03PrimeDivisor X) : IsClosed P.support := by
  exact P.closedSubscheme.support.isClosed

/-- The support of a prime divisor is irreducible. -/
theorem chapter03_primeDivisor_support_isIrreducible {X : Scheme.{u}}
    (P : Chapter03PrimeDivisor X) : IsIrreducible P.support := by
  sorry

/-- The integral closed-subscheme condition in the definition of a prime divisor. -/
theorem chapter03_primeDivisor_support_isIntegral {X : Scheme.{u}}
    (P : Chapter03PrimeDivisor X) : IsIntegral P.closedSubscheme.subscheme :=
  P.integral

/-- Normality turns the local ring at a codimension-one point into a DVR. -/
theorem chapter03_normal_codimensionOne_stalk_isDVR
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Chapter03Normal X] (P : Chapter03PrimeDivisor X) :
    IsDiscreteValuationRing (X.presheaf.stalk P.genericPoint) := by
  sorry

/-- Mathlib's order of vanishing, restricted to the generic point of a prime divisor. -/
noncomputable def chapter03OrderOfVanishing
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (P : Chapter03PrimeDivisor X) : ℤ :=
  X.ord f P.genericPoint

theorem chapter03_orderOfVanishing_eq_ord
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (P : Chapter03PrimeDivisor X) :
    chapter03OrderOfVanishing f P = X.ord f P.genericPoint :=
  rfl

theorem chapter03_orderOfVanishing_eq_ordHom
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (P : Chapter03PrimeDivisor X) :
    chapter03OrderOfVanishing f P =
      Multiplicative.toAdd ((X.ordHom P.genericPoint P.codim_one f).unzeroD 1) := by
  exact X.ord_eq_ordHom_of_coheight_eq_one P.codim_one f

theorem chapter03_orderOfVanishing_zero
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (P : Chapter03PrimeDivisor X) :
    chapter03OrderOfVanishing (0 : X.functionField) P = 0 := by
  simp [chapter03OrderOfVanishing]

theorem chapter03_orderOfVanishing_mul
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f g : X.functionField) (hf : f ≠ 0) (hg : g ≠ 0)
    (P : Chapter03PrimeDivisor X) :
    chapter03OrderOfVanishing (f * g) P =
      chapter03OrderOfVanishing f P + chapter03OrderOfVanishing g P := by
  exact X.ord_mul hf hg

theorem chapter03_orderOfVanishing_inv
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) (P : Chapter03PrimeDivisor X) :
    chapter03OrderOfVanishing f⁻¹ P = -chapter03OrderOfVanishing f P := by
  sorry

theorem chapter03_orderOfVanishing_of_isUnit
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {U : X.Opens} [Nonempty U] (f : Γ(X, U)) (hf : IsUnit f)
    (P : Chapter03PrimeDivisor X) (hP : P.genericPoint ∈ U) :
    chapter03OrderOfVanishing (X.germToFunctionField U f) P = 0 := by
  exact X.ord_of_isUnit hf hP

/-- Every nonzero rational function admits an affine numerator/denominator presentation. -/
theorem chapter03_rationalFunction_affine_fraction
    {X : Scheme.{u}} [IsIntegral X] (f : X.functionField) (hf : f ≠ 0) :
    ∃ (U : X.affineOpens) (hU : Nonempty U) (a b : Γ(X, U)),
      letI := hU
      X.germToFunctionField U a / X.germToFunctionField U b = f ∧
        X.germToFunctionField U b ≠ 0 := by
  sorry

/-- The finite-support theorem needed to turn the valuation function into a divisor. -/
theorem chapter03_principal_order_finite_support
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] (f : X.functionField) :
    ∃ s : Finset (Chapter03PrimeDivisor X),
      ∀ P, chapter03OrderOfVanishing f P ≠ 0 → P ∈ s := by
  sorry

noncomputable def chapter03PrincipalSupport
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] (f : X.functionField) :
    Finset (Chapter03PrimeDivisor X) :=
  Classical.choose (chapter03_principal_order_finite_support f)

theorem chapter03_mem_principalSupport
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] (f : X.functionField) (P : Chapter03PrimeDivisor X)
    (hP : chapter03OrderOfVanishing f P ≠ 0) : P ∈ chapter03PrincipalSupport f := by
  exact Classical.choose_spec (chapter03_principal_order_finite_support f) P hP

/-- The principal Weil divisor associated with a rational function. -/
noncomputable def chapter03PrincipalWeilDivisor
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] (f : X.functionField) : Chapter03WeilDivisor X :=
  Finsupp.onFinset (chapter03PrincipalSupport f)
    (chapter03OrderOfVanishing f)
    (fun P hP => chapter03_mem_principalSupport f P hP)

theorem chapter03_principalWeilDivisor_coeff
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] (f : X.functionField) (P : Chapter03PrimeDivisor X) :
    chapter03PrincipalWeilDivisor f P = chapter03OrderOfVanishing f P := by
  simp [chapter03PrincipalWeilDivisor]

theorem chapter03_principalWeilDivisor_support_subset
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] (f : X.functionField) :
    (chapter03PrincipalWeilDivisor f).support ⊆ chapter03PrincipalSupport f := by
  exact Finsupp.support_onFinset_subset

theorem chapter03_principalWeilDivisor_mul
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] (f g : X.functionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    chapter03PrincipalWeilDivisor (f * g) =
      chapter03PrincipalWeilDivisor f + chapter03PrincipalWeilDivisor g := by
  apply chapter03_weilDivisor_ext
  intro P
  simp only [chapter03_principalWeilDivisor_coeff, chapter03_orderOfVanishing_mul f g hf hg]
  rfl

theorem chapter03_principalWeilDivisor_one
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] :
    chapter03PrincipalWeilDivisor (1 : X.functionField) = 0 := by
  sorry

theorem chapter03_principalWeilDivisor_inv
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] (f : X.functionField) (hf : f ≠ 0) :
    chapter03PrincipalWeilDivisor f⁻¹ = -chapter03PrincipalWeilDivisor f := by
  apply chapter03_weilDivisor_ext
  intro P
  simp only [chapter03_principalWeilDivisor_coeff, chapter03_orderOfVanishing_inv f hf]
  rfl

theorem chapter03_principalWeilDivisor_zero
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [Chapter03Normal X] :
    chapter03PrincipalWeilDivisor (0 : X.functionField) = 0 := by
  apply chapter03_weilDivisor_ext
  intro P
  simp [chapter03_principalWeilDivisor_coeff, chapter03OrderOfVanishing]

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter03
