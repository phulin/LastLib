import LastLib.Book05LocalClassFieldTheory.Chapter01.Section02TheClassificationOneHopesFor

namespace LastLib.Book05LocalClassFieldTheory.Chapter01

noncomputable section

open Set
open scoped BigOperators Pointwise Topology WithZero IsMulCommutative

/-! ## 1.3. The reciprocity convention -/

/- A reduction identification for an unramified finite extension.  The
`Chapter06` reduction record only stores the group equivalence; this wrapper
also carries the existing Book 2 unramified-extension witness. -/
structure Chapter01UnramifiedGaloisReduction
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l] where
  reduction :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Chapter06UnramifiedGaloisReduction
      K L k l
  profile :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Chapter07FiniteLocalExtensionData
      K L k l
  unramified :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Chapter07UnramifiedExtension
      profile

/-- The arithmetic Frobenius lifted to an unramified local extension. -/
noncomputable def chapter01ArithmeticFrobenius
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter01UnramifiedGaloisReduction K L k l) : Gal(L / K) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedArithmeticFrobenius
    D.reduction

/-- The geometric Frobenius convention upstairs. -/
noncomputable def chapter01GeometricFrobenius
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter01UnramifiedGaloisReduction K L k l) : Gal(L / K) :=
  (chapter01ArithmeticFrobenius D)⁻¹

/-- The residue action of arithmetic Frobenius is `x ↦ x^q`. -/
theorem chapter01_arithmetic_frobenius_residue_formula
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter01UnramifiedGaloisReduction K L k l) (x : l) :
    D.reduction.reduction (chapter01ArithmeticFrobenius D) x =
      x ^ Fintype.card k := by
  simpa [chapter01ArithmeticFrobenius,
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06UnramifiedArithmeticFrobenius] using
    (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_arithmetic_frobenius_apply k l x)

/-- The arithmetic Frobenius lift is unique. -/
theorem chapter01_arithmetic_frobenius_lift_unique
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter01UnramifiedGaloisReduction K L k l) :
    ∃! σ : Gal(L / K),
      D.reduction.reduction σ =
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06ArithmeticFrobenius
          k l := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.chapter06_unramified_arithmetic_frobenius_unique
    D.reduction

/-- Arithmetic and geometric Frobenius are inverse conventions. -/
theorem chapter01_geometric_frobenius_is_inverse
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter01UnramifiedGaloisReduction K L k l) :
    chapter01GeometricFrobenius D =
      (chapter01ArithmeticFrobenius D)⁻¹ := by
  rfl

/-- Geometric reciprocity is pointwise inverse to arithmetic reciprocity. -/
theorem chapter01_geometric_reciprocity_apply
    {G H : Type*} [Group G] [Group H] [IsMulCommutative H]
    (f : G →* H) (x : G) :
    chapter01GeometricInverseHom f x = (f x)⁻¹ :=
  rfl

/-- Arithmetic normalization for a chosen finite or inverse-limit target.  A
uniformizer is represented by a field unit whose valuation is one. -/
def Chapter01ArithmeticNormalization
    {K G : Type*} [Field K] [Group G]
    (vK : AddValuation K (WithTop ℤ)) (rec : Kˣ →* G) (φ : G) : Prop :=
  ∀ π : Kˣ, vK (π : K) = (1 : WithTop ℤ) → rec π = φ

/-- A finite reciprocity equivalence together with the arithmetic Frobenius
normalization. -/
structure Chapter01FiniteReciprocityNormalization
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    (vK : AddValuation K (WithTop ℤ))
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    [Fintype (Gal(L / K))] [IsMulCommutative (Gal(L / K))] where
  unramified : Chapter01UnramifiedGaloisReduction K L k l
  quotientEquiv : Chapter01NormQuotient K L ≃* Gal(L / K)
  local_field : Chapter01LocalField vK
  normalization :
    Chapter01ArithmeticNormalization vK
      (chapter01FiniteArtinMap quotientEquiv)
      (chapter01ArithmeticFrobenius unramified)

/-- The arithmetic-normalized finite reciprocity map at a uniformizer. -/
theorem chapter01_arithmetic_normalization_apply
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    (vK : AddValuation K (WithTop ℤ))
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    [Fintype (Gal(L / K))] [IsMulCommutative (Gal(L / K))]
    (N : Chapter01FiniteReciprocityNormalization K L k l vK)
    (π : Kˣ) (hπ : vK (π : K) = (1 : WithTop ℤ)) :
    chapter01FiniteArtinMap N.quotientEquiv π =
      chapter01ArithmeticFrobenius N.unramified :=
  N.normalization π hπ

/-- Geometric normalization sends the same uniformizer to geometric
Frobenius. -/
theorem chapter01_geometric_normalization_apply
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    (vK : AddValuation K (WithTop ℤ))
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    [Fintype (Gal(L / K))] [IsMulCommutative (Gal(L / K))]
    (N : Chapter01FiniteReciprocityNormalization K L k l vK)
    (π : Kˣ) (hπ : vK (π : K) = (1 : WithTop ℤ)) :
    chapter01GeometricInverseHom (chapter01FiniteArtinMap N.quotientEquiv)
        π = (chapter01ArithmeticFrobenius N.unramified)⁻¹ := by
  sorry

/-- The normalization predicate applies to any chosen normalized
uniformizer. -/
theorem chapter01_arithmetic_normalization_condition_apply
    {K G : Type*} [Field K] [Group G]
    (vK : AddValuation K (WithTop ℤ)) (rec : Kˣ →* G) (φ : G)
    (π : Kˣ) (hπ : vK (π : K) = (1 : WithTop ℤ))
    (h : Chapter01ArithmeticNormalization vK rec φ) :
    rec π = φ :=
  h π hπ

end

end LastLib.Book05LocalClassFieldTheory.Chapter01
