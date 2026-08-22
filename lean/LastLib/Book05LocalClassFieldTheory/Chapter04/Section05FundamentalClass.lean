import LastLib.Book05LocalClassFieldTheory.Chapter04.Section04RelativeBrauerGroups

namespace LastLib.Book05LocalClassFieldTheory.Chapter04

noncomputable section

open scoped BigOperators TensorProduct

/-! ## 4.5. The fundamental class -/

theorem chapter04_crossed_product_cocycle_identity_is_associativity
    {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]
    [MulDistribMulAction G Lˣ]
    (c : Chapter04NormalizedTwoCocycle G L) :
    ∀ g h k,
      c.value g h * c.value (g * h) k =
        (g • c.value h k) * c.value g (h * k) := by
  exact c.cocycle

theorem chapter04_crossed_product_scalar_mul_scalar
    {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]
    [MulDistribMulAction G Lˣ]
    (c : Chapter04NormalizedTwoCocycle G L) (x y : L) :
    chapter04CrossedProductMul c
        (chapter04CrossedProductScalar x)
        (chapter04CrossedProductScalar y) =
      chapter04CrossedProductScalar (x * y) := by
  sorry

theorem chapter04_crossed_product_basis_mul_scalar
    {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]
    [MulDistribMulAction G Lˣ]
    (c : Chapter04NormalizedTwoCocycle G L) (g : G) (x : L) :
    chapter04CrossedProductMul c
        (chapter04CrossedProductBasis g)
        (chapter04CrossedProductScalar x) =
      Finsupp.single g (g • x) := by
  sorry

theorem chapter04_crossed_product_basis_mul_basis
    {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]
    [MulDistribMulAction G Lˣ]
    (c : Chapter04NormalizedTwoCocycle G L) (g h : G) :
    chapter04CrossedProductMul c
        (chapter04CrossedProductBasis g)
        (chapter04CrossedProductBasis h) =
      Finsupp.single (g * h) (c.value g h : L) := by
  sorry

theorem chapter04_crossed_product_mul_is_associative
    {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]
    [MulDistribMulAction G Lˣ]
    (c : Chapter04NormalizedTwoCocycle G L) :
    ∀ x y z,
      chapter04CrossedProductMul c
          (chapter04CrossedProductMul c x y) z =
        chapter04CrossedProductMul c x
          (chapter04CrossedProductMul c y z) := by
  sorry

structure Chapter04CrossedProductBrauerRepresentative
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (c : Chapter04NormalizedTwoCocycle (Gal(L / K)) L) where
  carrier : chapter04CentralSimpleAlgebra K
  embedL : L →ₐ[K] carrier
  carrier_equivalence :
    chapter04CrossedProductCarrier (Gal(L / K)) L ≃ₗ[K] carrier
  carrier_equivalence_scalar : ∀ x : L,
    carrier_equivalence (chapter04CrossedProductScalar x) = embedL x
  multiplication_compatibility : ∀ x y,
    carrier_equivalence (chapter04CrossedProductMul c x y) =
      carrier_equivalence x * carrier_equivalence y
  dimension_eq : Module.finrank K carrier =
    (Nat.card (Gal(L / K))) ^ 2
  brauerClass : chapter04BrauerGroup K
  brauerClass_eq_carrier : brauerClass = chapter04BrauerClass carrier

theorem chapter04_crossed_product_is_central_simple
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (c : Chapter04NormalizedTwoCocycle (Gal(L / K)) L) :
    Nonempty (Chapter04CrossedProductBrauerRepresentative K L c) := by
  sorry

theorem chapter04_crossed_product_is_central_simple_of_cocycle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (c : Chapter04NormalizedTwoCocycle (Gal(L / K)) L) :
    Nonempty (Chapter04CrossedProductBrauerRepresentative K L c) := by
  sorry

theorem chapter04_full_matrix_algebra_automorphism_is_inner
    {S : Type*} [Field S] (n : ℕ)
    (φ : Matrix (Fin n) (Fin n) S ≃ₐ[S] Matrix (Fin n) (Fin n) S) :
    ∃ T : (Matrix (Fin n) (Fin n) S)ˣ, ∀ X,
      φ X = (T : Matrix (Fin n) (Fin n) S) * X * (T⁻¹ : Matrix (Fin n) (Fin n) S) := by
  sorry

theorem chapter04_coboundary_rescaling_preserves_crossed_product_class
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (c₁ c₂ : Chapter04NormalizedTwoCocycle (Gal(L / K)) L)
    (hcohom : chapter04CocycleCohomologous c₁ c₂) :
    ∀ A₁ : Chapter04CrossedProductBrauerRepresentative K L c₁,
      ∃ B₁ : Chapter04CrossedProductBrauerRepresentative K L c₂,
        A₁.brauerClass = B₁.brauerClass := by
  sorry

theorem chapter04_coboundary_is_basis_rescaling
    {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]
    [MulDistribMulAction G Lˣ]
    (c₁ c₂ : Chapter04NormalizedTwoCocycle G L)
    (hcohom : chapter04CocycleCohomologous c₁ c₂) :
    ∃ b : G → Lˣ, ∀ g h,
      c₂.value g h = b g * (g • b h) * (b (g * h))⁻¹ * c₁.value g h := by
  exact hcohom

theorem chapter04_cocycle_product_corresponds_to_tensor_product
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (B : Chapter04BrauerGroupLaw K)
    (c₁ c₂ : Chapter04NormalizedTwoCocycle (Gal(L / K)) L)
    (A₁ : Chapter04CrossedProductBrauerRepresentative K L c₁)
    (A₂ : Chapter04CrossedProductBrauerRepresentative K L c₂)
    (c₁₂ : Chapter04NormalizedTwoCocycle (Gal(L / K)) L)
    (hproduct : ∀ g h,
      c₁₂.value g h = c₁.value g h * c₂.value g h) :
    B.tensor A₁.brauerClass A₂.brauerClass =
      (Classical.choice (chapter04_crossed_product_is_central_simple c₁₂)).brauerClass := by
  sorry

structure Chapter04SplitDescentData
    (K L V : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V] where
  algebra : chapter04CentralSimpleAlgebra K
  split_matrix_identification : Nonempty
    (L ⊗[K] algebra.carrier ≃ₐ[L] Module.End L V)
  semilinear_action : Gal(L / K) → V → V
  semilinear_add : ∀ g v w,
    semilinear_action g (v + w) = semilinear_action g v + semilinear_action g w
  semilinear_smul : ∀ (g : Gal(L / K)) (a : L) (v : V),
    semilinear_action g (a • v) = (g • a) • semilinear_action g v
  semilinear_bijective : ∀ g, Function.Bijective (semilinear_action g)
  semilinear_one : ∀ v, semilinear_action 1 v = v
  semilinear_mul : ∀ g h v,
    semilinear_action (g * h) v =
      semilinear_action g (semilinear_action h v)
  linear_operators : Gal(L / K) → (V ≃ₗ[L] V)
  matrixAction : Gal(L / K) → Module.End L V → Module.End L V
  matrixAction_apply : ∀ g X v,
    matrixAction g X v =
      semilinear_action g (X (semilinear_action g⁻¹ v))
  cocycleValue : Gal(L / K) → Gal(L / K) → Lˣ
  cocycle_left_normalized : ∀ g, cocycleValue 1 g = 1
  cocycle_right_normalized : ∀ g, cocycleValue g 1 = 1
  inner_automorphism_relation : ∀ g X v,
    matrixAction g X v = linear_operators g (X ((linear_operators g).symm v))
  scalar_relation : ∀ g h v,
    linear_operators g (matrixAction g (linear_operators h) v) =
      (cocycleValue g h : L) • linear_operators (g * h) v

theorem chapter04_split_descent_produces_a_cocycle
    {K L V : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V]
    (D : Chapter04SplitDescentData K L V) :
    ∀ g h k,
      D.cocycleValue g h * D.cocycleValue (g * h) k =
        (g • D.cocycleValue h k) * D.cocycleValue g (h * k) := by
  sorry

theorem chapter04_split_descent_inner_automorphisms_exist
    {K L V : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V]
    (D : Chapter04SplitDescentData K L V) :
    ∀ g, ∃ T : V ≃ₗ[L] V, ∀ X v,
      D.matrixAction g X v = T (X (T.symm v)) := by
  sorry

theorem chapter04_split_descent_scalar_relation
    {K L V : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V]
    (D : Chapter04SplitDescentData K L V) :
    ∀ g h v,
      D.linear_operators g (D.matrixAction g (D.linear_operators h) v) =
        (D.cocycleValue g h : L) • D.linear_operators (g * h) v := by
  sorry

theorem chapter04_relative_brauer_group_is_second_cohomology
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (R : Chapter04BrauerRestrictionData K L)
    (hcompat : ∀ A : chapter04CentralSimpleAlgebra K,
      R.restriction (chapter04BrauerClass A) =
        chapter04BrauerClass (R.scalarExtension A)) :
    Nonempty (Chapter04RelativeBrauerCohomologyData K L R) := by
  sorry

structure Chapter04RelativeH2CyclicData
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] where
  finite : Finite (chapter04H2 K L)
  cyclic : IsAddCyclic (chapter04H2 K L)
  card_eq : Nat.card (chapter04H2 K L) = Nat.card (Gal(L / K))
  card_eq_degree : Nat.card (chapter04H2 K L) = Module.finrank K L

theorem chapter04_relative_h2_is_cyclic_of_degree
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L)
    (C : Chapter04RelativeBrauerCohomologyData K L R)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (hcompat : ∀ A : chapter04CentralSimpleAlgebra K,
      R.restriction (chapter04BrauerClass A) =
        chapter04BrauerClass (R.scalarExtension A)) :
    Nonempty (Chapter04RelativeH2CyclicData K L) := by
  sorry

def chapter04CohomologyInvariant
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L)
    (C : Chapter04RelativeBrauerCohomologyData K L R)
    (u : chapter04H2 K L) : chapter04RationalResidue :=
  I.invariant (C.toRelative u).1

theorem chapter04_fundamental_class_exists_unique
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L)
    (C : Chapter04RelativeBrauerCohomologyData K L R)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (himage : Set.range (chapter04CohomologyInvariant I R C) =
      chapter04RationalResidueOneOverMultiples n) :
    ∃! u : chapter04H2 K L,
      chapter04CohomologyInvariant I R C u =
        chapter04RationalResidueOneOver n := by
  sorry

structure Chapter04FundamentalClass
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L)
    (C : Chapter04RelativeBrauerCohomologyData K L R) (n : ℕ) where
  value : chapter04H2 K L
  degree_pos : 0 < n
  invariant_eq_one_over :
    chapter04CohomologyInvariant I R C value = chapter04RationalResidueOneOver n

noncomputable def chapter04FundamentalClassChoice
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L)
    (C : Chapter04RelativeBrauerCohomologyData K L R)
    (n : ℕ) (hn : 0 < n) (hdegree : Module.finrank K L = n)
    (himage : Set.range (chapter04CohomologyInvariant I R C) =
      chapter04RationalResidueOneOverMultiples n) :
    Chapter04FundamentalClass I R C n := by
  sorry

theorem chapter04_fundamental_class_is_unique
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L)
    (C : Chapter04RelativeBrauerCohomologyData K L R) (n : ℕ)
    (u v : Chapter04FundamentalClass I R C n) : u.value = v.value := by
  sorry

/- The tower interface records the restriction and corestriction equations
  stated explicitly in the source. -/
structure Chapter04FundamentalClassTowerData
    (K M L : Type) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional M L] [FiniteDimensional K L] [IsGalois K L]
    [IsGalois M L] where
  degreeKM : ℕ
  degreeML : ℕ
  degreeKL : ℕ
  degreeKM_pos : 0 < degreeKM
  degreeML_pos : 0 < degreeML
  degreeKM_eq : Module.finrank K M = degreeKM
  degreeML_eq : Module.finrank M L = degreeML
  degreeKL_eq : Module.finrank K L = degreeKL
  degree_factor : degreeKL = degreeKM * degreeML
  invariantK : Chapter04LocalInvariantData K
  invariantM : Chapter04LocalInvariantData M
  restrictionKL : Chapter04BrauerRestrictionData K L
  restrictionML : Chapter04BrauerRestrictionData M L
  cohomologyKL : Chapter04RelativeBrauerCohomologyData K L restrictionKL
  cohomologyML : Chapter04RelativeBrauerCohomologyData M L restrictionML
  restriction : chapter04H2 K L → chapter04H2 M L
  corestriction : chapter04H2 M L → chapter04H2 K L
  fundamentalKL : chapter04H2 K L
  fundamentalML : chapter04H2 M L
  fundamentalKL_invariant :
    chapter04CohomologyInvariant invariantK restrictionKL cohomologyKL fundamentalKL =
      chapter04RationalResidueOneOver degreeKL
  fundamentalML_invariant :
    chapter04CohomologyInvariant invariantM restrictionML cohomologyML fundamentalML =
      chapter04RationalResidueOneOver degreeML
  restriction_fundamental :
    restriction fundamentalKL = fundamentalML
  corestriction_fundamental :
    corestriction fundamentalML = degreeKM • fundamentalKL

theorem chapter04_fundamental_class_is_tower_compatible
    {K M L : Type} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional M L] [FiniteDimensional K L] [IsGalois K L]
    [IsGalois M L]
    (T : Chapter04FundamentalClassTowerData K M L) :
    T.degreeKL = T.degreeKM * T.degreeML ∧
      T.restriction T.fundamentalKL = T.fundamentalML ∧
      T.corestriction T.fundamentalML = T.degreeKM • T.fundamentalKL := by
  exact ⟨T.degree_factor, T.restriction_fundamental,
    T.corestriction_fundamental⟩

theorem chapter04_unramified_fundamental_class_has_frobenius_cyclic_representative
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) :
    ∃ c : Chapter04NormalizedTwoCocycle (Gal(L / K)) L,
      ∃ A : Chapter04CrossedProductBrauerRepresentative K L c,
        A.brauerClass = chapter04UnramifiedCyclicBrauerClass U 1 := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter04
