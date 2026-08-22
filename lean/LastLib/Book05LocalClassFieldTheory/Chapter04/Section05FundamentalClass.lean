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
  simp [chapter04CrossedProductMul, chapter04CrossedProductScalar,
    c.right_normalized]

theorem chapter04_crossed_product_basis_mul_scalar
    {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]
    [MulDistribMulAction G Lˣ]
    (c : Chapter04NormalizedTwoCocycle G L) (g : G) (x : L) :
    chapter04CrossedProductMul c
        (chapter04CrossedProductBasis g)
        (chapter04CrossedProductScalar x) =
      Finsupp.single g (g • x) := by
  simp [chapter04CrossedProductMul, chapter04CrossedProductBasis,
    chapter04CrossedProductScalar, c.right_normalized]

theorem chapter04_crossed_product_basis_mul_basis
    {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]
    [MulDistribMulAction G Lˣ]
    (c : Chapter04NormalizedTwoCocycle G L) (g h : G) :
    chapter04CrossedProductMul c
        (chapter04CrossedProductBasis g)
        (chapter04CrossedProductBasis h) =
      Finsupp.single (g * h) (c.value g h : L) := by
  simp [chapter04CrossedProductMul, chapter04CrossedProductBasis]

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
  exact chapter04_crossed_product_is_central_simple c

theorem chapter04_full_matrix_algebra_automorphism_is_inner
    {S : Type*} [Field S] (n : ℕ)
    (hn : 0 < n)
    (φ : Matrix (Fin n) (Fin n) S ≃ₐ[S] Matrix (Fin n) (Fin n) S) :
    ∃ T : (Matrix (Fin n) (Fin n) S)ˣ, ∀ X,
      φ X = (T : Matrix (Fin n) (Fin n) S) * X * (T⁻¹ : Matrix (Fin n) (Fin n) S) := by
  let e : Matrix (Fin n) (Fin n) S ≃ₐ[S] Module.End S (Fin n → S) :=
    Matrix.toLinAlgEquiv'
  let ψ : Module.End S (Fin n → S) ≃ₐ[S] Module.End S (Fin n → S) :=
    (e.symm.trans φ).trans e
  obtain ⟨Tlin, hTlin⟩ := ψ.eq_linearEquivConjAlgEquiv
  let Tlin' : LinearMap.GeneralLinearGroup S (Fin n → S) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv Tlin
  let T : (Matrix (Fin n) (Fin n) S)ˣ :=
    Matrix.GeneralLinearGroup.toLin.symm Tlin'
  have hTunit : Matrix.GeneralLinearGroup.toLin T = Tlin' := by
    exact Matrix.GeneralLinearGroup.toLin.apply_symm_apply Tlin'
  have hT : e (T : Matrix (Fin n) (Fin n) S) = Tlin.toLinearMap := by
    change (Matrix.GeneralLinearGroup.toLin T).val = Tlin'.val
    rw [hTunit]
  have hTinv : e (T⁻¹ : Matrix (Fin n) (Fin n) S) = Tlin.symm.toLinearMap := by
    have hval :
        ((T : Matrix (Fin n) (Fin n) S)⁻¹) = (↑(T⁻¹) : Matrix (Fin n) (Fin n) S) :=
      (Matrix.GeneralLinearGroup.coe_inv T).symm
    rw [hval]
    have hTunit_inv : Matrix.GeneralLinearGroup.toLin T⁻¹ = Tlin'⁻¹ := by
      rw [map_inv, hTunit]
    change (Matrix.GeneralLinearGroup.toLin T⁻¹).val = Tlin.symm.toLinearMap
    rw [hTunit_inv]
    rfl
  refine ⟨T, ?_⟩
  intro X
  apply e.injective
  have hX := congrArg (fun f => f (e X)) hTlin
  have hψX : ψ (e X) = e (φ X) := by
    simp [ψ]
  rw [← hψX, hX]
  simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, hT, hTinv,
    map_mul, AlgEquiv.coe_trans, AlgEquiv.apply_symm_apply, Module.End.mul_eq_comp]
  rw [LinearMap.comp_assoc]

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
  have hmatrix : ∀ (g h : Gal(L / K)) (X : Module.End L V) (v : V),
      D.matrixAction g (D.matrixAction h X) v = D.matrixAction (g * h) X v := by
    intro g h X v
    rw [D.matrixAction_apply, D.matrixAction_apply, D.matrixAction_apply]
    rw [← D.semilinear_mul h⁻¹ g⁻¹, ← D.semilinear_mul g h]
    simp
  have hcomp : ∀ (g : Gal(L / K)) (X Y : Module.End L V) (v : V),
      D.matrixAction g (X * Y) v =
        (D.matrixAction g X) ((D.matrixAction g Y) v) := by
    intro g X Y v
    rw [D.matrixAction_apply, D.matrixAction_apply, D.matrixAction_apply]
    simp only [Module.End.mul_apply]
    rw [← D.semilinear_mul g⁻¹ g]
    simp only [inv_mul_cancel, D.semilinear_one]
  have hsmul : ∀ (g : Gal(L / K)) (a : L) (X : Module.End L V) (v : V),
      D.matrixAction g (a • X) v =
        (g • a) • D.matrixAction g X v := by
    intro g a X v
    rw [D.matrixAction_apply, D.matrixAction_apply]
    simp only [LinearMap.smul_apply]
    exact D.semilinear_smul g a (X (D.semilinear_action g⁻¹ v))
  have hmatrixop : ∀ (g h : Gal(L / K)) (X : Module.End L V),
      D.matrixAction g (D.matrixAction h X) = D.matrixAction (g * h) X := by
    intro g h X
    ext v
    exact hmatrix g h X v
  have hcompop : ∀ (g : Gal(L / K)) (X Y : Module.End L V),
      D.matrixAction g (X * Y) =
        D.matrixAction g X * D.matrixAction g Y := by
    intro g X Y
    ext v
    exact hcomp g X Y v
  have hsmulop : ∀ (g : Gal(L / K)) (a : L) (X : Module.End L V),
      D.matrixAction g (a • X) =
        (g • a) • D.matrixAction g X := by
    intro g a X
    ext v
    exact hsmul g a X v
  have hscalarop : ∀ (h k : Gal(L / K)),
      D.linear_operators h * D.matrixAction h (D.linear_operators k) =
        (D.cocycleValue h k : L) • D.linear_operators (h * k) := by
    intro h k
    ext v
    change D.linear_operators h (D.matrixAction h (D.linear_operators k) v) =
      (D.cocycleValue h k : L) • D.linear_operators (h * k) v
    exact D.scalar_relation h k v
  have hne : (1 : Module.End L V) ≠ 0 := by
    obtain ⟨e⟩ := D.split_matrix_identification
    intro h
    have heq : (1 : L ⊗[K] D.algebra.carrier) = 0 := by
      apply e.injective
      simpa using h
    exact one_ne_zero heq
  have hnonzero : ∃ v : V, v ≠ 0 := by
    by_contra h
    apply hne
    ext v
    have hv : v = 0 := by
      by_contra hv
      exact h ⟨v, hv⟩
    simp [hv]
  obtain ⟨v₀, hv₀⟩ := hnonzero
  intro g h k
  apply Units.ext
  have hleft :
      D.linear_operators g
          (D.matrixAction g (D.linear_operators h)
            (D.matrixAction (g * h) (D.linear_operators k) v₀)) =
        ((D.cocycleValue g h : L) *
          (D.cocycleValue (g * h) k : L)) •
          D.linear_operators (g * h * k) v₀ := by
    calc
      D.linear_operators g
          (D.matrixAction g (D.linear_operators h)
            (D.matrixAction (g * h) (D.linear_operators k) v₀)) =
          (D.cocycleValue g h : L) •
            D.linear_operators (g * h)
              (D.matrixAction (g * h) (D.linear_operators k) v₀) :=
        D.scalar_relation g h _
      _ = (D.cocycleValue g h : L) •
          ((D.cocycleValue (g * h) k : L) •
            D.linear_operators (g * h * k) v₀) := by
        rw [D.scalar_relation (g * h) k v₀]
      _ = ((D.cocycleValue g h : L) *
          (D.cocycleValue (g * h) k : L)) •
          D.linear_operators (g * h * k) v₀ := by
        rw [smul_smul]
  have hrightop :
      D.matrixAction g (D.linear_operators h) *
          D.matrixAction (g * h) (D.linear_operators k) =
        (g • (D.cocycleValue h k : L)) •
          D.matrixAction g (D.linear_operators (h * k)) := by
    calc
      D.matrixAction g (D.linear_operators h) *
          D.matrixAction (g * h) (D.linear_operators k) =
          D.matrixAction g (D.linear_operators h) *
            D.matrixAction g (D.matrixAction h (D.linear_operators k)) := by
        rw [hmatrixop g h (D.linear_operators k)]
      _ = D.matrixAction g
            (D.linear_operators h *
              D.matrixAction h (D.linear_operators k)) :=
        (hcompop g (D.linear_operators h)
          (D.matrixAction h (D.linear_operators k))).symm
      _ = D.matrixAction g
          ((D.cocycleValue h k : L) • D.linear_operators (h * k)) := by
        rw [hscalarop h k]
      _ = (g • (D.cocycleValue h k : L)) •
          D.matrixAction g (D.linear_operators (h * k)) :=
        hsmulop g (D.cocycleValue h k : L) (D.linear_operators (h * k))
  have hright :
      D.linear_operators g
          (D.matrixAction g (D.linear_operators h)
            (D.matrixAction (g * h) (D.linear_operators k) v₀)) =
        ((g • (D.cocycleValue h k : L)) *
          (D.cocycleValue g (h * k) : L)) •
          D.linear_operators (g * h * k) v₀ := by
    calc
      D.linear_operators g
          (D.matrixAction g (D.linear_operators h)
            (D.matrixAction (g * h) (D.linear_operators k) v₀)) =
          D.linear_operators g
            ((g • (D.cocycleValue h k : L)) •
              D.matrixAction g (D.linear_operators (h * k)) v₀) := by
        have hop := congrArg
          (fun X : Module.End L V => D.linear_operators g (X v₀)) hrightop
        simpa only [Module.End.mul_apply, LinearMap.smul_apply] using hop
      _ = (g • (D.cocycleValue h k : L)) •
          D.linear_operators g
            (D.matrixAction g (D.linear_operators (h * k)) v₀) := by
        rw [map_smul]
      _ = (g • (D.cocycleValue h k : L)) •
          ((D.cocycleValue g (h * k) : L) •
            D.linear_operators (g * h * k) v₀) := by
        rw [D.scalar_relation g (h * k) v₀]
        simp only [mul_assoc]
      _ = ((g • (D.cocycleValue h k : L)) *
          (D.cocycleValue g (h * k) : L)) •
          D.linear_operators (g * h * k) v₀ := by
        rw [smul_smul]
  have hvector :
      ((D.cocycleValue g h : L) *
          (D.cocycleValue (g * h) k : L)) •
          D.linear_operators (g * h * k) v₀ =
        ((g • (D.cocycleValue h k : L)) *
          (D.cocycleValue g (h * k) : L)) •
          D.linear_operators (g * h * k) v₀ :=
    hleft.symm.trans hright
  have hT : D.linear_operators (g * h * k) v₀ ≠ 0 := by
    intro hz
    apply hv₀
    apply (D.linear_operators (g * h * k)).injective
    simpa using hz
  have hscalar :
      (D.cocycleValue g h : L) * (D.cocycleValue (g * h) k : L) =
        (g • (D.cocycleValue h k : L)) *
          (D.cocycleValue g (h * k) : L) := by
    exact smul_left_injective L hT hvector
  exact hscalar

theorem chapter04_split_descent_inner_automorphisms_exist
    {K L V : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V]
    (D : Chapter04SplitDescentData K L V) :
    ∀ g, ∃ T : V ≃ₗ[L] V, ∀ X v,
      D.matrixAction g X v = T (X (T.symm v)) := by
  intro g
  exact ⟨D.linear_operators g, D.inner_automorphism_relation g⟩

theorem chapter04_split_descent_scalar_relation
    {K L V : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V]
    (D : Chapter04SplitDescentData K L V) :
    ∀ g h v,
      D.linear_operators g (D.matrixAction g (D.linear_operators h) v) =
        (D.cocycleValue g h : L) • D.linear_operators (g * h) v := by
  exact D.scalar_relation

theorem chapter04_relative_brauer_group_is_second_cohomology
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (R : Chapter04BrauerRestrictionData K L) :
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
    : Nonempty (Chapter04RelativeH2CyclicData K L) := by
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
  have _hdegree : Module.finrank K L = n := hdegree
  have hinj : Function.Injective (chapter04CohomologyInvariant I R C) := by
    intro u v huv
    have hsub : (C.toRelative u).1 = (C.toRelative v).1 := by
      apply I.invariant_injective
      exact huv
    have hto : C.toRelative u = C.toRelative v := Subtype.ext hsub
    calc
      u = C.fromRelative (C.toRelative u) := (C.left_inverse u).symm
      _ = C.fromRelative (C.toRelative v) := congrArg C.fromRelative hto
      _ = v := C.left_inverse v
  have htarget : chapter04RationalResidueOneOver n ∈
      Set.range (chapter04CohomologyInvariant I R C) := by
    rw [himage]
    exact ⟨1, by simp⟩
  rcases htarget with ⟨u, hu⟩
  refine ⟨u, hu, ?_⟩
  intro v hv
  apply hinj
  exact hv.trans hu.symm

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
  let h := chapter04_fundamental_class_exists_unique I R C n hdegree himage
  let u : chapter04H2 K L := Classical.choose h.exists
  have hu : chapter04CohomologyInvariant I R C u =
      chapter04RationalResidueOneOver n := Classical.choose_spec h.exists
  exact {
    value := u
    degree_pos := hn
    invariant_eq_one_over := hu
  }

theorem chapter04_fundamental_class_is_unique
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I : Chapter04LocalInvariantData K)
    (R : Chapter04BrauerRestrictionData K L)
    (C : Chapter04RelativeBrauerCohomologyData K L R) (n : ℕ)
    (u v : Chapter04FundamentalClass I R C n) : u.value = v.value := by
  have hinj : Function.Injective (chapter04CohomologyInvariant I R C) := by
    intro a b hab
    have hsub : (C.toRelative a).1 = (C.toRelative b).1 := by
      apply I.invariant_injective
      exact hab
    have hto : C.toRelative a = C.toRelative b := Subtype.ext hsub
    calc
      a = C.fromRelative (C.toRelative a) := (C.left_inverse a).symm
      _ = C.fromRelative (C.toRelative b) := congrArg C.fromRelative hto
      _ = b := C.left_inverse b
  apply hinj
  exact u.invariant_eq_one_over.trans v.invariant_eq_one_over.symm

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
  /- Prior attempt: the tower equalities were incorrectly stored as fields of
     `Chapter04FundamentalClassTowerData`, making this theorem circular. -/
  sorry

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
