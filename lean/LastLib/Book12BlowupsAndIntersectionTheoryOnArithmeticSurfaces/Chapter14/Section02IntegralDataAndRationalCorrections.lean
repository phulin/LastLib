import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14.Section01SolvingTheBalancingEquations

/-!
# Book 12, Chapter 14, §14.2: integral data and rational corrections
-/

noncomputable section

open scoped BigOperators

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14

/-! ## The primitive multiplicity vector -/

def chapter14MultiplicityGcd {r : ℕ} (F : Chapter14FiberMatrix r) : ℕ :=
  (Finset.univ : Finset (Fin r)).gcd
    (fun i => (F.multiplicity i).natAbs)

def chapter14PrimitiveMultiplicity {r : ℕ} (F : Chapter14FiberMatrix r) :
    Chapter14IntegralVector r :=
  fun i => F.multiplicity i / (chapter14MultiplicityGcd F : ℤ)

def chapter14PrimitiveMultiplicityRat {r : ℕ} (F : Chapter14FiberMatrix r) :
    Chapter14RationalVector r :=
  fun i => (chapter14PrimitiveMultiplicity F i : ℚ)

def chapter14NonPrimitiveFiberSubmodule {r : ℕ} (F : Chapter14FiberMatrix r) :
    Submodule ℤ (Chapter14IntegralVector r) :=
  Submodule.span ℤ {F.multiplicity}

abbrev Chapter14NonPrimitiveFiberQuotient {r : ℕ}
    (F : Chapter14FiberMatrix r) :=
  (Chapter14IntegralVector r) ⧸ chapter14NonPrimitiveFiberSubmodule F

theorem chapter14_multiplicity_gcd_pos
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    0 < chapter14MultiplicityGcd F := by
  sorry

theorem chapter14_multiplicity_is_gcd_smul_primitive
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    ∀ i, F.multiplicity i =
      (chapter14MultiplicityGcd F : ℤ) * chapter14PrimitiveMultiplicity F i := by
  sorry

theorem chapter14_primitive_multiplicity_is_integral
    {r : ℕ} (F : Chapter14FiberMatrix r) (i : Fin r) :
    (chapter14PrimitiveMultiplicity F i : ℚ) =
      (F.multiplicity i : ℚ) / chapter14MultiplicityGcd F := by
  sorry

theorem chapter14_nonprimitive_quotient_has_spurious_torsion
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (hg : 1 < chapter14MultiplicityGcd F) :
    ∃ x : Chapter14NonPrimitiveFiberQuotient F,
      x ≠ 0 ∧
        (chapter14MultiplicityGcd F : ℤ) • x = 0 := by
  sorry

/-! ## Integral kernel and degree-zero lattices -/

def chapter14PrimitiveFiberSubmodule {r : ℕ} (F : Chapter14FiberMatrix r) :
    Submodule ℤ (Chapter14IntegralVector r) :=
  Submodule.span ℤ {chapter14PrimitiveMultiplicity F}

def chapter14IntegralDegreeZeroLattice {r : ℕ} (F : Chapter14FiberMatrix r) :
    Submodule ℤ (Chapter14IntegralVector r) where
  carrier := {d | chapter14IntegralCompatibility F d}
  zero_mem' := by
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

theorem chapter14_integral_kernel_is_primitive_fiber
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (v : Chapter14IntegralVector r) :
    chapter14MatrixVec F.matrix v = 0 ↔
      ∃ z : ℤ, v = z • chapter14PrimitiveMultiplicity F := by
  sorry

theorem chapter14_primitive_fiber_submodule_eq_integral_kernel
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    chapter14PrimitiveFiberSubmodule F =
      LinearMap.ker (by
        refine
          { toFun := chapter14MatrixVec F.matrix
            map_add' := by sorry
            map_smul' := by sorry } :
            (Chapter14IntegralVector r) →ₗ[ℤ]
              (Chapter14IntegralVector r)) := by
  sorry

theorem chapter14_integral_matrix_image_is_degree_zero
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (v : Chapter14IntegralVector r) :
    chapter14IntegralCompatibility F (chapter14MatrixVec F.matrix v) := by
  sorry

def chapter14IntegralMatrixLinearMap {r : ℕ} (F : Chapter14FiberMatrix r) :
    (Chapter14IntegralVector r) →ₗ[ℤ] (Chapter14IntegralVector r) :=
  { toFun := chapter14MatrixVec F.matrix
    map_add' := by
      sorry
    map_smul' := by
      sorry }

def chapter14IntegralMatrixToDegreeZero {r : ℕ} (F : Chapter14FiberMatrix r) :
    (Chapter14IntegralVector r) →ₗ[ℤ] chapter14IntegralDegreeZeroLattice F :=
  { toFun := fun v =>
      ⟨chapter14MatrixVec F.matrix v,
        chapter14_integral_matrix_image_is_degree_zero F v⟩
    map_add' := by
      sorry
    map_smul' := by
      sorry }

abbrev Chapter14IntegralFiberQuotient {r : ℕ} (F : Chapter14FiberMatrix r) :=
  (Chapter14IntegralVector r) ⧸ chapter14PrimitiveFiberSubmodule F

/-!
The quotient map is exposed through a small record so that the factorization
identity remains available even when the pinned quotient API changes its
constructor name.
-/
structure Chapter14IntegralMatrixQuotientMapData
    {r : ℕ} (F : Chapter14FiberMatrix r) where
  map : Chapter14IntegralFiberQuotient F →ₗ[ℤ]
    chapter14IntegralDegreeZeroLattice F
  factorization : ∀ v,
    map (Submodule.mkQ (chapter14PrimitiveFiberSubmodule F) v) =
      chapter14IntegralMatrixToDegreeZero F v

theorem chapter14_integral_matrix_quotient_map_exists
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    Nonempty (Chapter14IntegralMatrixQuotientMapData F) := by
  sorry

noncomputable def chapter14IntegralMatrixQuotientMap
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    Chapter14IntegralMatrixQuotientMapData F :=
  Classical.choice (chapter14_integral_matrix_quotient_map_exists F)

theorem chapter14IntegralMatrixQuotientMap_factorization
    {r : ℕ} (F : Chapter14FiberMatrix r) (v : Chapter14IntegralVector r) :
    (chapter14IntegralMatrixQuotientMap F).map
        (Submodule.mkQ (chapter14PrimitiveFiberSubmodule F) v) =
      chapter14IntegralMatrixToDegreeZero F v := by
  exact (chapter14IntegralMatrixQuotientMap F).factorization v

/-! ## Finite cokernel and rank statements -/

abbrev Chapter14IntegralMatrixCokernel {r : ℕ} (F : Chapter14FiberMatrix r) :=
  (chapter14IntegralDegreeZeroLattice F) ⧸
    Submodule.range (chapter14IntegralMatrixQuotientMap F).map

def chapter14FreeAbelianRank (A : Type*) [AddCommGroup A]
    [Module ℤ A] (n : ℕ) : Prop :=
  Nonempty (Basis (Fin n) ℤ A)

theorem chapter14_integral_matrix_quotient_source_free_rank
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    chapter14FreeAbelianRank (Chapter14IntegralFiberQuotient F) (r - 1) := by
  sorry

theorem chapter14_integral_degree_zero_lattice_free_rank
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    chapter14FreeAbelianRank (chapter14IntegralDegreeZeroLattice F) (r - 1) := by
  sorry

theorem chapter14_integral_matrix_quotient_map_has_finite_cokernel
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    Finite (Chapter14IntegralMatrixCokernel F) := by
  sorry

/-! ## Rationalization -/

def chapter14RationalKernelSubmodule {r : ℕ} (F : Chapter14FiberMatrix r) :
    Submodule ℚ (Chapter14RationalVector r) :=
  Submodule.span ℚ {chapter14FiberMultiplicityRat F}

def chapter14RationalDegreeZeroLattice {r : ℕ} (F : Chapter14FiberMatrix r) :
    Submodule ℚ (Chapter14RationalVector r) where
  carrier := {d | chapter14RationalCompatibility F d}
  zero_mem' := by
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

structure Chapter14RationalizedMatrixEquivalence
    {r : ℕ} (F : Chapter14FiberMatrix r) where
  equivalence :
    (Chapter14RationalVector r) ⧸ chapter14RationalKernelSubmodule F ≃ₗ[ℚ]
      chapter14RationalDegreeZeroLattice F
  factorization : ∀ v,
    equivalence (Submodule.mkQ (chapter14RationalKernelSubmodule F) v) =
      ⟨chapter14MatrixVec (chapter14FiberRationalMatrix F) v, by sorry⟩

theorem chapter14_rationalized_matrix_map_isomorphism_exists
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    Nonempty (Chapter14RationalizedMatrixEquivalence F) := by
  sorry

noncomputable def chapter14RationalizedMatrixEquivalence
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    Chapter14RationalizedMatrixEquivalence F :=
  Classical.choice (chapter14_rationalized_matrix_map_isomorphism_exists F)

theorem chapter14_rationalized_matrix_map_isomorphism
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    Nonempty ((Chapter14RationalVector r) ⧸ chapter14RationalKernelSubmodule F ≃ₗ[ℚ]
      chapter14RationalDegreeZeroLattice F) := by
  exact ⟨(chapter14RationalizedMatrixEquivalence F).equivalence⟩

/-! ## Cofactors and denominator control -/

noncomputable def chapter14PrincipalCofactor {r : ℕ}
    (F : Chapter14FiberMatrix r) (i₀ : Fin r) : ℤ := by
  classical
  exact Matrix.det (F.matrix.submatrix
    (fun i : {j : Fin r // j ≠ i₀} => i.1)
    (fun j : {j : Fin r // j ≠ i₀} => j.1))

def chapter14IntegralMultipleOfRationalVector {r : ℕ}
    (n : ℕ) (v : Chapter14RationalVector r) : Prop :=
  ∀ i, ∃ z : ℤ, (n : ℚ) * v i = z

theorem chapter14_nonzero_principal_cofactor_exists
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    ∃ i₀, chapter14PrincipalCofactor F i₀ ≠ 0 := by
  sorry

theorem chapter14_denominators_are_controlled_by_a_cofactor
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (d : Chapter14RationalVector r)
    (hd : chapter14RationalCompatibility F d)
    (v : Chapter14RationalVector r)
    (hv : chapter14MatrixVec (chapter14FiberRationalMatrix F) v = -d) :
    ∃ i₀, chapter14PrincipalCofactor F i₀ ≠ 0 ∧
      chapter14IntegralMultipleOfRationalVector
        (Int.natAbs (chapter14PrincipalCofactor F i₀)) v := by
  sorry

/- The spanning-tree reformulation is restricted to the graph-Laplacian
case; a general symmetric component matrix has cofactors but no spanning-tree
determinant. -/
structure Chapter14WeightedGraphLaplacianCertificate
    {r : ℕ} (F : Chapter14FiberMatrix r) where
  is_graph_laplacian : Prop
  weighted_spanning_tree_determinant : ℤ
  matrix_tree_identity :
    ∀ i₀, chapter14PrincipalCofactor F i₀ =
      weighted_spanning_tree_determinant

theorem chapter14_graph_laplacian_tree_determinant_controls_denominators
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (C : Chapter14WeightedGraphLaplacianCertificate F)
    (hdet : C.weighted_spanning_tree_determinant ≠ 0)
    (d : Chapter14RationalVector r)
    (hd : chapter14RationalCompatibility F d)
    (v : Chapter14RationalVector r)
    (hv : chapter14MatrixVec (chapter14FiberRationalMatrix F) v = -d) :
    chapter14IntegralMultipleOfRationalVector
      (Int.natAbs C.weighted_spanning_tree_determinant) v := by
  sorry

/-! ## The two-component calculation -/

def chapter14TwoComponentMatrix (q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 0 then if j = 0 then -q else q
    else if j = 0 then q else -q

def chapter14TwoComponentVector (a : ℤ) : Chapter14IntegralVector 2 :=
  fun i => if i = 0 then a else -a

theorem chapter14_two_component_correction_difference
    (q : ℤ) (hq : 0 < q) (a : ℤ)
    (v : Chapter14RationalVector 2)
    (hv : chapter14MatrixVec (fun i j => (chapter14TwoComponentMatrix q i j : ℚ)) v =
      -(fun i => (chapter14TwoComponentVector a i : ℚ))) :
    v 0 - v 1 = (a : ℚ) / q := by
  sorry

theorem chapter14_two_component_integral_correction_iff
    (q : ℤ) (hq : 0 < q) (a : ℤ) :
    (∃ v : Chapter14IntegralVector 2,
      chapter14MatrixVec (chapter14TwoComponentMatrix q) v =
        -chapter14TwoComponentVector a) ↔ q ∣ a := by
  sorry

theorem chapter14_two_component_no_integral_correction_of_not_dvd
    (q : ℤ) (hq : 0 < q) (a : ℤ) (ha : ¬ q ∣ a) :
    ¬ ∃ v : Chapter14IntegralVector 2,
      chapter14MatrixVec (chapter14TwoComponentMatrix q) v =
        -chapter14TwoComponentVector a := by
  exact fun h => ha ((chapter14_two_component_integral_correction_iff q hq a).mp h)

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14
