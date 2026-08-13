import LastLib.Book04AdelesAndIdeles.Chapter15.Section01MatricesOverTheAdeles
import LastLib.Book04AdelesAndIdeles.Chapter09.Section01TheGlobalModuleAndDegree

namespace LastLib.Book04AdelesAndIdeles.Chapter15

noncomputable section

open Set Filter NumberField
open scoped NNReal RestrictedProduct

/-! ## 15.2. Diagonal rational points and the determinant module -/

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-! ### Principal matrices and principal ideles -/

/-- The diagonal map into the infinite matrix factors. -/
def chapter15ArchimedeanPrincipalMatrix (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) K →*
      Chapter15ArchimedeanMatrixGroup n K where
  toFun g := fun v => Matrix.GeneralLinearGroup.map (algebraMap K v.Completion) g
  map_one' := by
    ext v i j
    simp
  map_mul' g h := by
    ext v i j
    simp

/-- The diagonal map into the finite matrix restricted product. -/
def chapter15FinitePrincipalMatrix (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) K →* Chapter15FiniteMatrixGroup n R K where
  toFun g :=
    ⟨fun v => Matrix.GeneralLinearGroup.map
        (algebraMap K (v.adicCompletion K)) g, by
      sorry⟩
  map_one' := by
    ext v i j
    simp
  map_mul' g h := by
    sorry

/-- The diagonal embedding `GLₙ(K) → GLₙ(𝔸_K)`. -/
def chapter15PrincipalMatrix (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) K →* Chapter15GLnAdeles n R K where
  toFun g :=
    (chapter15ArchimedeanPrincipalMatrix n g,
      chapter15FinitePrincipalMatrix n g)
  map_one' := by
    ext v i j <;> simp [chapter15ArchimedeanPrincipalMatrix,
      chapter15FinitePrincipalMatrix]
  map_mul' g h := by
    sorry

theorem chapter15_principal_matrix_apply_archimedean
    (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) K)
    (v : NumberField.InfinitePlace K) :
    (chapter15PrincipalMatrix (R := R) (K := K) n g).1 v =
      Matrix.GeneralLinearGroup.map (algebraMap K v.Completion) g :=
  rfl

theorem chapter15_principal_matrix_apply_finite
    (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) K)
    (v : Chapter15FinitePlace R) :
    (chapter15PrincipalMatrix n g).2 v =
      Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) g :=
  rfl

theorem chapter15_principal_matrix_injective
    (n : ℕ) [NumberField K] :
    Function.Injective (chapter15PrincipalMatrix (R := R) (K := K) n) := by
  sorry

theorem chapter15_principal_matrix_range_is_discrete
    (n : ℕ) {L : Type*} [Field L] [NumberField L] :
    IsDiscrete (Set.range (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n)) := by
  sorry

/-- The diagonal map into the infinite multiplicative factors. -/
def chapter15ArchimedeanPrincipalIdele :
    Kˣ →* Chapter15ArchimedeanIdeleGroup K where
  toFun x := fun v => Units.map (algebraMap K v.Completion).toMonoidHom x
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    ext v
    simp

/-- The diagonal map into the finite idele restricted product. -/
def chapter15FinitePrincipalIdele :
    Kˣ →* Chapter15FiniteIdeleGroup R K where
  toFun x :=
    ⟨fun v => Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x, by
      sorry⟩
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    sorry

/-- The principal idele map `Kˣ → 𝔸_Kˣ` in the graph-topologized model. -/
def chapter15PrincipalIdele : Kˣ →* Chapter15IdeleGroup R K where
  toFun x := (chapter15ArchimedeanPrincipalIdele x, chapter15FinitePrincipalIdele x)
  map_one' := by
    ext v <;> simp [chapter15ArchimedeanPrincipalIdele,
      chapter15FinitePrincipalIdele]
  map_mul' x y := by
    sorry

theorem chapter15_rank_one_recovers_ideles_principal
    (K : Type*) [Field K] [NumberField K]
    (g : Matrix.GeneralLinearGroup (Fin 1) K) :
    chapter15_rank_one_recovers_ideles K
        (chapter15PrincipalMatrix (R := 𝓞 K) (K := K) 1 g) =
      chapter15PrincipalIdele (R := 𝓞 K) (K := K)
        (chapter15_rank_one_local_gl_is_multiplicative_group K g) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the book's normalized idele module is not a named
Mathlib object.  The structure records the surjective, continuous,
principal-trivial multiplicative interface needed by this chapter. -/
structure Chapter15IdeleModuleData where
  toMonoidHom : Chapter15IdeleGroup R K →* ℝ≥0ˣ
  surjective_toMonoidHom : Function.Surjective toMonoidHom
  principal_eq_one : ∀ x : Kˣ,
    toMonoidHom (chapter15PrincipalIdele (R := R) (K := K) x) = 1
  continuous_toMonoidHom : Continuous toMonoidHom

/- The canonical full-idele model from Chapter 9 supplies the normalized module
once the book-facing graph model is identified with units of the full adele ring. -/
theorem chapter15_idele_group_homeomorph_full_adele_units_principal
    (K : Type*) [Field K] [NumberField K] (x : Kˣ) :
    chapter15_idele_group_homeomorph_full_adele_units (R := 𝓞 K) (K := K)
        (chapter15PrincipalIdele (R := 𝓞 K) (K := K) x) =
      LastLib.Book04AdelesAndIdeles.Chapter09.chapter09PrincipalIdele K x := by
  sorry

def chapter15CanonicalIdeleModuleData
    (K : Type*) [Field K] [NumberField K] :
    Chapter15IdeleModuleData (R := 𝓞 K) (K := K) where
  toMonoidHom :=
    (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModuleHom K).comp
      (chapter15_idele_group_homeomorph_full_adele_units (R := 𝓞 K) (K := K)).toMulEquiv.toMonoidHom
  surjective_toMonoidHom := by
    sorry
  principal_eq_one := by
    intro x
    sorry
  continuous_toMonoidHom := by
    sorry

/- LOCAL_DEPENDENCY_GUESS: the preceding ideles chapters provide the product
formula construction of the normalized idele module.  This existence bridge
keeps the determinant-one API usable before that canonical construction is
reconciled into the shared project namespace. -/
theorem chapter15_idele_module_data_exists
    (K : Type*) [Field K] [NumberField K] :
    Nonempty (Chapter15IdeleModuleData (R := 𝓞 K) (K := K)) := by
  exact ⟨chapter15CanonicalIdeleModuleData K⟩

/-! ### The determinant homomorphism -/

/-- Determinant on the infinite matrix component. -/
def chapter15ArchimedeanDeterminant (n : ℕ) :
    Chapter15ArchimedeanMatrixGroup n K →*
      Chapter15ArchimedeanIdeleGroup K where
  toFun g := fun v => Matrix.GeneralLinearGroup.det (g v)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

/-- Determinant on the finite matrix restricted product. -/
def chapter15FiniteMatrixDeterminant (n : ℕ) :
    Chapter15FiniteMatrixGroup n R K →* Chapter15FiniteIdeleGroup R K :=
  RestrictedProduct.mapAlongMonoidHom
    (R₁ := fun v : Chapter15FinitePlace R =>
      Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
    (R₂ := fun v : Chapter15FinitePlace R => (v.adicCompletion K)ˣ)
    (B₁ := fun v => chapter15FiniteMatrixIntegralSubgroup n v)
    (B₂ := fun v => chapter15FiniteUnitIntegralSubgroup v)
    (f := id) (hf := Filter.tendsto_id)
    (φ := fun _ => Matrix.GeneralLinearGroup.det)
    (hφ := by
      sorry)

/-- The global determinant `GLₙ(𝔸_K) → 𝔸_Kˣ`. -/
def chapter15AdelicDeterminant (n : ℕ) :
    Chapter15GLnAdeles n R K →* Chapter15IdeleGroup R K where
  toFun g :=
    (chapter15ArchimedeanDeterminant n g.1,
      chapter15FiniteMatrixDeterminant n g.2)
  map_one' := by
    ext v <;> simp [chapter15ArchimedeanDeterminant,
      chapter15FiniteMatrixDeterminant]
  map_mul' g h := by
    ext v <;> simp [chapter15ArchimedeanDeterminant,
      chapter15FiniteMatrixDeterminant]

theorem chapter15_adelic_determinant_apply_archimedean
    (n : ℕ) (g : Chapter15GLnAdeles n R K)
    (v : NumberField.InfinitePlace K) :
    (chapter15AdelicDeterminant n g).1 v =
      Matrix.GeneralLinearGroup.det (g.1 v) :=
  rfl

theorem chapter15_adelic_determinant_apply_finite
    (n : ℕ) (g : Chapter15GLnAdeles n R K)
    (v : Chapter15FinitePlace R) :
    (chapter15AdelicDeterminant n g).2 v =
      Matrix.GeneralLinearGroup.det (g.2 v) :=
  rfl

theorem chapter15_adelic_determinant_continuous
    (n : ℕ) [NumberField K] :
    Continuous (chapter15AdelicDeterminant (R := R) (K := K) n) := by
  sorry

theorem chapter15_adelic_determinant_principal
    (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) K) :
    chapter15AdelicDeterminant (R := R) (K := K) n
        (chapter15PrincipalMatrix (R := R) (K := K) n g) =
      chapter15PrincipalIdele (R := R) (K := K)
        (Matrix.GeneralLinearGroup.det g) := by
  sorry

/-! ### The determinant module and the norm-one subgroup -/

/-- The normalized determinant module `g ↦ |det g|_𝔸`. -/
def chapter15AdelicDeterminantModule (n : ℕ) (M : Chapter15IdeleModuleData (R := R) (K := K)) :
    Chapter15GLnAdeles n R K →* ℝ≥0ˣ :=
  M.toMonoidHom.comp (chapter15AdelicDeterminant n)

theorem chapter15_adelic_determinant_module_apply
    (n : ℕ) (M : Chapter15IdeleModuleData (R := R) (K := K))
    (g : Chapter15GLnAdeles n R K) :
    chapter15AdelicDeterminantModule (R := R) (K := K) n M g =
      M.toMonoidHom (chapter15AdelicDeterminant n g) :=
  rfl

theorem chapter15_adelic_determinant_module_continuous
    (n : ℕ) [NumberField K]
    (M : Chapter15IdeleModuleData (R := R) (K := K)) :
    Continuous (chapter15AdelicDeterminantModule (R := R) (K := K) n M) := by
  sorry

theorem chapter15_adelic_determinant_module_surjective
    (n : ℕ) (hn : 0 < n)
    (M : Chapter15IdeleModuleData (R := R) (K := K)) :
    Function.Surjective (chapter15AdelicDeterminantModule (R := R) (K := K) n M) := by
  sorry

theorem chapter15_adelic_determinant_module_principal
    (n : ℕ) (M : Chapter15IdeleModuleData (R := R) (K := K))
    (g : Matrix.GeneralLinearGroup (Fin n) K) :
    chapter15AdelicDeterminantModule (R := R) (K := K) n M
        (chapter15PrincipalMatrix (R := R) (K := K) n g) = 1 := by
  rw [chapter15_adelic_determinant_module_apply,
    chapter15_adelic_determinant_principal,
    M.principal_eq_one]

/-- The determinant-one subgroup `GLₙ(𝔸_K)^1`. -/
def chapter15AdelicMatrixGroupOne (n : ℕ) (M : Chapter15IdeleModuleData (R := R) (K := K)) :
    Subgroup (Chapter15GLnAdeles n R K) :=
  (chapter15AdelicDeterminantModule (R := R) (K := K) n M).ker

theorem chapter15_adelic_matrix_group_one_mem_iff
    (n : ℕ) (M : Chapter15IdeleModuleData (R := R) (K := K))
    (g : Chapter15GLnAdeles n R K) :
    g ∈ chapter15AdelicMatrixGroupOne n M ↔
      chapter15AdelicDeterminantModule (R := R) (K := K) n M g = 1 := by
  exact MonoidHom.mem_ker

theorem chapter15_principal_matrix_mem_group_one
    (n : ℕ) (M : Chapter15IdeleModuleData (R := R) (K := K))
    (g : Matrix.GeneralLinearGroup (Fin n) K) :
    chapter15PrincipalMatrix (R := R) (K := K) n g ∈
      chapter15AdelicMatrixGroupOne n M := by
  exact (MonoidHom.mem_ker).2
    (chapter15_adelic_determinant_module_principal n M g)

/-- The rational subgroup viewed inside the determinant-one subgroup. -/
def chapter15PrincipalMatrixOne (n : ℕ) (M : Chapter15IdeleModuleData (R := R) (K := K)) :
    Matrix.GeneralLinearGroup (Fin n) K →*
      (chapter15AdelicMatrixGroupOne n M : Type _) where
  toFun g := ⟨chapter15PrincipalMatrix n g,
    chapter15_principal_matrix_mem_group_one n M g⟩
  map_one' := by
    apply Subtype.ext
    exact (chapter15PrincipalMatrix (R := R) (K := K) n).map_one
  map_mul' g h := by
    apply Subtype.ext
    exact (chapter15PrincipalMatrix (R := R) (K := K) n).map_mul g h

/-- A finite level, restricted to `GLₙ(𝔸_K)^1`. -/
def chapter15DeterminantOneLevelSubgroup (n : ℕ)
    (M : Chapter15IdeleModuleData (R := R) (K := K))
    (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) :
    Subgroup (chapter15AdelicMatrixGroupOne n M : Type _) :=
  (chapter15GlobalLevelSubgroup n Kf).comap
    (chapter15AdelicMatrixGroupOne n M).subtype

/-- The determinant-one automorphic double quotient. -/
def chapter15DeterminantOneAutomorphicDoubleQuotient
    (n : ℕ) (M : Chapter15IdeleModuleData (R := R) (K := K))
    (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) :=
  Chapter15DoubleQuotient
    (chapter15PrincipalMatrixOne n M).range
    (chapter15DeterminantOneLevelSubgroup n M Kf)

instance chapter15DeterminantOneAutomorphicDoubleQuotient_topologicalSpace
    (n : ℕ) (M : Chapter15IdeleModuleData (R := R) (K := K))
    (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) :
    TopologicalSpace (chapter15DeterminantOneAutomorphicDoubleQuotient n M Kf) := by
  change TopologicalSpace
    (Quotient
      (chapter15DoubleCosetSetoid
        (chapter15PrincipalMatrixOne n M).range
        (chapter15DeterminantOneLevelSubgroup n M Kf)))
  infer_instance

/- The higher-rank noncompactness warning is stated as a genuine topological
negative result, rather than being silently generalized from rank one. -/
theorem chapter15_higher_rank_determinant_one_quotient_not_compact
    (n : ℕ) (hn : 1 < n) {L : Type*} [Field L] [NumberField L] :
    ¬ IsCompact (Set.univ : Set
      (chapter15DeterminantOneAutomorphicDoubleQuotient (R := 𝓞 L) (K := L) n
        (chapter15CanonicalIdeleModuleData L)
        (chapter15StandardFiniteMatrixLevel (R := 𝓞 L) (K := L) n))) := by
  sorry

/-! The source's warning about rank one is recorded here as an API boundary.  No
compactness theorem for `GLₙ(𝔸_K)^1` is introduced; the rank-one compactness
result belongs to the earlier idele module chapter, and higher-rank quotients
retain non-central escape directions. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter15
