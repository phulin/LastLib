import LastLib.Book04AdelesAndIdeles.Chapter15.Section01MatricesOverTheAdeles
import LastLib.Book04AdelesAndIdeles.Chapter09.Section01TheGlobalModuleAndDegree
import LastLib.Book04AdelesAndIdeles.Chapter05.Section01TheDiagonalEmbedding
import LastLib.Book04AdelesAndIdeles.Chapter05.Section03DiscretenessInTheFullAdeles

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
      have hglobal : ∀ x : Matrix.GeneralLinearGroup (Fin n) K,
          ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
            ∀ i j : Fin n,
              algebraMap K (v.adicCompletion K) (x i j) ∈
                v.adicCompletionIntegers K := by
        intro x
        simp only [Filter.eventually_all]
        intro i j
        exact (algebraMap K (IsDedekindDomain.FiniteAdeleRing R K)
          (x i j)).2
      filter_upwards [hglobal g, hglobal (g⁻¹)] with v hv hvi
      apply (chapter15_finite_integral_matrix_mem_entries_and_inverse_iff
        (R := R) (K := K) n v
          (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) g)).2
      intro i j
      constructor
      · exact hv i j
      · rw [← Matrix.GeneralLinearGroup.map_inv]
        exact hvi i j
    ⟩
  map_one' := by
    ext v i j
    simp
  map_mul' g h := by
    apply Subtype.ext
    funext v
    exact (Matrix.GeneralLinearGroup.map
      (algebraMap K (v.adicCompletion K))).map_mul g h

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
    exact Prod.ext ((chapter15ArchimedeanPrincipalMatrix n).map_mul g h)
      ((chapter15FinitePrincipalMatrix n).map_mul g h)

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
  intro g h hgh
  obtain ⟨v⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply (FaithfulSMul.algebraMap_injective K (v.Completion))
  exact congrArg (fun z : Chapter15GLnAdeles n R K => (z.1 v) i j) hgh

private theorem chapter15_matrix_identity_neighborhood
    (n : ℕ) {L : Type*} [Field L] [NumberField L] :
    ∃ W : Set (Chapter15GLnAdeles n (𝓞 L) L),
      IsOpen W ∧ (1 : Chapter15GLnAdeles n (𝓞 L) L) ∈ W ∧
        W ∩ Set.range (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n) = {1} := by
  classical
  obtain ⟨Uinf, hUinfOpen, hUinfNhds, hUinf⟩ :=
    LastLib.Book04AdelesAndIdeles.Chapter05.chapter05_exists_small_archimedean_neighborhood L
  let U : Set (LastLib.Book04AdelesAndIdeles.Chapter05.Chapter05AdeleRing L) :=
    LastLib.Book04AdelesAndIdeles.Chapter05.chapter05FullZeroNeighborhood L Uinf
  have hUopen : IsOpen U := by
    exact LastLib.Book04AdelesAndIdeles.Chapter05.chapter05_full_zero_neighborhood_is_open
      L Uinf hUinfOpen
  have hUinter : U ∩ Set.range
      (LastLib.Book04AdelesAndIdeles.Chapter05.chapter05Diagonal L) = {0} := by
    exact LastLib.Book04AdelesAndIdeles.Chapter05.chapter05_full_zero_neighborhood_meets_diagonal_only_at_zero
      L Uinf hUinf
  have hUzero : (0 : LastLib.Book04AdelesAndIdeles.Chapter05.Chapter05AdeleRing L) ∈ U := by
    have hUnhds : U ∈ nhds
        (0 : LastLib.Book04AdelesAndIdeles.Chapter05.Chapter05AdeleRing L) := by
      exact LastLib.Book04AdelesAndIdeles.Chapter05.chapter05_full_zero_neighborhood_is_nhds
        L Uinf hUinfNhds
    exact mem_of_mem_nhds hUnhds
  let finiteEntry (i j : Fin n) :
      Chapter15FiniteMatrixGroup n (𝓞 L) L →
        IsDedekindDomain.FiniteAdeleRing (𝓞 L) L :=
    RestrictedProduct.mapAlong
      (R₁ := fun v : Chapter15FinitePlace (𝓞 L) =>
        Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))
      (R₂ := fun v : Chapter15FinitePlace (𝓞 L) => v.adicCompletion L)
      (A₁ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))))
      (A₂ := fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L)))
      (f := fun v => v) Filter.tendsto_id
      (fun _ g => g i j)
      (Filter.Eventually.of_forall (fun v g hg =>
        ((chapter15_finite_integral_matrix_mem_entries_and_inverse_iff
          (R := 𝓞 L) (K := L) n v g).mp hg i j).1))
  have hfiniteEntry_cont (i j : Fin n) : Continuous (finiteEntry i j) := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun v : Chapter15FinitePlace (𝓞 L) =>
        Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))
      (R₂ := fun v : Chapter15FinitePlace (𝓞 L) => v.adicCompletion L)
      (A₁ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L))))
      (A₂ := fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L)))
      (f := fun v => v) Filter.tendsto_id
      (fun v g => g i j)
      (Filter.Eventually.of_forall (fun v g hg =>
        ((chapter15_finite_integral_matrix_mem_entries_and_inverse_iff
          (R := 𝓞 L) (K := L) n v g).mp hg i j).1))
      (fun v =>
        (continuous_apply j).comp
          (Matrix.GeneralLinearGroup.continuous_apply
            (fun g : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L) => g)
            continuous_id i))
  let entry : Chapter15GLnAdeles n (𝓞 L) L → Fin n → Fin n →
      LastLib.Book04AdelesAndIdeles.Chapter05.Chapter05AdeleRing L := fun x i j =>
    (fun v => (x.1 v) i j, finiteEntry i j x.2)
  have hentry_cont (i j : Fin n) :
      Continuous (fun x : Chapter15GLnAdeles n (𝓞 L) L => entry x i j) := by
    change Continuous (fun x :
        Chapter15ArchimedeanMatrixGroup n L × Chapter15FiniteMatrixGroup n (𝓞 L) L =>
      (fun v => (x.1 v) i j, finiteEntry i j x.2))
    have harch : Continuous (fun x :
        Chapter15ArchimedeanMatrixGroup n L × Chapter15FiniteMatrixGroup n (𝓞 L) L =>
        fun v => (x.1 v) i j) := by
      apply continuous_pi
      intro v
      have hv : Continuous (fun x : Chapter15ArchimedeanMatrixGroup n L => x v) :=
        continuous_apply v
      have hv' : Continuous (fun x :
          Chapter15ArchimedeanMatrixGroup n L × Chapter15FiniteMatrixGroup n (𝓞 L) L =>
          x.1 v) :=
        hv.comp (continuous_fst : Continuous (fun x :
          Chapter15ArchimedeanMatrixGroup n L × Chapter15FiniteMatrixGroup n (𝓞 L) L => x.1))
      exact (continuous_apply j).comp
        (Matrix.GeneralLinearGroup.continuous_apply
          (fun x : Chapter15ArchimedeanMatrixGroup n L ×
            Chapter15FiniteMatrixGroup n (𝓞 L) L => x.1 v)
          hv' i)
    exact harch.prodMk (hfiniteEntry_cont i j |>.comp continuous_snd)
  have hentry_principal (g : Matrix.GeneralLinearGroup (Fin n) L) (i j : Fin n) :
      entry (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n g) i j =
        LastLib.Book04AdelesAndIdeles.Chapter05.chapter05Diagonal L (g i j) := by
    apply Prod.ext
    · funext v
      rfl
    · apply Subtype.ext
      funext v
      rfl
  let W : Set (Chapter15GLnAdeles n (𝓞 L) L) :=
    ⋂ i : Fin n, ⋂ j : Fin n,
      (fun x => entry x i j -
        LastLib.Book04AdelesAndIdeles.Chapter05.chapter05Diagonal L
          (if i = j then 1 else 0)) ⁻¹' U
  have hWopen : IsOpen W := by
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact hUopen.preimage ((hentry_cont i j).sub continuous_const)
  have hWone : (1 : Chapter15GLnAdeles n (𝓞 L) L) ∈ W := by
    simp only [W, Set.mem_iInter, Set.mem_preimage]
    intro i j
    rw [show (1 : Chapter15GLnAdeles n (𝓞 L) L) =
      chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n
        (1 : Matrix.GeneralLinearGroup (Fin n) L) by simp, hentry_principal]
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using hUzero
    · simpa [Matrix.one_apply, hij] using hUzero
  have hWinter : W ∩ Set.range
      (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n) = {1} := by
    ext x
    constructor
    · intro hx
      rcases hx.2 with ⟨g, rfl⟩
      have hWx : ∀ i : Fin n, ∀ j : Fin n,
          entry (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n g) i j -
              LastLib.Book04AdelesAndIdeles.Chapter05.chapter05Diagonal L
                (if i = j then 1 else 0) ∈ U := by
        simpa only [W, Set.mem_iInter, Set.mem_preimage] using hx.1
      have hscalar : ∀ i : Fin n, ∀ j : Fin n,
          g i j = if i = j then 1 else 0 := by
        intro i j
        have hz : LastLib.Book04AdelesAndIdeles.Chapter05.chapter05Diagonal L
              (g i j - (if i = j then 1 else 0)) ∈ U := by
          have hw := hWx i j
          rw [hentry_principal] at hw
          simpa only [map_sub] using hw
        have hz' : LastLib.Book04AdelesAndIdeles.Chapter05.chapter05Diagonal L
              (g i j - (if i = j then 1 else 0)) ∈
            U ∩ Set.range
              (LastLib.Book04AdelesAndIdeles.Chapter05.chapter05Diagonal L) := by
          exact ⟨hz, ⟨_, rfl⟩⟩
        rw [hUinter] at hz'
        have hz'' : LastLib.Book04AdelesAndIdeles.Chapter05.chapter05Diagonal L
              (g i j - (if i = j then 1 else 0)) = 0 :=
          Set.mem_singleton_iff.mp hz'
        apply sub_eq_zero.mp
        apply (LastLib.Book04AdelesAndIdeles.Chapter05.chapter05_diagonal_injective L)
        simpa using hz''
      have hg : g = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change g i j = if i = j then 1 else 0
        exact hscalar i j
      rw [hg]
      simp
    · intro hx
      have hx' : x = 1 := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨hWone, ⟨1, by simp⟩⟩
  exact ⟨W, hWopen, hWone, hWinter⟩

theorem chapter15_principal_matrix_range_is_discrete
    (n : ℕ) {L : Type*} [Field L] [NumberField L] :
    IsDiscrete (Set.range (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n)) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨W, hWopen, hWone, hWinter⟩ :=
    chapter15_matrix_identity_neighborhood (L := L) n
  let : Fact (∀ v : Chapter15FinitePlace (𝓞 L),
      IsOpen
        (chapter15FiniteMatrixIntegralSubgroup (R := 𝓞 L) (K := L) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion L)))) :=
    ⟨fun v => chapter15_finite_integral_matrix_group_is_open n v⟩
  let V : Set (Chapter15GLnAdeles n (𝓞 L) L) :=
    (fun y =>
      (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n g)⁻¹ * y) ⁻¹' W
  have hVopen : IsOpen V := by
    exact hWopen.preimage (continuous_const.mul continuous_id)
  have hVmem : chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n g ∈ V := by
    change (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n g)⁻¹ *
        chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n g ∈ W
    simpa using hWone
  have hVinter : V ∩ Set.range
      (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n) =
      {chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n g} := by
    ext y
    constructor
    · rintro ⟨hyV, ⟨h, rfl⟩⟩
      have hz :
          (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n g)⁻¹ *
              chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n h ∈ W := hyV
      have hz' :
          (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n g)⁻¹ *
              chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n h ∈
            W ∩ Set.range (chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n) := by
        refine ⟨hz, ⟨g⁻¹ * h, ?_⟩⟩
        simp [map_mul]
      rw [hWinter] at hz'
      have hz'' := Set.mem_singleton_iff.mp hz'
      apply Set.mem_singleton_iff.mpr
      have hz''' := congrArg
        (fun z => chapter15PrincipalMatrix (R := 𝓞 L) (K := L) n g * z) hz''
      simpa [mul_assoc] using hz'''
    · intro hy
      have hy' := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨hVmem, ⟨g, rfl⟩⟩
  exact ⟨V, hVopen, hVinter⟩

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
      have hglobal (y : K) :
          ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
            algebraMap K (v.adicCompletion K) y ∈ v.adicCompletionIntegers K :=
        (algebraMap K (IsDedekindDomain.FiniteAdeleRing R K) y).2
      filter_upwards [hglobal (x : K), hglobal (x⁻¹ : K)] with v hx hxi
      let y : (v.adicCompletion K)ˣ :=
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x
      have hy : (y : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
        exact hx
      have hyinv : ((y⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
          v.adicCompletionIntegers K := by
        simpa [y] using hxi
      refine ⟨(v.adicCompletionIntegers K).unitsEquivUnitsType
        ⟨y, Submonoid.mem_units_of_val_mem_inv_val_mem _ hy hyinv⟩, ?_⟩
      apply Units.ext
      rfl
    ⟩
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    apply Subtype.ext
    funext v
    exact (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom).map_mul x y

/-- The principal idele map `Kˣ → 𝔸_Kˣ` in the graph-topologized model. -/
def chapter15PrincipalIdele : Kˣ →* Chapter15IdeleGroup R K where
  toFun x := (chapter15ArchimedeanPrincipalIdele x, chapter15FinitePrincipalIdele x)
  map_one' := by
    ext v <;> simp [chapter15ArchimedeanPrincipalIdele,
      chapter15FinitePrincipalIdele]
  map_mul' x y := by
    exact Prod.ext ((chapter15ArchimedeanPrincipalIdele).map_mul x y)
      ((chapter15FinitePrincipalIdele).map_mul x y)

theorem chapter15_rank_one_recovers_ideles_principal
    (K : Type*) [Field K] [NumberField K]
    (g : Matrix.GeneralLinearGroup (Fin 1) K) :
    chapter15_rank_one_recovers_ideles K
        (chapter15PrincipalMatrix (R := 𝓞 K) (K := K) 1 g) =
      chapter15PrincipalIdele (R := 𝓞 K) (K := K)
        (chapter15_rank_one_local_gl_is_multiplicative_group K g) := by
  apply Prod.ext
  · funext v
    change Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (algebraMap K v.Completion) g) =
      Units.map (algebraMap K v.Completion).toMonoidHom
        (Matrix.GeneralLinearGroup.det g)
    exact Matrix.GeneralLinearGroup.map_det
      (algebraMap K v.Completion) g
  · apply Subtype.ext
    funext v
    change Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map
          (algebraMap K (v.adicCompletion K)) g) =
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom
        (Matrix.GeneralLinearGroup.det g)
    exact Matrix.GeneralLinearGroup.map_det
      (algebraMap K (v.adicCompletion K)) g

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
through the underlying-group identification; the graph topology remains the
book-facing topology. -/
theorem chapter15_idele_group_equiv_full_adele_units_principal
    (K : Type*) [Field K] [NumberField K] (x : Kˣ) :
    chapter15_idele_group_equiv_full_adele_units (R := 𝓞 K) (K := K)
        (chapter15PrincipalIdele (R := 𝓞 K) (K := K) x) =
      LastLib.Book04AdelesAndIdeles.Chapter09.chapter09PrincipalIdele K x := by
  rfl

def chapter15CanonicalIdeleModuleData
    (K : Type*) [Field K] [NumberField K] :
    Chapter15IdeleModuleData (R := 𝓞 K) (K := K) where
  toMonoidHom :=
    (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModuleHom K).comp
      (chapter15_idele_group_equiv_full_adele_units (R := 𝓞 K) (K := K)).toMonoidHom
  surjective_toMonoidHom := by
    exact
      LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModule_surjective K |>.comp
        (chapter15_idele_group_equiv_full_adele_units
          (R := 𝓞 K) (K := K)).surjective
  principal_eq_one := by
    intro x
    change LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleModuleHom K
        (chapter15_idele_group_equiv_full_adele_units (R := 𝓞 K) (K := K)
          (chapter15PrincipalIdele (R := 𝓞 K) (K := K) x)) = 1
    rw [chapter15_idele_group_equiv_full_adele_units_principal]
    exact LastLib.Book04AdelesAndIdeles.Chapter09.chapter09PrincipalIdele_module_eq_one x
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
      filter_upwards [] with v
      rintro g ⟨h, rfl⟩
      exact ⟨Matrix.GeneralLinearGroup.det h,
        (Matrix.GeneralLinearGroup.map_det (v.adicCompletionIntegers K).subtype h).symm⟩)

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
  have hφ : ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite,
      MapsTo (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K) → (v.adicCompletion K)ˣ)
        (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v : Set _)
        (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v : Set _) := by
    filter_upwards [] with v
    rintro g ⟨h, rfl⟩
    exact ⟨Matrix.GeneralLinearGroup.det h,
      (Matrix.GeneralLinearGroup.map_det (v.adicCompletionIntegers K).subtype h).symm⟩
  have hfin : Continuous (chapter15FiniteMatrixDeterminant (R := R) (K := K) n) := by
    exact RestrictedProduct.mapAlong_continuous
      (R₁ := fun v : Chapter15FinitePlace R =>
        Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))
      (R₂ := fun v : Chapter15FinitePlace R => (v.adicCompletion K)ˣ)
      (A₁ := fun v =>
        (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v : Set _))
      (A₂ := fun v =>
        (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v : Set _))
      (f := id) Filter.tendsto_id
      (φ := fun _ => Matrix.GeneralLinearGroup.det) hφ
      (fun _ => Matrix.GeneralLinearGroup.continuous_det)
  apply Continuous.prodMk
  · exact continuous_pi fun v =>
      Matrix.GeneralLinearGroup.continuous_det.comp
        (continuous_apply v |>.comp continuous_fst)
  · exact hfin.comp continuous_snd

theorem chapter15_adelic_determinant_principal
    (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) K) :
    chapter15AdelicDeterminant (R := R) (K := K) n
        (chapter15PrincipalMatrix (R := R) (K := K) n g) =
    chapter15PrincipalIdele (R := R) (K := K)
        (Matrix.GeneralLinearGroup.det g) := by
  apply Prod.ext
  · funext v
    change Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (algebraMap K v.Completion) g) =
      Units.map (algebraMap K v.Completion).toMonoidHom
        (Matrix.GeneralLinearGroup.det g)
    exact Matrix.GeneralLinearGroup.map_det (algebraMap K v.Completion) g
  · apply Subtype.ext
    funext v
    change Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) g) =
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom
        (Matrix.GeneralLinearGroup.det g)
    exact Matrix.GeneralLinearGroup.map_det (algebraMap K (v.adicCompletion K)) g

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
  change Continuous (M.toMonoidHom.comp (chapter15AdelicDeterminant n))
  exact (M.continuous_toMonoidHom).comp
    (chapter15_adelic_determinant_continuous (R := R) (K := K) n)

private def chapter15DiagonalUnit (n : ℕ) (i0 : Fin n)
    {A : Type*} [CommRing A] (u : Aˣ) :
    Matrix.GeneralLinearGroup (Fin n) A :=
  ⟨Matrix.diagonal (fun j => if j = i0 then u else 1),
    Matrix.diagonal (fun j => if j = i0 then (u⁻¹ : Aˣ) else 1),
    by
      simp only [Matrix.diagonal_mul_diagonal, mul_ite, ite_mul,
        one_mul, mul_one, Matrix.diagonal_eq_one]
      funext j
      split_ifs <;> simp,
    by
      simp only [Matrix.diagonal_mul_diagonal, mul_ite, ite_mul,
        one_mul, mul_one, Matrix.diagonal_eq_one]
      funext j
      split_ifs <;> simp⟩

theorem chapter15_adelic_determinant_module_surjective
    (n : ℕ) (hn : 0 < n)
    (M : Chapter15IdeleModuleData (R := R) (K := K)) :
    Function.Surjective (chapter15AdelicDeterminantModule (R := R) (K := K) n M) := by
  intro y
  obtain ⟨x, hx⟩ := M.surjective_toMonoidHom y
  let i0 : Fin n := ⟨0, hn⟩
  have hfinite : ∀ v : Chapter15FinitePlace R,
      MapsTo (fun u : (v.adicCompletion K)ˣ =>
        chapter15DiagonalUnit n i0 u)
        (chapter15FiniteUnitIntegralSubgroup (R := R) (K := K) v :
          Set ((v.adicCompletion K)ˣ))
        (chapter15FiniteMatrixIntegralSubgroup (R := R) (K := K) n v :
          Set (Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K))) := by
    intro v u hu
    rcases hu with ⟨w, rfl⟩
    apply (chapter15_finite_integral_matrix_mem_iff
      (R := R) (K := K) n hn v (chapter15DiagonalUnit n i0
        (Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom w))).2
    constructor
    · intro i j
      by_cases hij : i = j
      · subst j
        by_cases hi0 : i = i0 <;>
          simp [chapter15DiagonalUnit, hi0, i0,
            (w : v.adicCompletionIntegers K).property]
      · simp [chapter15DiagonalUnit, hij, i0]
    · refine ⟨w, ?_⟩
      apply Units.ext
      simp [chapter15DiagonalUnit, Matrix.GeneralLinearGroup.det,
        Matrix.det_diagonal, i0]
  let finiteScalar : Chapter15FiniteIdeleGroup R K →
      Chapter15FiniteMatrixGroup n R K :=
    RestrictedProduct.map
      (φ := fun v u => chapter15DiagonalUnit n i0 u)
      (Filter.Eventually.of_forall hfinite)
  let g : Chapter15GLnAdeles n R K :=
    (fun v => chapter15DiagonalUnit n i0 (x.1 v), finiteScalar x.2)
  have hdet : chapter15AdelicDeterminant (R := R) (K := K) n g = x := by
    apply Prod.ext
    · funext v
      change Matrix.GeneralLinearGroup.det
          (chapter15DiagonalUnit n i0 (x.1 v)) = x.1 v
      simp [chapter15DiagonalUnit, Matrix.GeneralLinearGroup.det,
        Matrix.det_diagonal, i0]
    · apply Subtype.ext
      funext v
      change Matrix.GeneralLinearGroup.det
          (chapter15DiagonalUnit n i0 (x.2 v)) = x.2 v
      simp [chapter15DiagonalUnit, Matrix.GeneralLinearGroup.det,
        Matrix.det_diagonal, i0]
  refine ⟨g, ?_⟩
  change M.toMonoidHom (chapter15AdelicDeterminant (R := R) (K := K) n g) = y
  rw [hdet, hx]

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
