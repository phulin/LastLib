import LastLib.Book04AdelesAndIdeles.Chapter10.Section02TheAdelicNorm

namespace LastLib.Book04AdelesAndIdeles.Chapter10

noncomputable section

open scoped BigOperators NNReal
open Chapter10GlobalNormData

/-! ## 10.3. Compatibility with principal ideles -/

/-- A principal embedding into an idele group. -/
structure Chapter10PrincipalIdeleData
    (G : Type*) (I : Type*) [Group G] [CommGroup I] where
  principal : G →* I
  injective : Function.Injective principal

/-- The subgroup of principal ideles. -/
def chapter10PrincipalSubgroup
    {G I : Type*} [Group G] [CommGroup I]
    (p : G →* I) : Subgroup I :=
  Subgroup.map p ⊤

/-- The idele class group attached to a principal embedding. -/
abbrev chapter10IdeleClassGroup
    {G I : Type*} [Group G] [CommGroup I] (p : G →* I) : Type _ :=
  I ⧸ chapter10PrincipalSubgroup p

theorem chapter10_mem_principal_subgroup_iff
    {G I : Type*} [Group G] [CommGroup I] (p : G →* I) (x : I) :
    x ∈ chapter10PrincipalSubgroup p ↔ ∃ g : G, p g = x := by
  sorry

/-- The norm-one ideles and their image in the idele class group. -/
def chapter10NormOneIdeleSet
    {I : Type*} [CommGroup I] (module : I →* ℝ≥0) : Set I :=
  {x | module x = 1}

def chapter10NormOneIdeleClassSet
    {G I : Type*} [Group G] [CommGroup I]
    (p : G →* I) (module : I →* ℝ≥0) :
    Set (chapter10IdeleClassGroup p) :=
  QuotientGroup.mk' (chapter10PrincipalSubgroup p) ''
    chapter10NormOneIdeleSet module

theorem chapter10_mem_norm_one_idele_set_iff
    {I : Type*} [CommGroup I] (module : I →* ℝ≥0) (x : I) :
    x ∈ chapter10NormOneIdeleSet module ↔ module x = 1 := Iff.rfl

/-- The determinant decomposition at principal components is recorded as the
book-facing compatibility equation. -/
def chapter10PrincipalNormCompatibility
    {G_K G_L I_K I_L : Type*} [Group G_K] [Group G_L]
    [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (fieldNorm : G_L →* G_K) (ideleNorm : I_L →* I_K) : Prop :=
  ideleNorm.comp pL = pK.comp fieldNorm

theorem chapter10_principal_norm_compatibility_iff
    {G_K G_L I_K I_L : Type*} [Group G_K] [Group G_L]
    [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (fieldNorm : G_L →* G_K) (ideleNorm : I_L →* I_K) :
    chapter10PrincipalNormCompatibility pK pL fieldNorm ideleNorm ↔
      ideleNorm.comp pL = pK.comp fieldNorm := Iff.rfl

theorem chapter10_adelic_norm_on_principal_ideles
    {G_K G_L I_K I_L : Type*} [Group G_K] [Group G_L]
    [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (fieldNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL fieldNorm ideleNorm)
    (a : G_L) :
    ideleNorm (pL a) = pK (fieldNorm a) := by
  exact DFunLike.congr_fun hcompat a

/-- The quotient lift is the canonical descent from ideles to idele classes. -/
def chapter10IdeleClassNorm
    {G_K G_L I_K I_L : Type*} [Group G_K] [Group G_L]
    [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (fieldNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL fieldNorm ideleNorm) :
    chapter10IdeleClassGroup pL →* chapter10IdeleClassGroup pK := by
  classical
  refine QuotientGroup.lift (chapter10PrincipalSubgroup pL)
    ((QuotientGroup.mk' (chapter10PrincipalSubgroup pK)).comp ideleNorm) ?_
  intro x hx
  sorry

theorem chapter10_idele_class_norm_mk
    {G_K G_L I_K I_L : Type*} [Group G_K] [Group G_L]
    [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (fieldNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL fieldNorm ideleNorm)
    (x : I_L) :
    chapter10IdeleClassNorm pK pL fieldNorm ideleNorm hcompat
        (QuotientGroup.mk' (chapter10PrincipalSubgroup pL) x) =
      QuotientGroup.mk' (chapter10PrincipalSubgroup pK) (ideleNorm x) := by
  rfl

theorem chapter10_idele_class_norm_continuous
    {G_K G_L I_K I_L : Type*} [Group G_K] [Group G_L]
    [CommGroup I_K] [CommGroup I_L]
    [TopologicalSpace I_K] [TopologicalSpace I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (fieldNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL fieldNorm ideleNorm)
    (hcontinuous : Continuous ideleNorm) :
    Continuous (chapter10IdeleClassNorm pK pL fieldNorm ideleNorm hcompat) := by
  sorry

theorem chapter10_idele_class_norm_preserves_norm_one
    {G_K G_L I_K I_L : Type*} [Group G_K] [Group G_L]
    [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (fieldNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL fieldNorm ideleNorm)
    (moduleK : I_K →* ℝ≥0) (moduleL : I_L →* ℝ≥0)
    (hmodule : ∀ x, moduleK (ideleNorm x) = moduleL x)
    (x : I_L) (hx : x ∈ chapter10NormOneIdeleSet moduleL) :
    chapter10IdeleClassNorm pK pL fieldNorm ideleNorm hcompat
        (QuotientGroup.mk' (chapter10PrincipalSubgroup pL) x) ∈
      chapter10NormOneIdeleClassSet pK moduleK := by
  refine ⟨ideleNorm x, ?_, rfl⟩
  exact (hmodule x).trans hx

theorem chapter10_idele_class_norm_maps_norm_one_classes
    {G_K G_L I_K I_L : Type*} [Group G_K] [Group G_L]
    [CommGroup I_K] [CommGroup I_L]
    (pK : G_K →* I_K) (pL : G_L →* I_L)
    (fieldNorm : G_L →* G_K) (ideleNorm : I_L →* I_K)
    (hcompat : chapter10PrincipalNormCompatibility pK pL fieldNorm ideleNorm)
    (moduleK : I_K →* ℝ≥0) (moduleL : I_L →* ℝ≥0)
    (hmodule : ∀ x, moduleK (ideleNorm x) = moduleL x) :
    chapter10IdeleClassNorm pK pL fieldNorm ideleNorm hcompat ''
        chapter10NormOneIdeleClassSet pL moduleL ⊆
      chapter10NormOneIdeleClassSet pK moduleK := by
  intro x hx
  rcases hx with ⟨x, hx, rfl⟩
  rcases hx with ⟨y, hy, rfl⟩
  exact chapter10_idele_class_norm_preserves_norm_one pK pL fieldNorm ideleNorm
    hcompat moduleK moduleL hmodule y hy

/- LOCAL_DEPENDENCY_GUESS: a later global tower interface should instantiate
the following pointwise transitivity proposition from the local norm tower
identity in Section 10.1. -/
def chapter10AdelicNormTransitivity
    {I_0 I_1 I_2 : Type*} [CommGroup I_0] [CommGroup I_1] [CommGroup I_2]
    (N_10 : I_1 →* I_0) (N_21 : I_2 →* I_1) (N_20 : I_2 →* I_0)
    : Prop :=
  ∀ x, N_20 x = N_10 (N_21 x)

theorem chapter10_adelic_norm_transitive_iff
    {I_0 I_1 I_2 : Type*} [CommGroup I_0] [CommGroup I_1] [CommGroup I_2]
    (N_10 : I_1 →* I_0) (N_21 : I_2 →* I_1) (N_20 : I_2 →* I_0) :
    chapter10AdelicNormTransitivity N_10 N_21 N_20 ↔
      ∀ x, N_20 x = N_10 (N_21 x) := Iff.rfl

theorem chapter10_idele_class_norm_transitive
    {I_0 I_1 I_2 C_0 C_1 C_2 : Type*}
    [CommGroup I_0] [CommGroup I_1] [CommGroup I_2]
    [CommGroup C_0] [CommGroup C_1] [CommGroup C_2]
    (q_0 : I_0 →* C_0) (q_1 : I_1 →* C_1) (q_2 : I_2 →* C_2)
    (N_10 : I_1 →* I_0) (N_21 : I_2 →* I_1) (N_20 : I_2 →* I_0)
    (Q_10 : C_1 →* C_0) (Q_21 : C_2 →* C_1) (Q_20 : C_2 →* C_0)
    (hq10 : Q_10.comp q_1 = q_0.comp N_10)
    (hq21 : Q_21.comp q_2 = q_1.comp N_21)
    (hq20 : Q_20.comp q_2 = q_0.comp N_20)
    (hq2 : Function.Surjective q_2)
    (htrans : chapter10AdelicNormTransitivity N_10 N_21 N_20) :
    Q_20 = Q_10.comp Q_21 := by
  sorry

/-! ### The ideal norm shadow -/

structure Chapter10IdealNormData (ιK ιL : Type*) where
  below : ιL → ιK
  residueDegree : ιL → ℕ
  fiber : ∀ _v : ιK, Finset ιL
  fiber_spec : ∀ v w, w ∈ fiber v ↔ below w = v

/-- The exponent of `p_v` in the ideal norm of an ideal with upstairs
exponents `a_w`. -/
def chapter10IdealNormExponent {ιK ιL : Type*}
    (d : Chapter10IdealNormData ιK ιL) (a : ιL → ℤ) (v : ιK) : ℤ :=
  Finset.sum (d.fiber v) (fun w => (d.residueDegree w : ℤ) * a w)

/-- The norm of a prime `P_w` is the base prime to the residue degree. -/
def chapter10PrimeIdealNormExponent {ιK ιL : Type*}
    (d : Chapter10IdealNormData ιK ιL) (w : ιL) (v : ιK) : ℤ :=
  @ite ℤ (d.below w = v) (Classical.propDecidable (d.below w = v))
    (d.residueDegree w : ℤ) 0

theorem chapter10_prime_ideal_norm_exponent
    {ιK ιL : Type*} (d : Chapter10IdealNormData ιK ιL)
    (w : ιL) (v : ιK) :
    chapter10PrimeIdealNormExponent d w v =
      @ite ℤ (d.below w = v) (Classical.propDecidable (d.below w = v))
        (d.residueDegree w : ℤ) 0 := by
  rfl

theorem chapter10_ideal_norm_valuation_sum
    {ιK ιL : Type*} (d : Chapter10IdealNormData ιK ιL)
    (a : ιL → ℤ) (v : ιK) :
    chapter10IdealNormExponent d a v =
      Finset.sum (d.fiber v) (fun w => (d.residueDegree w : ℤ) * a w) := by
  rfl

theorem chapter10_associated_ideal_of_adelic_norm
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (id : Chapter10IdealNormData ιK ιL)
    (ordK : ∀ v, Kloc v → ℤ) (ordL : ∀ w, Lloc w → ℤ)
    (associatedK : kIdeles d → ιK → ℤ)
    (associatedL : lIdeles d → ιL → ℤ)
    (hK : ∀ x v, associatedK x v = ordK v (x v))
    (hL : ∀ x w, associatedL x w = ordL w (x w))
    (hordK : ∀ v x y, ordK v (x * y) = ordK v x + ordK v y)
    (hlocal : ∀ w y,
      ordK (d.below w) (d.localNorm w y) =
        (id.residueDegree w : ℤ) * ordL w y)
    (hover : ∀ w, d.below w = id.below w)
    (x : lIdeles d) (v : ιK) :
    associatedK (d.adelicNormHom x) v =
      chapter10IdealNormExponent id (associatedL x) v := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter10
