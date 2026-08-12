import LastLib.Book06GlobalClassFieldTheory.Chapter03.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter03

noncomputable section

open Filter Set
open scoped BigOperators RestrictedProduct

/-!
## 3.1. Constructing the global norm
-/

def chapter03_local_tensor_product_decomposition
    {K L V : Type*} [Field K] [Field L] [Field V]
    [Algebra K L] [Algebra K V]
    (W : Type*) [Fintype W] (E : W → Type*) [∀ w, CommRing (E w)]
    (T : Chapter03TensorProductDecomposition K L V W E) :
    TensorProduct K L V ≃+* (∀ w, E w) :=
  T.equiv

theorem chapter03_norm_component
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (y : Chapter03Ideles S_L)
    (v : Chapter03Place K) :
    chapter03IdeleNorm N y v =
      (N.above v).prod (fun w => N.localNorm v w (y w)) := by
  sorry

theorem chapter03_norm_output_is_an_idele
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (y : Chapter03Ideles S_L) :
    ∀ᶠ v in cofinite,
      (chapter03IdeleNorm N y v) ∈ (S_K.localFactor v).unit :=
  (chapter03IdeleNorm N y).2

/- The local hypotheses in the prose are exposed together, so later proofs can use the
finite-support normalization without unpacking the restricted-product constructor. -/
theorem chapter03_eventually_unramified_and_integral
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (y : Chapter03Ideles S_L) :
    ∀ᶠ v in cofinite,
      S_K.finitePlace v ∧ N.unramified v ∧
        (∀ w ∈ N.above v, y w ∈ (S_L.localFactor w).unit) ∧
        (∀ w ∈ N.above v,
          N.localNorm v w (y w) ∈ (S_K.localFactor v).unit) := by
  sorry

theorem chapter03_ideleNorm_continuous
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    Continuous (chapter03IdeleNorm N) :=
  (chapter03ContinuousIdeleNorm N).continuous_toFun

theorem chapter03_classNorm_continuous
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) :
    Continuous (chapter03ClassNorm N) :=
  (chapter03ContinuousClassNorm N).continuous_toFun

theorem chapter03_classNorm_principal
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L) (a : Units L) :
    chapter03ClassNorm N
        (QuotientGroup.mk' (chapter03PrincipalSubgroup S_L)
          (chapter03PrincipalIdeleHom S_L a)) =
      QuotientGroup.mk' (chapter03PrincipalSubgroup S_K)
        (chapter03PrincipalIdeleHom S_K (Units.map (Algebra.norm K (S := L)) a)) := by
  rw [chapter03ClassNorm_mk, chapter03_ideleNorm_principal]

theorem chapter03_ideleNorm_module_identity
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {S_K : Chapter03FieldIdeleData K} {S_L : Chapter03FieldIdeleData L}
    (N : Chapter03NormData S_K S_L)
    (A : Chapter03AdelicModuleData N) (y : Chapter03Ideles S_L) :
    A.baseModuleNorm (chapter03IdeleNorm N y) = A.topModuleNorm y :=
  chapter03_ideleNorm_moduleNorm A y

theorem chapter03_ideleNorm_tower_compatibility
    {K L M : Type*} [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsScalarTower K L M]
    {S_K : Chapter03FieldIdeleData K}
    {S_L : Chapter03FieldIdeleData L}
    {S_M : Chapter03FieldIdeleData M}
    (T : Chapter03NormTowerData S_K S_L S_M) :
    (chapter03IdeleNorm T.norm_L_over_K).comp
        (chapter03IdeleNorm T.norm_M_over_L) =
      chapter03IdeleNorm T.norm_M_over_K :=
  chapter03_ideleNorm_transitive T

theorem chapter03_classNorm_tower_compatibility
    {K L M : Type*} [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsScalarTower K L M]
    {S_K : Chapter03FieldIdeleData K}
    {S_L : Chapter03FieldIdeleData L}
    {S_M : Chapter03FieldIdeleData M}
    (T : Chapter03NormTowerData S_K S_L S_M) :
    (chapter03ClassNorm T.norm_L_over_K).comp
        (chapter03ClassNorm T.norm_M_over_L) =
      chapter03ClassNorm T.norm_M_over_K := by
  sorry

end
end LastLib.Book06GlobalClassFieldTheory.Chapter03
