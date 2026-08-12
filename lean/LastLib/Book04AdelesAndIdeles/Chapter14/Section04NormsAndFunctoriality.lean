import LastLib.Book04AdelesAndIdeles.Chapter14.Dependencies

/-!
# 14.4. Norms and functoriality
-/

noncomputable section

namespace LastLib.Book04AdelesAndIdeles.Chapter14

theorem chapter14_adelic_norm_module_identity {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) (y : chapter14IdeleGroup L) :
    N.moduleK.module (N.ideleNorm y) = N.moduleL.module y :=
  N.module_compatibility y

def chapter14NormGaloisCompatibility {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L)
    (reciprocityL : chapter14IdeleClassGroup L →*
      chapter14AbelianGaloisGroup L)
    (reciprocityK : chapter14IdeleClassGroup K →*
      chapter14AbelianGaloisGroup K) : Prop :=
  reciprocityK.comp (chapter14NormOnClassGroups N) =
    N.galoisRestriction.comp reciprocityL

def chapter14_norm_and_galois_maps_have_covariant_direction
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :
    chapter14IdeleGroup L →* chapter14IdeleGroup K :=
  N.ideleNorm

theorem chapter14_class_norm_module_identity {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) (x : chapter14IdeleClassGroup L) :
    chapter14ClassModule N.moduleK (chapter14NormOnClassGroups N x) =
      chapter14ClassModule N.moduleL x := by
  sorry

def chapter14NormOneMap {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :
    chapter14NormOneClassSubgroup N.moduleL →*
      chapter14NormOneClassSubgroup N.moduleK := by
  refine
    { toFun := fun x => ⟨chapter14NormOnClassGroups N x, ?_⟩
      map_one' := ?_
      map_mul' := ?_ }
  · change chapter14ClassModule N.moduleK (chapter14NormOnClassGroups N x) = 1
    rw [chapter14_class_norm_module_identity N x]
    exact x.property
  · ext
    simp
  · intro x y
    ext
    simp

theorem chapter14_norm_maps_norm_one_classes {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L)
    {x : chapter14IdeleClassGroup L}
    (hx : x ∈ chapter14NormOneClassSubgroup N.moduleL) :
    chapter14NormOnClassGroups N x ∈ chapter14NormOneClassSubgroup N.moduleK := by
  change chapter14ClassModule N.moduleK (chapter14NormOnClassGroups N x) = 1
  rw [chapter14_class_norm_module_identity N x, hx]

theorem chapter14_norm_one_map_on_compact_class_groups {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L)
    [CompactSpace (chapter14NormOneClassSubgroup N.moduleL)]
    [CompactSpace (chapter14NormOneClassSubgroup N.moduleK)] :
    Nonempty (chapter14NormOneClassSubgroup N.moduleL →*
      chapter14NormOneClassSubgroup N.moduleK) := by
  exact ⟨chapter14NormOneMap N⟩

/-! Ray maps carry a source depth into a target depth; the target depth need not be equal. -/

structure Chapter14RayNormDepthCompatibility {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L)
    (D_L : Chapter14IdeleLevelData L) (R_L : Chapter14RaySubgroupFamily D_L)
    (D_K : Chapter14IdeleLevelData K) (R_K : Chapter14RaySubgroupFamily D_K)
    (mL : Chapter14Modulus L) (mK : Chapter14Modulus K) where
  map : chapter14RayClassGroup D_L R_L mL →* chapter14RayClassGroup D_K R_K mK
  commutes :
    map.comp (chapter14RayClassQuotientMap D_L R_L mL) =
      (chapter14RayClassQuotientMap D_K R_K mK).comp
        (chapter14NormOnClassGroups N)
  sourceDepth : ℕ
  targetDepth : ℕ
  targetDepth_le_sourceDepth : targetDepth ≤ sourceDepth

def chapter14EqualExponentNormClaim (sourceDepth targetDepth : ℕ) : Prop :=
  sourceDepth = targetDepth

def chapter14NormSurjectivityClaim {G H : Type*} [Group G] [Group H]
    (f : G →* H) : Prop :=
  Function.Surjective f

/-!
The structure above intentionally has no field asserting either equal exponents or surjectivity.
Those are additional claims, not formal consequences of the norm construction.
-/

theorem chapter14_ray_norm_depth_is_not_an_equal_exponent_rule
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L)
    (D_L : Chapter14IdeleLevelData L) (R_L : Chapter14RaySubgroupFamily D_L)
    (D_K : Chapter14IdeleLevelData K) (R_K : Chapter14RaySubgroupFamily D_K)
    (mL : Chapter14Modulus L) (mK : Chapter14Modulus K)
    (C : Chapter14RayNormDepthCompatibility N D_L R_L D_K R_K mL mK) :
    C.targetDepth ≤ C.sourceDepth :=
  C.targetDepth_le_sourceDepth

end LastLib.Book04AdelesAndIdeles.Chapter14
