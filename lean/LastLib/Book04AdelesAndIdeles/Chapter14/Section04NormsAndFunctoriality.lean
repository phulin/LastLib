import LastLib.Book04AdelesAndIdeles.Chapter14.Dependencies

/-!
# 14.4. Norms and functoriality
-/

noncomputable section

namespace LastLib.Book04AdelesAndIdeles.Chapter14

theorem chapter14_adelic_norm_module_identity {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) (y : chapter14IdeleGroup L) :
    Chapter09.chapter09IdeleModuleHom K (N.ideleNorm y) =
      Chapter09.chapter09IdeleModuleHom L y :=
  N.module_compatibility y

theorem chapter14_adelic_norm_is_continuous {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :
    Continuous N.ideleNorm :=
  N.ideleNorm_continuous

theorem chapter14_class_norm_is_continuous {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :
    Continuous (chapter14NormOnClassGroups N) := by
  sorry

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
    chapter14ClassModule K (chapter14NormOnClassGroups N x) =
      chapter14ClassModule L x := by
  sorry

def chapter14NormOneMap {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L) :
    chapter14NormOneClassSubgroup L →*
      chapter14NormOneClassSubgroup K := by
  refine
    { toFun := fun x => ⟨chapter14NormOnClassGroups N x, ?_⟩
      map_one' := ?_
      map_mul' := ?_ }
  · change chapter14ClassModule K (chapter14NormOnClassGroups N x) = 1
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
    (hx : x ∈ chapter14NormOneClassSubgroup L) :
    chapter14NormOnClassGroups N x ∈ chapter14NormOneClassSubgroup K := by
  change chapter14ClassModule K (chapter14NormOnClassGroups N x) = 1
  rw [chapter14_class_norm_module_identity N x, hx]

/-! Ray maps carry a source depth into a target depth; the target depth need not be equal. -/

structure Chapter14RayNormDepthCompatibility {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (N : Chapter14AdelicNormInterface K L)
    (mL : Chapter14Modulus L) (mK : Chapter14Modulus K) where
  map : chapter14RayClassGroup mL →* chapter14RayClassGroup mK
  commutes :
    map.comp (chapter14RayClassQuotientMap mL) =
      (chapter14RayClassQuotientMap mK).comp
        (chapter14NormOnClassGroups N)

def chapter14EqualExponentNormClaim (sourceDepth targetDepth : ℕ) : Prop :=
  sourceDepth = targetDepth

def chapter14NormSurjectivityClaim {G H : Type*} [Group G] [Group H]
    (f : G →* H) : Prop :=
  Function.Surjective f

/-!
The structure above intentionally has no field asserting either equal exponents or surjectivity.
Those are additional claims, not formal consequences of the norm construction.
-/


end LastLib.Book04AdelesAndIdeles.Chapter14
