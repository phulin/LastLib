import LastLib.Book04AdelesAndIdeles.Chapter08.Section81

namespace LastLib.Book04AdelesAndIdeles.Chapter08

noncomputable section

open scoped BigOperators nonZeroDivisors RestrictedProduct
open IsDedekindDomain

/-! ## 8.2 Recovering the ideal class group -/

def chapter08InfinitePrincipalIdele {K : Type*} [Field K] [NumberField K]
    (a : Kˣ) : Chapter08InfiniteIdeles K :=
  Units.map (algebraMap K (Chapter08InfiniteAdeles K)) a

def chapter08PrincipalIdeleHom (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Chapter08Ideles K where
  toFun := fun a => (chapter08InfinitePrincipalIdele a, chapter08FinitePrincipalIdele a)
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    sorry

def chapter08PrincipalIdeles (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter08Ideles K) :=
  MonoidHom.range (chapter08PrincipalIdeleHom K)

abbrev Chapter08IdeleClassGroup (K : Type*) [Field K] [NumberField K] :=
  Chapter08Ideles K ⧸ chapter08PrincipalIdeles K

instance chapter08IdeleClassGroupCommGroup
    (K : Type*) [Field K] [NumberField K] :
    CommGroup (Chapter08IdeleClassGroup K) := by
  change CommGroup (Chapter08Ideles K ⧸ chapter08PrincipalIdeles K)
  infer_instance

def chapter08IdeleIdealHom (K : Type*) [Field K] [NumberField K] :
    Chapter08Ideles K →* Chapter08IdealGroup K where
  toFun := fun x => chapter08FiniteIdeleIdealMap K x.2
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    exact map_mul (chapter08FiniteIdeleIdealMap K) x.2 y.2

theorem chapter08_idele_ideal_map_apply
    {K : Type*} [Field K] [NumberField K]
    (x : Chapter08Ideles K) :
    chapter08IdeleIdealHom K x = chapter08FiniteIdeleIdealMap K x.2 :=
  rfl

def chapter08IdeleClassMap (K : Type*) [Field K] [NumberField K] :
    Chapter08IdeleClassGroup K →* Chapter08OrdinaryClassGroup K :=
  QuotientGroup.lift (chapter08PrincipalIdeles K)
    ((ClassGroup.mk K).comp (chapter08IdeleIdealHom K)) (by
      intro x hx
      sorry)

theorem chapter08_idele_class_map_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08IdeleClassMap K) := by
  sorry

/-! The kernel is the archimedean unit group times the finite integral unit group, modulo global
units.  The product below is a genuine product group; no factor is silently identified with the
other. -/

abbrev Chapter08KernelNumerator (K : Type*) [Field K] [NumberField K] :=
  Chapter08InfiniteIdeles K × chapter08FiniteIntegralUnits (K := K)

def chapter08KernelNumeratorEmbedding (K : Type*) [Field K] [NumberField K] :
    Chapter08KernelNumerator K →* Chapter08Ideles K where
  toFun := fun x => (x.1, x.2.1)
  map_one' := by
    rfl
  map_mul' := by
    intro x y
    rfl

def chapter08KernelGlobalUnitHom (K : Type*) [Field K] [NumberField K] :
    (Chapter08Integers K)ˣ →* Chapter08KernelNumerator K where
  toFun := fun u =>
    ( Units.map (algebraMap K (Chapter08InfiniteAdeles K))
        (Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u),
      ⟨chapter08FinitePrincipalIdele
          (Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u), by
        sorry⟩ )
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    sorry

def chapter08KernelGlobalUnits (K : Type*) [Field K] [NumberField K] :
    Subgroup (Chapter08KernelNumerator K) :=
  MonoidHom.range (chapter08KernelGlobalUnitHom K)

def chapter08KernelIntoIdeleClass (K : Type*) [Field K] [NumberField K] :
    Chapter08KernelNumerator K →* Chapter08IdeleClassGroup K :=
  (QuotientGroup.mk' (chapter08PrincipalIdeles K)).comp
    (chapter08KernelNumeratorEmbedding K)

theorem chapter08_idele_class_kernel_eq_kernel_numerator_range
    (K : Type*) [Field K] [NumberField K] :
    MonoidHom.ker (chapter08IdeleClassMap K) =
      MonoidHom.range (chapter08KernelIntoIdeleClass K) := by
  sorry

abbrev Chapter08KernelQuotient (K : Type*) [Field K] [NumberField K] :=
  Chapter08KernelNumerator K ⧸ chapter08KernelGlobalUnits K

def chapter08KernelMap (K : Type*) [Field K] [NumberField K] :
    Chapter08KernelQuotient K →* Chapter08IdeleClassGroup K :=
  QuotientGroup.lift (chapter08KernelGlobalUnits K)
    (chapter08KernelIntoIdeleClass K) (by
      intro x hx
      sorry)

theorem chapter08_kernel_map_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (chapter08KernelMap K) := by
  sorry

theorem chapter08_idele_class_short_exact
    (K : Type*) [Field K] [NumberField K] :
    chapter08IsShortExact (chapter08KernelMap K) (chapter08IdeleClassMap K) := by
  refine ⟨chapter08_kernel_map_injective K, ?_, chapter08_idele_class_map_surjective K⟩
  sorry

theorem chapter08_idele_class_kernel_map_range
    (K : Type*) [Field K] [NumberField K] :
    MonoidHom.range (chapter08KernelMap K) =
      MonoidHom.ker (chapter08IdeleClassMap K) := by
  sorry

noncomputable def chapter08IdeleClassQuotientEquivClassGroup
    (K : Type*) [Field K] [NumberField K] :
    (Chapter08IdeleClassGroup K ⧸ MonoidHom.range (chapter08KernelMap K)) ≃*
      Chapter08OrdinaryClassGroup K :=
  QuotientGroup.liftEquiv (MonoidHom.range (chapter08KernelMap K))
    (chapter08_idele_class_map_surjective K)
    (chapter08_idele_class_kernel_map_range K)

theorem chapter08_idele_class_quotient_is_class_group
    (K : Type*) [Field K] [NumberField K] :
    Nonempty
      ((Chapter08IdeleClassGroup K ⧸ MonoidHom.range (chapter08KernelMap K)) ≃*
        Chapter08OrdinaryClassGroup K) := by
  exact ⟨chapter08IdeleClassQuotientEquivClassGroup K⟩

/-! The finite-idele map is unchanged when the infinite coordinate varies. -/

theorem chapter08_idele_ideal_map_ignores_infinite
    {K : Type*} [Field K] [NumberField K]
    {x y : Chapter08Ideles K} (h : x.2 = y.2) :
    chapter08IdeleIdealHom K x = chapter08IdeleIdealHom K y := by
  rw [chapter08_idele_ideal_map_apply, chapter08_idele_ideal_map_apply, h]

end

end LastLib.Book04AdelesAndIdeles.Chapter08
