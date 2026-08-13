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
    ext <;> simp [chapter08InfinitePrincipalIdele, chapter08FinitePrincipalIdele]
  map_mul' := by
    intro x y
    ext <;> simp [chapter08InfinitePrincipalIdele, chapter08FinitePrincipalIdele]

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
    exact map_one (chapter08FiniteIdeleIdealMap K)
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
      rcases hx with ⟨a, rfl⟩
      change ClassGroup.mk K
        (chapter08FiniteIdeleIdealMap K (chapter08FinitePrincipalIdele a)) = 1
      rw [chapter08_finite_idele_ideal_principal]
      apply (ClassGroup.mk_eq_one_iff).2
      refine ⟨(a : K), ?_⟩
      simp [coe_toPrincipalIdeal])

theorem chapter08_idele_class_map_surjective
    (K : Type*) [Field K] [NumberField K] :
    Function.Surjective (chapter08IdeleClassMap K) := by
  intro c
  obtain ⟨q, rfl⟩ := (ClassGroup.equiv K).symm.surjective c
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    ((toPrincipalIdeal (Chapter08Integers K) K).range) q
  obtain ⟨x, hx⟩ := chapter08_finite_idele_ideal_surjective K I
  refine ⟨QuotientGroup.mk' (chapter08PrincipalIdeles K) (1, x), ?_⟩
  apply (ClassGroup.equiv K).injective
  simp [chapter08IdeleClassMap, chapter08IdeleIdealHom, hx]
  rfl

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
        rw [← chapter08_finite_idele_ideal_kernel (K := K), MonoidHom.mem_ker]
        rw [chapter08_finite_idele_ideal_principal]
        apply Units.ext
        apply FractionalIdeal.coeToSubmodule_injective
        have hspan : Submodule.span (Chapter08Integers K)
            {((algebraMap (Chapter08Integers K) K) (u : Chapter08Integers K))} = 1 :=
          (Submodule.span_singleton_eq_one_iff).2 ⟨u, rfl⟩
        simpa [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using hspan⟩ )
  map_one' := by
    ext <;> simp [chapter08FinitePrincipalIdele]
  map_mul' := by
    intro x y
    ext <;> simp [chapter08FinitePrincipalIdele]

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
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (chapter08PrincipalIdeles K) q
    have hclass : ClassGroup.mk K
        (chapter08IdeleIdealHom K x) = 1 := by
      simpa [chapter08IdeleClassMap] using hq
    have hclass' := congrArg (ClassGroup.equiv K) hclass
    rw [ClassGroup.equiv_mk, map_one] at hclass'
    let I : Chapter08IdealGroup K := chapter08FiniteIdeleIdealMap K x.2
    have hI : QuotientGroup.mk'
        (toPrincipalIdeal (Chapter08Integers K) K).range I = 1 := by
      simpa [I, chapter08IdeleIdealHom] using hclass'
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hI
    obtain ⟨a, ha⟩ := hI
    let y : Chapter08FiniteIdeles K :=
      x.2 * (chapter08FinitePrincipalIdele a)⁻¹
    have hyideal : chapter08FiniteIdeleIdealMap K y = 1 := by
      simp [y]
      rw [chapter08_finite_idele_ideal_principal]
      rw [ha]
      change I * I⁻¹ = 1
      simp
    have hy : y ∈ chapter08FiniteIntegralUnits := by
      rw [← chapter08_finite_idele_ideal_kernel]
      exact (MonoidHom.mem_ker).2 hyideal
    let z : Chapter08KernelNumerator K :=
      (x.1 * (chapter08InfinitePrincipalIdele a)⁻¹, ⟨y, hy⟩)
    refine ⟨z, ?_⟩
    change QuotientGroup.mk' (chapter08PrincipalIdeles K)
      (chapter08KernelNumeratorEmbedding K z) =
      QuotientGroup.mk' (chapter08PrincipalIdeles K) x
    apply (QuotientGroup.mk'_eq_mk' (chapter08PrincipalIdeles K)).2
    refine ⟨chapter08PrincipalIdeleHom K a, ⟨a, rfl⟩, ?_⟩
    ext
    · simp [z, y, chapter08KernelNumeratorEmbedding,
        chapter08PrincipalIdeleHom, chapter08InfinitePrincipalIdele]
    · simp [z, y, chapter08KernelNumeratorEmbedding,
        chapter08PrincipalIdeleHom, chapter08InfinitePrincipalIdele]
  · rintro ⟨z, rfl⟩
    change chapter08IdeleClassMap K
      (QuotientGroup.mk' (chapter08PrincipalIdeles K)
        (chapter08KernelNumeratorEmbedding K z)) = 1
    change ClassGroup.mk K (chapter08FiniteIdeleIdealMap K z.2.1) = 1
    have hzideal : chapter08FiniteIdeleIdealMap K z.2.1 = 1 := by
      have hzker : (z.2 : Chapter08FiniteIdeles K) ∈
          MonoidHom.ker (chapter08FiniteIdeleIdealMap K) := by
        rw [chapter08_finite_idele_ideal_kernel (K := K)]
        exact z.2.property
      exact (MonoidHom.mem_ker).1 hzker
    rw [hzideal]
    simp

abbrev Chapter08KernelQuotient (K : Type*) [Field K] [NumberField K] :=
  Chapter08KernelNumerator K ⧸ chapter08KernelGlobalUnits K

def chapter08KernelMap (K : Type*) [Field K] [NumberField K] :
    Chapter08KernelQuotient K →* Chapter08IdeleClassGroup K :=
  QuotientGroup.lift (chapter08KernelGlobalUnits K)
    (chapter08KernelIntoIdeleClass K) (by
      intro x hx
      rcases hx with ⟨u, rfl⟩
      let b : Kˣ :=
        Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u
      have heq : chapter08KernelNumeratorEmbedding K
          (chapter08KernelGlobalUnitHom K u) =
          chapter08PrincipalIdeleHom K b := by
        ext <;> rfl
      change QuotientGroup.mk' (chapter08PrincipalIdeles K)
        (chapter08KernelNumeratorEmbedding K
          (chapter08KernelGlobalUnitHom K u)) = 1
      rw [heq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨b, rfl⟩)

theorem chapter08_kernel_map_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (chapter08KernelMap K) := by
  have hglobal : ∀ {c : Kˣ},
      toPrincipalIdeal (Chapter08Integers K) K c = 1 →
        ∃ u : (Chapter08Integers K)ˣ,
          c = Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u := by
    intro c hc
    have hspan : Submodule.span (Chapter08Integers K) {(c : K)} = 1 := by
      have hcoe := congrArg (fun I : Chapter08IdealGroup K =>
        ((I : Chapter08FractionalIdeal K) :
          Submodule (Chapter08Integers K) K)) hc
      simpa [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton] using hcoe
    obtain ⟨u, hu⟩ := (Submodule.span_singleton_eq_one_iff).1 hspan
    refine ⟨u, ?_⟩
    apply Units.ext
    simpa using hu
  have hker : MonoidHom.ker (chapter08KernelIntoIdeleClass K) =
      chapter08KernelGlobalUnits K := by
    ext x
    constructor
    · intro hx
      change chapter08KernelIntoIdeleClass K x = 1 at hx
      change QuotientGroup.mk' (chapter08PrincipalIdeles K)
        (chapter08KernelNumeratorEmbedding K x) = 1 at hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      obtain ⟨a, ha⟩ := hx
      have hfinite := congrArg Prod.snd ha
      change chapter08FinitePrincipalIdele a = x.2.1 at hfinite
      have hxker : x.2.1 ∈ MonoidHom.ker (chapter08FiniteIdeleIdealMap K) := by
        rw [chapter08_finite_idele_ideal_kernel]
        exact x.2.property
      have hxideal : chapter08FiniteIdeleIdealMap K x.2.1 = 1 :=
        (MonoidHom.mem_ker.mp hxker)
      have hpa : toPrincipalIdeal (Chapter08Integers K) K a = 1 := by
        rw [← chapter08_finite_idele_ideal_principal a, hfinite]
        exact hxideal
      obtain ⟨u, hu⟩ := hglobal hpa
      refine ⟨u, ?_⟩
      apply Prod.ext
      · have hfirst := congrArg Prod.fst ha
        change Units.map (algebraMap K (Chapter08InfiniteAdeles K))
            (Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u) = x.1
        change Units.map (algebraMap K (Chapter08InfiniteAdeles K)) a = x.1 at hfirst
        simpa [hu] using hfirst
      · apply Subtype.ext
        apply Units.ext
        have hsecond := congrArg Prod.snd ha
        change chapter08FinitePrincipalIdele a = x.2.1 at hsecond
        have hsecond' := congrArg (fun z : Chapter08FiniteIdeles K =>
          (z : Chapter08FiniteAdeles K)) hsecond
        simpa [chapter08KernelGlobalUnitHom, hu] using hsecond'
    · rintro ⟨u, rfl⟩
      let b : Kˣ :=
        Units.map (algebraMap (Chapter08Integers K) K).toMonoidHom u
      have heq : chapter08KernelNumeratorEmbedding K
          (chapter08KernelGlobalUnitHom K u) =
          chapter08PrincipalIdeleHom K b := by
        ext <;> rfl
      change QuotientGroup.mk' (chapter08PrincipalIdeles K)
        (chapter08KernelNumeratorEmbedding K
          (chapter08KernelGlobalUnitHom K u)) = 1
      rw [heq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨b, rfl⟩
  have hN : chapter08KernelGlobalUnits K ≤
      MonoidHom.ker (chapter08KernelIntoIdeleClass K) := by
    rw [hker]
  have hinj : Function.Injective
      (QuotientGroup.lift (chapter08KernelGlobalUnits K)
        (chapter08KernelIntoIdeleClass K) hN) :=
    (QuotientGroup.injective_lift_iff
      (N := chapter08KernelGlobalUnits K)
      (chapter08KernelIntoIdeleClass K) hN).2 hker.symm
  simpa [chapter08KernelMap] using hinj

theorem chapter08_idele_class_short_exact
    (K : Type*) [Field K] [NumberField K] :
    chapter08IsShortExact (chapter08KernelMap K) (chapter08IdeleClassMap K) := by
  refine ⟨chapter08_kernel_map_injective K, ?_, chapter08_idele_class_map_surjective K⟩
  rw [chapter08IsExact]
  apply le_antisymm
  · rintro q ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (chapter08KernelGlobalUnits K) z
    change chapter08KernelIntoIdeleClass K x ∈
      MonoidHom.ker (chapter08IdeleClassMap K)
    rw [chapter08_idele_class_kernel_eq_kernel_numerator_range]
    exact ⟨x, rfl⟩
  · rintro q hq
    rw [chapter08_idele_class_kernel_eq_kernel_numerator_range] at hq
    obtain ⟨x, rfl⟩ := hq
    exact ⟨QuotientGroup.mk' (chapter08KernelGlobalUnits K) x, rfl⟩

theorem chapter08_idele_class_kernel_map_range
    (K : Type*) [Field K] [NumberField K] :
    MonoidHom.range (chapter08KernelMap K) =
      MonoidHom.ker (chapter08IdeleClassMap K) := by
  rw [chapter08_idele_class_kernel_eq_kernel_numerator_range]
  apply le_antisymm
  · rintro q ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (chapter08KernelGlobalUnits K) z
    exact ⟨x, rfl⟩
  · rintro q ⟨x, rfl⟩
    exact ⟨QuotientGroup.mk' (chapter08KernelGlobalUnits K) x, rfl⟩

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
