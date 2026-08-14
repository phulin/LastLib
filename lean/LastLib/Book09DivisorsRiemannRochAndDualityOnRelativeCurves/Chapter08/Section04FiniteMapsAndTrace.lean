import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Section01TheLocalResidue

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

universe u v

/-! ### 8.4 Finite maps and trace -/

variable (k : Type u) [Field k]

structure Chapter08DifferentialTrace
    (F E : Type v) [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E]
    [IsScalarTower k F E] where
  finite : FiniteDimensional F E
  genericallySeparable : Algebra.IsSeparable F E
  map : Ω[E⁄k] →ₗ[F] Ω[F⁄k]
  agreesWithFieldTrace :
    ∀ a : E, map (KaehlerDifferential.D k E a) =
      KaehlerDifferential.D k F (Algebra.trace F E a)

def chapter08DifferentialTraceMap
    {F E : Type v} [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E]
    [IsScalarTower k F E]
    (T : Chapter08DifferentialTrace k F E) : Ω[E⁄k] →ₗ[F] Ω[F⁄k] :=
  T.map

theorem chapter08_differential_trace_exists
    {F E : Type v} [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E]
    [IsScalarTower k F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Nonempty (Chapter08DifferentialTrace k F E) := by
  sorry

theorem chapter08_finite_map_function_field_trace
    (π : Chapter08FiniteMapOfProperCurves k)
    [IsScalarTower k π.target.carrier.functionField π.source.carrier.functionField] :
    Nonempty (Chapter08DifferentialTrace k
      π.target.carrier.functionField π.source.carrier.functionField) := by
  let finite : FiniteDimensional π.target.carrier.functionField
      π.source.carrier.functionField := π.functionFieldExtension.finite
  let separable : Algebra.IsSeparable π.target.carrier.functionField
      π.source.carrier.functionField := π.functionFieldExtension.separable
  exact @chapter08_differential_trace_exists k _ _ _ _ _ _ _ _ _ finite separable

def Chapter08FiberClosedPoints
    {k : Type u} [Field k]
    (π : Chapter08FiniteMapOfProperCurves k)
    (x : Chapter08ClosedPoint π.target.carrier) :=
  {y : Chapter08ClosedPoint π.source.carrier // π.hom y.1 = x.1}

def chapter08_fiberPoint
    {k : Type u} [Field k]
    (π : Chapter08FiniteMapOfProperCurves k)
    (x : Chapter08ClosedPoint π.target.carrier)
    (y : Chapter08ClosedPoint π.source.carrier)
    (hy : π.hom y.1 = x.1) : Chapter08FiberClosedPoints π x :=
  ⟨y, hy⟩

@[simp] theorem chapter08_fiberPoint_val
    {k : Type u} [Field k]
    (π : Chapter08FiniteMapOfProperCurves k)
    (x : Chapter08ClosedPoint π.target.carrier)
    (y : Chapter08ClosedPoint π.source.carrier)
    (hy : π.hom y.1 = x.1) :
    (chapter08_fiberPoint π x y hy).1 = y :=
  rfl

def chapter08_evaluation_at_one
    {A B : Type v} {ωA : Type u} [CommRing A] [CommRing B] [AddCommGroup ωA]
    [Algebra A B] [Module A ωA] :
    (B →ₗ[A] ωA) →ₗ[A] ωA :=
  { toFun := fun φ => φ 1
    map_add' := by
      intro φ ψ
      simp
    map_smul' := by
      intro a φ
      simp }

structure Chapter08FiniteDualityTrace
    (A B ωA ωB : Type u)
    [CommRing A] [CommRing B] [AddCommGroup ωA] [AddCommGroup ωB]
    [Algebra A B] [Module A ωA] [Module B ωB] [Module A ωB]
    [IsScalarTower A B ωB] where
  finite : Module.Finite A B
  [homModuleB : Module B (B →ₗ[A] ωA)]
  [homModuleB_tower : IsScalarTower A B (B →ₗ[A] ωA)]
  identification : ωB ≃ₗ[B] (B →ₗ[A] ωA)

structure Chapter08FiniteMapResidueData
    (π : Chapter08FiniteMapOfProperCurves k)
    [IsScalarTower k π.target.carrier.functionField π.source.carrier.functionField]
    (T : Chapter08DifferentialTrace k
      π.target.carrier.functionField π.source.carrier.functionField) where
  fiberEnumeration :
    ∀ x : Chapter08ClosedPoint π.target.carrier,
      Finset (Chapter08FiberClosedPoints π x)
  fiberComplete :
    ∀ (x : Chapter08ClosedPoint π.target.carrier)
      (y : Chapter08FiberClosedPoints π x),
      y ∈ fiberEnumeration x
  finiteDualityTrace :
    Chapter08FiniteDualityTrace
      π.target.carrier.functionField π.source.carrier.functionField
      Ω[π.target.carrier.functionField⁄k]
      Ω[π.source.carrier.functionField⁄k]
  differentialTrace_compatibility :
    ∀ η : Ω[π.source.carrier.functionField⁄k],
      T.map η =
        chapter08_evaluation_at_one
          (finiteDualityTrace.identification η)

theorem chapter08_finite_map_residue_data_exists
    (π : Chapter08FiniteMapOfProperCurves k)
    [IsScalarTower k π.target.carrier.functionField π.source.carrier.functionField]
    (T : Chapter08DifferentialTrace k
      π.target.carrier.functionField π.source.carrier.functionField) :
    Nonempty (Chapter08FiniteMapResidueData k π T) := by
  sorry

/- No separability assumption is placed on the individual residue fields. -/
theorem chapter08_finite_map_residue_formula
    (π : Chapter08FiniteMapOfProperCurves k)
    [IsScalarTower k π.target.carrier.functionField π.source.carrier.functionField]
    (T : Chapter08DifferentialTrace k
      π.target.carrier.functionField π.source.carrier.functionField)
    (R : Chapter08FiniteMapResidueData k π T)
    (x : Chapter08ClosedPoint π.target.carrier)
    (η : Ω[π.source.carrier.functionField⁄k]) :
    chapter08CanonicalResidueAt k π.target.toChapter08SmoothIntegralCurve x (T.map η) =
      Finset.sum (R.fiberEnumeration x) (fun y =>
        chapter08CanonicalResidueAt k π.source.toChapter08SmoothIntegralCurve y.1 η) := by
  sorry

def chapter08_finite_duality_trace
    {A B ωA ωB : Type u}
    [CommRing A] [CommRing B] [AddCommGroup ωA] [AddCommGroup ωB]
    [Algebra A B] [Module A ωA] [Module B ωB] [Module A ωB]
    [IsScalarTower A B ωB]
    (_D : Chapter08FiniteDualityTrace A B ωA ωB) :
    ωB →ₗ[A] ωA :=
  letI := _D.homModuleB
  letI := _D.homModuleB_tower
  (chapter08_evaluation_at_one : (B →ₗ[A] ωA) →ₗ[A] ωA).comp
    (_D.identification.restrictScalars A).toLinearMap

structure Chapter08FiniteMapOfCohenMacaulayCurves (k : Type u) [Field k] where
  source : Chapter08CohenMacaulayCurve k
  target : Chapter08CohenMacaulayCurve k
  hom : source.carrier ⟶ target.carrier
  finite : IsFinite hom
  overBase : hom ≫ target.structureMap = source.structureMap

structure Chapter08FiniteMapCohenMacaulayTraceData
    (π : Chapter08FiniteMapOfCohenMacaulayCurves k) where
  [globalSectionsAlgebra :
    Algebra (Γ(π.target.carrier, ⊤)) (Γ(π.source.carrier, ⊤))]
  globalSectionsAlgebra_map :
    algebraMap (Γ(π.target.carrier, ⊤)) (Γ(π.source.carrier, ⊤)) =
      π.hom.appTop.hom
  globalSectionsFinite :
    Module.Finite (Γ(π.target.carrier, ⊤)) (Γ(π.source.carrier, ⊤))
  sourceRelativeDualizingSheaf : π.source.carrier.Modules
  targetRelativeDualizingSheaf : π.target.carrier.Modules
  targetDualizingModule : Type u
  [targetDualizingModuleAddCommGroup : AddCommGroup targetDualizingModule]
  [targetDualizingModuleModule :
    Module (Γ(π.target.carrier, ⊤)) targetDualizingModule]
  targetDualizingModuleEquiv :
    letI : AddCommGroup targetRelativeDualizingSheaf.val.sections :=
      chapter04SectionsAddCommGroup targetRelativeDualizingSheaf
    letI : Module (Γ(π.target.carrier, ⊤)) targetRelativeDualizingSheaf.val.sections :=
      chapter04SectionsModuleOverGlobalSections targetRelativeDualizingSheaf
    targetDualizingModule ≃ₗ[Γ(π.target.carrier, ⊤)]
      targetRelativeDualizingSheaf.val.sections
  sourceDualizingModule : Type u
  [sourceDualizingModuleAddCommGroup : AddCommGroup sourceDualizingModule]
  [sourceDualizingModuleModuleB :
    Module (Γ(π.source.carrier, ⊤)) sourceDualizingModule]
  [sourceDualizingModuleModuleA :
    Module (Γ(π.target.carrier, ⊤)) sourceDualizingModule]
  [sourceDualizingModuleTower :
    IsScalarTower (Γ(π.target.carrier, ⊤)) (Γ(π.source.carrier, ⊤))
      sourceDualizingModule]
  sourceDualizingModuleEquiv :
    letI : AddCommGroup sourceRelativeDualizingSheaf.val.sections :=
      chapter04SectionsAddCommGroup sourceRelativeDualizingSheaf
    letI : Module (Γ(π.source.carrier, ⊤)) sourceRelativeDualizingSheaf.val.sections :=
      chapter04SectionsModuleOverGlobalSections sourceRelativeDualizingSheaf
    sourceDualizingModule ≃ₗ[Γ(π.source.carrier, ⊤)]
      sourceRelativeDualizingSheaf.val.sections
  [homModuleB :
    Module (Γ(π.source.carrier, ⊤))
      (Γ(π.source.carrier, ⊤) →ₗ[Γ(π.target.carrier, ⊤)]
        targetDualizingModule)]
  [homModuleBTower :
    IsScalarTower (Γ(π.target.carrier, ⊤)) (Γ(π.source.carrier, ⊤))
      (Γ(π.source.carrier, ⊤) →ₗ[Γ(π.target.carrier, ⊤)]
        targetDualizingModule)]
  identification :
    sourceDualizingModule ≃ₗ[Γ(π.source.carrier, ⊤)]
      (Γ(π.source.carrier, ⊤) →ₗ[Γ(π.target.carrier, ⊤)]
        targetDualizingModule)

noncomputable def chapter08FiniteMapCohenMacaulayTrace
    (D : Chapter08FiniteMapCohenMacaulayTraceData k π) :
    letI : AddCommGroup D.sourceDualizingModule := D.sourceDualizingModuleAddCommGroup
    letI : AddCommGroup D.targetDualizingModule := D.targetDualizingModuleAddCommGroup
    letI : Module (Γ(π.target.carrier, ⊤)) D.sourceDualizingModule :=
      D.sourceDualizingModuleModuleA
    letI : Module (Γ(π.target.carrier, ⊤)) D.targetDualizingModule :=
      D.targetDualizingModuleModule
    D.sourceDualizingModule →ₗ[Γ(π.target.carrier, ⊤)] D.targetDualizingModule := by
  letI := D.globalSectionsAlgebra
  letI := D.sourceDualizingModuleAddCommGroup
  letI := D.sourceDualizingModuleModuleB
  letI := D.sourceDualizingModuleModuleA
  letI := D.sourceDualizingModuleTower
  letI := D.targetDualizingModuleAddCommGroup
  letI := D.targetDualizingModuleModule
  letI := D.homModuleB
  letI := D.homModuleBTower
  let finiteDuality :
      Chapter08FiniteDualityTrace
        (Γ(π.target.carrier, ⊤)) (Γ(π.source.carrier, ⊤))
        D.targetDualizingModule D.sourceDualizingModule :=
    { finite := D.globalSectionsFinite
      identification := D.identification }
  exact chapter08_finite_duality_trace finiteDuality

theorem chapter08_finite_duality_trace_exists_for_cohen_macaulay_curves
    (π : Chapter08FiniteMapOfCohenMacaulayCurves k) :
    Nonempty (Chapter08FiniteMapCohenMacaulayTraceData k π) := by
  sorry

def Chapter08PurelyInseparableExtension
    (p : ℕ) {F E : Type v} [Field F] [Field E]
    [Fact p.Prime] [CharP F p] [Algebra F E] : Prop :=
  ∀ x : E, ∃ n : ℕ, ∃ a : F,
    x ^ (p ^ n) = algebraMap F E a

def Chapter08PurelyInseparableFieldTraceObstruction
    (p : ℕ) (F E : Type v) [Field F] [Field E]
    [Fact p.Prime] [CharP F p] [Algebra F E] [FiniteDimensional F E] : Prop :=
  Chapter08PurelyInseparableExtension (F := F) (E := E) p ∧ Algebra.trace F E = 0

theorem chapter08_purely_inseparable_field_trace_obstruction_of_nontrivial
    {p : ℕ} {F E : Type v} [Field F] [Field E]
    [Fact p.Prime] [CharP F p] [Algebra F E] [FiniteDimensional F E]
    (hpure : Chapter08PurelyInseparableExtension (F := F) (E := E) p)
    (hnontrivial : ∃ x : E, ∀ a : F, algebraMap F E a ≠ x) :
    Chapter08PurelyInseparableFieldTraceObstruction p F E := by
  refine ⟨hpure, ?_⟩
  have hpure' : IsPurelyInseparable F E := by
    rw [isPurelyInseparable_iff_pow_mem F p]
    intro x
    obtain ⟨n, a, ha⟩ := hpure x
    exact ⟨n, ⟨a, ha.symm⟩⟩
  have hnot : ¬ Algebra.IsSeparable F E := by
    intro hseparable
    obtain ⟨x, hx⟩ := hnontrivial
    have hsurj : Function.Surjective (algebraMap F E) :=
      @IsPurelyInseparable.surjective_algebraMap_of_isSeparable F E _ _ _ hpure'
        hseparable
    obtain ⟨a, ha⟩ := hsurj x
    exact hx a ha
  exact Algebra.trace_eq_zero_of_not_isSeparable hnot

theorem chapter08_finite_duality_trace_is_evaluation_at_one
    {A B ωA ωB : Type u}
    [CommRing A] [CommRing B] [AddCommGroup ωA] [AddCommGroup ωB]
    [Algebra A B] [Module A ωA] [Module B ωB] [Module A ωB]
    [IsScalarTower A B ωB]
    (D : Chapter08FiniteDualityTrace A B ωA ωB) (η : ωB) :
    chapter08_finite_duality_trace D η = D.identification η 1 := by
  rfl

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
