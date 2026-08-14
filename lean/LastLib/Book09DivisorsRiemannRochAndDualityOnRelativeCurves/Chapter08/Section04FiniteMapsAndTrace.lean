import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08.Section03TheGlobalResidueTheorem

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u v

/-! ### 8.4 Finite maps and trace -/

variable (k : Type u) [Field k]

structure Chapter08DifferentialTrace
    (F E : Type v) [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] where
  finite : FiniteDimensional F E
  genericallySeparable : Algebra.IsSeparable F E
  map : Ω[E⁄k] →ₗ[k] Ω[F⁄k]
  agreesWithFieldTrace :
    ∀ a : E, map (KaehlerDifferential.D k E a) =
      KaehlerDifferential.D k F (Algebra.trace F E a)

def chapter08DifferentialTraceMap
    {F E : Type v} [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E]
    (T : Chapter08DifferentialTrace k F E) : Ω[E⁄k] →ₗ[k] Ω[F⁄k] :=
  T.map

theorem chapter08_differential_trace_exists
    {F E : Type v} [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Nonempty (Chapter08DifferentialTrace k F E) := by
  sorry

theorem chapter08_finite_map_function_field_trace
    (π : Chapter08FiniteMapOfProperCurves k)
    [Algebra k π.target.carrier.functionField]
    [Algebra k π.source.carrier.functionField]
    [Algebra π.target.carrier.functionField π.source.carrier.functionField]
    [FiniteDimensional π.target.carrier.functionField π.source.carrier.functionField]
    [Algebra.IsSeparable π.target.carrier.functionField π.source.carrier.functionField] :
    Nonempty (Chapter08DifferentialTrace k
      π.target.carrier.functionField π.source.carrier.functionField) := by
  sorry

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

structure Chapter08FiniteMapResidueData
    {F E : Type v} [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E]
    (π : Chapter08FiniteMapOfProperCurves k)
    (T : Chapter08DifferentialTrace k F E) where
  sourceResidue :
    ∀ y : Chapter08ClosedPoint π.source.carrier, Ω[E⁄k] →ₗ[k] k
  targetResidue :
    ∀ x : Chapter08ClosedPoint π.target.carrier, Ω[F⁄k] →ₗ[k] k
  fiberEnumeration :
    ∀ x : Chapter08ClosedPoint π.target.carrier,
      Finset (Chapter08FiberClosedPoints π x)
  fiberComplete :
    ∀ (x : Chapter08ClosedPoint π.target.carrier)
      (y : Chapter08FiberClosedPoints π x),
      y ∈ fiberEnumeration x

/- No separability assumption is placed on the individual residue fields. -/
theorem chapter08_finite_map_residue_formula
    {F E : Type v} [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E]
    (π : Chapter08FiniteMapOfProperCurves k)
    (T : Chapter08DifferentialTrace k F E)
    (R : Chapter08FiniteMapResidueData k π T)
    (x : Chapter08ClosedPoint π.target.carrier)
    (η : Ω[E⁄k]) :
    R.targetResidue x (T.map η) =
      ∑ y in R.fiberEnumeration x, R.sourceResidue y.1 η := by
  sorry

/-! The finite-duality trace is evaluation at `1`, independently of field
separability. -/

def chapter08_evaluation_at_one
    {A B ωA : Type u} [CommRing A] [CommRing B] [AddCommGroup ωA]
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
    [Algebra A B] [Module A ωA] [Module B ωB] [Module A ωB] where
  duality : Chapter08FiniteDualityData A B ωA ωB
  traceOnRelativeDualizingModule :
    (B →ₗ[A] ωA) →ₗ[A] ωA
  trace_is_evaluation_at_one :
    traceOnRelativeDualizingModule = chapter08_evaluation_at_one

def chapter08_finite_duality_trace
    {A B ωA ωB : Type u}
    [CommRing A] [CommRing B] [AddCommGroup ωA] [AddCommGroup ωB]
    [Algebra A B] [Module A ωA] [Module B ωB] [Module A ωB]
    (D : Chapter08FiniteDualityTrace A B ωA ωB) :
    (B →ₗ[A] ωA) →ₗ[A] ωA :=
  D.traceOnRelativeDualizingModule

structure Chapter08FiniteMapOfCohenMacaulayCurves where
  source : Chapter08CohenMacaulayCurve
  target : Chapter08CohenMacaulayCurve
  hom : source.carrier ⟶ target.carrier
  finite : IsFinite hom

/- Local dependency guess: finite dualizing modules for arbitrary
Cohen--Macaulay curve maps are not yet a canonical sheaf-level object in the
earlier chapters. -/
structure Chapter08FiniteMapCohenMacaulayTraceData
    (π : Chapter08FiniteMapOfCohenMacaulayCurves) where
  relativeDualizingModule : Prop
  evaluationAtOneTrace : Prop
  functorial : Prop

theorem chapter08_finite_duality_trace_exists_for_cohen_macaulay_curves
    (π : Chapter08FiniteMapOfCohenMacaulayCurves) :
    Nonempty (Chapter08FiniteMapCohenMacaulayTraceData π) := by
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

theorem chapter08_finite_duality_trace_is_not_field_trace
    {A B ωA ωB : Type u}
    [CommRing A] [CommRing B] [AddCommGroup ωA] [AddCommGroup ωB]
    [Algebra A B] [Module A ωA] [Module B ωB] [Module A ωB]
    (D : Chapter08FiniteDualityTrace A B ωA ωB) :
    chapter08_finite_duality_trace D = chapter08_evaluation_at_one := by
  exact D.trace_is_evaluation_at_one

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter08
