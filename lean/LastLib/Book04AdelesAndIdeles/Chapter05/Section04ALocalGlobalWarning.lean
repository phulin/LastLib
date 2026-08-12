import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open scoped Topology

universe u v w

/-! ## 5.4. A local--global warning -/

variable {K : Type u} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {V : Type v} {Kv : V → Type w}
variable [∀ v, Field (Kv v)] [∀ v, TopologicalSpace (Kv v)]
variable {P : Chapter05PlaceSystem K V Kv}

/-! The source uses the real conic as a warning before discussing subtler
    Hasse-principle failures. -/

def chapter05RealConicEquation (x y : ℝ) : Prop :=
  x ^ 2 + y ^ 2 = (-1 : ℝ)

theorem chapter05_real_conic_has_no_real_point :
    ¬ ∃ x y : ℝ, chapter05RealConicEquation x y := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the later algebraic-geometry API should replace
    this lightweight affine-equation interface when a concrete variety is
    selected.

SOURCE_ISSUE: “subtler varieties can have points over every completion and
none over `K`” gives no variety, equation, or hypotheses on the local-point
functor.  The smallest principled accommodation is the parameterized
obstruction interface below; a concrete counterexample should replace it in
the later fixup pass. -/

/-! The source does not name a particular counterexample for the second
    warning.  This structure records exactly what “points over every
    completion but no global point” means, without inventing an equation. -/

structure Chapter05LocalGlobalObstruction
    (P : Chapter05PlaceSystem K V Kv) where
  arity : ℕ
  equation : (Fin arity → K) → Prop
  localEquation : ∀ v : V, (Fin arity → Kv v) → Prop
  global_to_local :
    ∀ (v : V) (x : Fin arity → K), equation x →
      localEquation v (fun i => P.completionMap v (x i))
  every_completion_has_point :
    ∀ v : V, ∃ x : Fin arity → Kv v, localEquation v x
  has_no_global_point : ¬ ∃ x : Fin arity → K, equation x

def chapter05HasLocalGlobalObstruction : Prop :=
  Nonempty (Chapter05LocalGlobalObstruction P)

/- The source asserts that such obstructions exist but does not specify an
   equation.  The predicate above is the proof-ready interface for that
   assertion; a later chapter can instantiate it with a concrete variety. -/

/-! A precise tail predicate isolates the hypothesis that is absent from weak
    approximation and present in strong approximation. -/

def chapter05IntegralTailCondition (S : Set V) (a : K) : Prop :=
  ∀ v : V, v ∉ S → v ∈ P.finite →
    P.completionMap v a ∈ P.integral v

theorem chapter05_global_elements_have_finite_nonintegral_tail (a : K) :
    ({v | v ∈ P.finite ∧ P.completionMap v a ∉ P.integral v} : Set V).Finite := by
  exact P.global_integrality a

theorem chapter05_strong_tail_is_an_almost_everywhere_requirement
    (S : Set V) (a : K) (hS :
      ∀ v : V, v ∈ P.finite → v ∉ S →
        P.completionMap v a ∈ P.integral v) :
    chapter05IntegralTailCondition (P := P) S a := by
  intro v hvS hvfinite
  exact hS v hvfinite hvS

end

end LastLib.Book04AdelesAndIdeles.Chapter05
