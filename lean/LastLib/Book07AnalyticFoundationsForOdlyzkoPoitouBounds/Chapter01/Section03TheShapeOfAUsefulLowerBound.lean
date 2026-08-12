import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.Section02DegreeSignatureAndRootDiscriminant

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01

noncomputable section

open NumberField

universe u

/-! ## 1.3. The shape of a useful lower bound -/

/- An analytic lower bound is recorded with exactly the two monotonicity
   bridges used by the chapter: degree and the number of real embeddings.
   Monotonicity is only required on valid signature parameters. -/
structure Chapter01AnalyticLowerBound where
  bound : ℕ → ℕ → ℝ
  lower_bound : ∀ (K : Type u) [Field K] [NumberField K],
    bound (chapter01Degree K) (chapter01RealPlaces K) ≤ chapter01RootDiscriminant K
  degree_mono : ∀ {n m r₁ : ℕ},
    chapter01ValidSignature n r₁ → chapter01ValidSignature m r₁ → n ≤ m →
      bound n r₁ ≤ bound m r₁
  real_mono : ∀ {n r₁ s₁ : ℕ},
    chapter01ValidSignature n r₁ → chapter01ValidSignature n s₁ → r₁ ≤ s₁ →
      bound n r₁ ≤ bound n s₁

theorem chapter01_analytic_lower_bound
    (B : Chapter01AnalyticLowerBound.{u})
    (K : Type u) [Field K] [NumberField K] :
    B.bound (chapter01Degree K) (chapter01RealPlaces K) ≤
      chapter01RootDiscriminant K := by
  exact B.lower_bound K

theorem chapter01_analytic_lower_bound_degree_mono
    (B : Chapter01AnalyticLowerBound) {n m r₁ : ℕ}
    (hn : chapter01ValidSignature n r₁)
    (hm : chapter01ValidSignature m r₁) (hnm : n ≤ m) :
    B.bound n r₁ ≤ B.bound m r₁ := by
  exact B.degree_mono hn hm hnm

theorem chapter01_analytic_lower_bound_real_mono
    (B : Chapter01AnalyticLowerBound) {n r₁ s₁ : ℕ}
    (hn : chapter01ValidSignature n r₁)
    (hs : chapter01ValidSignature n s₁) (hrs : r₁ ≤ s₁) :
    B.bound n r₁ ≤ B.bound n s₁ := by
  exact B.real_mono hn hs hrs

def chapter01StrictRootDiscriminantCeiling
    (K : Type*) [Field K] [NumberField K] (U : ℝ) : Prop :=
  chapter01RootDiscriminant K < U

def chapter01WeakRootDiscriminantCeiling
    (K : Type*) [Field K] [NumberField K] (U : ℝ) : Prop :=
  chapter01RootDiscriminant K ≤ U

def chapter01FiniteDegreeCrossing (B : ℕ → ℝ) (U : ℝ) (N : ℕ) : Prop :=
  U ≤ B N

theorem chapter01_strict_ceiling_contradiction
    (K : Type*) [Field K] [NumberField K] (U : ℝ)
    (hupper : chapter01StrictRootDiscriminantCeiling K U)
    (hlower : U ≤ chapter01RootDiscriminant K) : False := by
  exact (not_lt_of_ge hlower) hupper

/- If a monotone lower bound reaches a strict arithmetic ceiling at degree N,
   every field satisfying that ceiling has degree strictly below N. -/
theorem chapter01_degree_lt_of_strict_ceiling_of_crossing
    (K : Type*) [Field K] [NumberField K] (U : ℝ) (B : ℕ → ℝ)
    {N : ℕ} (hmono : Monotone B)
    (hupper : chapter01StrictRootDiscriminantCeiling K U)
    (hlower : B (chapter01Degree K) ≤ chapter01RootDiscriminant K)
    (hcross : chapter01FiniteDegreeCrossing B U N) :
    chapter01Degree K < N := by
  sorry

/- With a weak arithmetic ceiling, the crossing must be strict. -/
theorem chapter01_degree_lt_of_weak_ceiling_of_strict_crossing
    (K : Type*) [Field K] [NumberField K] (U : ℝ) (B : ℕ → ℝ)
    {N : ℕ} (hmono : Monotone B)
    (hupper : chapter01WeakRootDiscriminantCeiling K U)
    (hlower : B (chapter01Degree K) ≤ chapter01RootDiscriminant K)
    (hcross : U < B N) :
    chapter01Degree K < N := by
  sorry

/- Equal-degree inclusions of finite intermediate fields are equalities. -/
theorem chapter01_intermediateField_eq_of_le_of_degree_eq
    (Ω : Type*) [Field Ω] [NumberField Ω]
    (E F : IntermediateField ℚ Ω) (hEF : E ≤ F)
    (hdegree : Module.finrank ℚ E = Module.finrank ℚ F) : E = F := by
  exact IntermediateField.eq_of_le_of_finrank_eq hEF hdegree

structure Chapter01NestedFieldChain
    (Ω : Type*) [Field Ω] [NumberField Ω] where
  field : ℕ → IntermediateField ℚ Ω
  nested : ∀ i : ℕ, field i ≤ field (i + 1)

@[ext]
theorem Chapter01NestedFieldChain.ext
    (Ω : Type*) [Field Ω] [NumberField Ω]
    {C D : Chapter01NestedFieldChain Ω}
    (hfield : C.field = D.field) : C = D := by
  cases C
  cases D
  simp_all

def chapter01NestedFieldChainDegree
    (Ω : Type*) [Field Ω] [NumberField Ω]
    (C : Chapter01NestedFieldChain Ω) : ℕ → ℕ :=
  fun i => Module.finrank ℚ (C.field i)

theorem chapter01NestedFieldChainDegree_mono
    (Ω : Type*) [Field Ω] [NumberField Ω]
    (C : Chapter01NestedFieldChain Ω) :
    Monotone (chapter01NestedFieldChainDegree Ω C) := by
  sorry

/- Bounded degree in a nested chain forces eventual equality and hence
   stabilization. -/
theorem chapter01_nested_field_chain_stabilizes
    (Ω : Type*) [Field Ω] [NumberField Ω]
    (C : Chapter01NestedFieldChain Ω)
    (hbounded : ∃ N : ℕ, ∀ i : ℕ,
      chapter01NestedFieldChainDegree Ω C i ≤ N) :
    ∃ i₀ : ℕ, ∀ j : ℕ, i₀ ≤ j → C.field j = C.field i₀ := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01
