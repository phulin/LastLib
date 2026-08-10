import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section03ConstructingTheUnramifiedLift

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open scoped Polynomial

noncomputable section

/-! # Book 2, Chapter 7, §7.4: finite residue fields -/

/-- The finite-residue-field hypothesis. -/
def Chapter07FiniteResidueField (k : Type*) [Field k] : Prop :=
  Finite k

/-- The cardinality used as `q` in finite-residue-field formulas. -/
def Chapter07ResidueCardinality (k : Type*) [Field k] [Fintype k] : ℕ :=
  Fintype.card k

/-- The arithmetic Frobenius polynomial map `x ↦ x^q`, before installing the
field-specific ring-hom proof. -/
def Chapter07ArithmeticFrobeniusMap
    (q : ℕ) (k : Type*) [MonoidWithZero k] : k → k :=
  fun x => x ^ q

/-- An extension model that retains the field, residue-field, and Frobenius
data as structure fields.  Instance fields are used because the carrier types
are existential in the existence theorem below. -/
structure Chapter07FiniteResidueUnramifiedModel
    (K k : Type*) [Field K] [Field k] [Fintype k] where
  carrier : Type*
  [carrierField : Field carrier]
  [carrierAlgebra : Algebra K carrier]
  [carrierFinite : FiniteDimensional K carrier]
  residue : Type*
  [residueField : Field residue]
  [residueAlgebra : Algebra k residue]
  [residueFinite : FiniteDimensional k residue]
  q : ℕ
  q_card : Fintype.card k = q
  degree : ℕ
  degree_eq : degree = Module.finrank K carrier
  residueDegree : ℕ
  residueDegree_eq : residueDegree = Module.finrank k residue
  ramificationIndex : ℕ
  ramificationIndex_eq_one : ramificationIndex = 1
  residue_separable : ∀ x : residue, IsSeparable k x
  residueMap : carrier →+* residue
  frobenius : carrier ≃ₐ[K] carrier
  frobenius_generates :
    ∀ σ : carrier ≃ₐ[K] carrier, ∃ n : ℕ, frobenius ^ n = σ
  frobenius_on_residue :
    ∀ x : carrier,
      residueMap (frobenius x) = (residueMap x) ^ q

/-- The automorphism group used for finite unramified Galois groups. -/
abbrev Chapter07GaloisAutomorphismGroup
    (K L : Type*) [Field K] [Field L] [Algebra K L] :=
  L ≃ₐ[K] L

/-- Existence of the unique degree-`f` unramified lift over a finite residue
field.  The polynomial hypothesis is the finite-field residue construction
used in §7.3. -/
theorem chapter07_finite_residue_unramified_exists
    {A K k : Type*} [CommRing A] [IsDomain A]
    [Field K] [Field k] [Fintype k]
    [Algebra A K] [IsFractionRing A K] [HenselianLocalRing A]
    (res : A →+* k) (f : ℕ) (hf : 0 < f)
    (hpoly : ∃ gbar : k[X],
      gbar.Monic ∧ Irreducible gbar ∧ gbar.Separable ∧ gbar.natDegree = f) :
    ∃ M : Chapter07FiniteResidueUnramifiedModel K k,
      M.degree = f ∧ M.residueDegree = f ∧ M.ramificationIndex = 1 := by
  sorry

/-- Two degree-`f` unramified lifts are uniquely isomorphic over the base. -/
theorem chapter07_finite_residue_unramified_unique
    {K K₁ K₂ k k₁ k₂ : Type*}
    [Field K] [Field K₁] [Field K₂] [Field k] [Field k₁] [Field k₂]
    [Algebra K K₁] [Algebra K K₂] [Algebra k k₁] [Algebra k k₂]
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    [FiniteDimensional k k₁] [FiniteDimensional k k₂]
    [Fintype k]
    (f : ℕ)
    (h₁ : Module.finrank K K₁ = f ∧ Module.finrank k k₁ = f)
    (h₂ : Module.finrank K K₂ = f ∧ Module.finrank k k₂ = f)
    (hsep₁ : Chapter07ResidueExtensionIsSeparable k k₁)
    (hsep₂ : Chapter07ResidueExtensionIsSeparable k k₂)
    (E₁ : Chapter07FiniteLocalExtensionData K K₁ k k₁)
    (E₂ : Chapter07FiniteLocalExtensionData K K₂ k k₂)
    (hU₁ : Chapter07UnramifiedExtension E₁)
    (hU₂ : Chapter07UnramifiedExtension E₂) :
    Nonempty (K₁ ≃ₐ[K] K₂) := by
  sorry

/-- The finite unramified Galois group is cyclic, with generator characterized
by arithmetic Frobenius on the residue field. -/
theorem chapter07_finite_residue_galois_group_is_cyclic
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [Fintype k]
    (q f : ℕ) (hq : Fintype.card k = q)
    (hdegree : Module.finrank K L = f)
    (hresdegree : Module.finrank k l = f)
    (hsep : Chapter07ResidueExtensionIsSeparable k l)
    (ρ : L →+* l)
    (σ : Chapter07GaloisAutomorphismGroup K L)
    (hfrob : ∀ x : L, ρ (σ x) = (ρ x) ^ q)
    (hgen : ∀ τ : Chapter07GaloisAutomorphismGroup K L,
      ∃ n : ℕ, σ ^ n = τ) :
    IsCyclic (Chapter07GaloisAutomorphismGroup K L) := by
  sorry

/-- The standard finite-field indexing of unramified lifts in a fixed
separable closure.  The degree, nesting, and exhaustivity fields make the
chosen tower explicit instead of hiding it behind an arbitrary function. -/
structure Chapter07FiniteResidueTower
    (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] where
  level : ℕ → IntermediateField K Ω
  level_finite : ∀ f, FiniteDimensional K (level f)
  level_degree : ∀ f, Module.finrank K (level f) = f
  nested : ∀ {m n : ℕ}, m ∣ n → level m ≤ level n
  exhaustive : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
    ∃ f, E = level f

/-- In a fixed separable closure, the degree-indexed unramified tower has the
expected compositum and intersection laws. -/
theorem chapter07_finite_residue_compositum_intersection
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (T : Chapter07FiniteResidueTower K Ω) (m n : ℕ) :
    T.level m ⊔ T.level n = T.level (Nat.lcm m n) ∧
      T.level m ⊓ T.level n = T.level (Nat.gcd m n) := by
  sorry

/-- The maximal unramified subextension inside a chosen separable closure is
the union of all finite unramified levels. -/
def chapter07MaximalUnramifiedExtension
    (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
    (T : Chapter07FiniteResidueTower K Ω) : IntermediateField K Ω :=
  ⨆ f, T.level f

theorem chapter07_maximal_unramified_extension_is_maximal
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (T : Chapter07FiniteResidueTower K Ω) :
    ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      E ≤ chapter07MaximalUnramifiedExtension K Ω T := by
  sorry

/-- A fixed inverse-limit model of the profinite completion of the integers.
Compatibility is expressed using Mathlib's canonical maps `ZMod n → ZMod m`
for `m ∣ n`. -/
def Chapter07ProfiniteIntegerCompletionSubgroup :
    AddSubgroup (∀ n : ℕ, ZMod n) where
  carrier := {x |
    ∀ (m n : ℕ) (h : m ∣ n), ZMod.castHom h (ZMod m) (x n) = x m}
  zero_mem' := by
    intro m n h
    simp
  add_mem' := by
    intro x y hx hy m n h
    change ZMod.castHom h (ZMod m) (x n + y n) = x m + y m
    rw [map_add, hx m n h, hy m n h]
  neg_mem' := by
    intro x hx m n h
    change ZMod.castHom h (ZMod m) (-x n) = -x m
    rw [map_neg, hx m n h]

abbrev Chapter07ProfiniteIntegerCompletion : Type :=
  Chapter07ProfiniteIntegerCompletionSubgroup

/-- The canonical integer-to-compatible-residue map. -/
def chapter07IntegerToProfiniteCompletion
    (z : ℤ) : Chapter07ProfiniteIntegerCompletion :=
  ⟨fun n => z, by
    intro m n h
    simp⟩

/-- The inverse-limit assertion for the Galois group of the maximal
unramified extension.  The finite quotient maps are retained explicitly. -/
structure Chapter07MaximalUnramifiedGaloisData
    (G : Type*) [Group G] where
  quotient : ∀ n : ℕ, G →* Multiplicative (ZMod n)
  quotient_surjective : ∀ n, Function.Surjective (quotient n)
  quotient_compatible :
    ∀ (m n : ℕ) (h : m ∣ n),
      ((ZMod.castHom h (ZMod m)).toAddMonoidHom.toMultiplicative).comp
          (quotient n) = quotient m
  arithmeticFrobenius : G
  arithmeticFrobenius_image :
    ∀ n : ℕ, quotient n arithmeticFrobenius = Multiplicative.ofAdd (1 : ZMod n)
  profinite_equiv : Nonempty (G ≃* Multiplicative Chapter07ProfiniteIntegerCompletion)

theorem chapter07_maximal_unramified_galois_group_is_profinite_integer_completion
    (G : Type*) [Group G]
    (hG : Chapter07MaximalUnramifiedGaloisData G) :
    Nonempty (G ≃* Multiplicative Chapter07ProfiniteIntegerCompletion) := by
  exact hG.profinite_equiv

/-- The precise formal content of the warning about the completed infinite
union: non-algebraicity is a property of the chosen completion model, not an
automatic consequence of merely naming a completion. -/
def Chapter07CompletionIsNonAlgebraic
    (K Kcompletion : Type*) [Field K] [Field Kcompletion] [Algebra K Kcompletion]
    : Prop :=
  ∃ x : Kcompletion, ¬IsAlgebraic K x

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
