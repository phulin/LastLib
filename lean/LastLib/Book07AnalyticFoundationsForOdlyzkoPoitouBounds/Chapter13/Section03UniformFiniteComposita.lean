import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13

noncomputable section

open scoped BigOperators

/-! ### 13.3 Uniform finite composita -/

/-
All extensions are realized in one ambient field.  This is the canonical
meaning of a family of composita; the ambient field need not itself be a
number field, since the directed compositum is the object whose finiteness is
being proved.
-/
structure Chapter13UniformCompositumFamily
    (F Ω : Type*) [Field F] [Field Ω] [NumberField F] [Algebra F Ω] where
  index : Type*
  extension : index → IntermediateField F Ω
  finite : ∀ i, FiniteDimensional F (extension i)

noncomputable def chapter13FiniteCompositum
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) : IntermediateField F Ω :=
  ⨆ i ∈ s, 𝓛.extension i

theorem chapter13_finite_compositum_finite
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    FiniteDimensional F (chapter13FiniteCompositum 𝓛 s) := by
  sorry

noncomputable instance chapter13FiniteCompositumNumberField
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    NumberField (chapter13FiniteCompositum 𝓛 s) := by
  let hfinite : Module.Finite F (chapter13FiniteCompositum 𝓛 s) :=
    chapter13_finite_compositum_finite 𝓛 s
  exact @NumberField.of_module_finite F (chapter13FiniteCompositum 𝓛 s) _ _ _ _ hfinite

theorem chapter13_finite_compositum_numberField
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    NumberField (chapter13FiniteCompositum 𝓛 s) := by
  let hfinite : Module.Finite F (chapter13FiniteCompositum 𝓛 s) :=
    chapter13_finite_compositum_finite 𝓛 s
  exact @NumberField.of_module_finite F (chapter13FiniteCompositum 𝓛 s) _ _ _ _ hfinite

noncomputable def chapter13FiniteCompositumDegree
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) : ℕ := by
  letI : FiniteDimensional F (chapter13FiniteCompositum 𝓛 s) :=
    chapter13_finite_compositum_finite 𝓛 s
  letI : NumberField (chapter13FiniteCompositum 𝓛 s) :=
    NumberField.of_module_finite F (chapter13FiniteCompositum 𝓛 s)
  exact chapter13Degree (chapter13FiniteCompositum 𝓛 s)

theorem chapter13_finite_compositum_degree_eq_finrank
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    chapter13FiniteCompositumDegree 𝓛 s =
      Module.finrank ℚ (chapter13FiniteCompositum 𝓛 s) := by
  sorry

noncomputable def chapter13FiniteCompositumRootDiscriminant
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) : ℝ := by
  letI : FiniteDimensional F (chapter13FiniteCompositum 𝓛 s) :=
    chapter13_finite_compositum_finite 𝓛 s
  letI : NumberField (chapter13FiniteCompositum 𝓛 s) :=
    NumberField.of_module_finite F (chapter13FiniteCompositum 𝓛 s)
  exact chapter13RootDiscriminant (chapter13FiniteCompositum 𝓛 s)

noncomputable def chapter13FiniteCompositumRealProportion
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) : ℝ := by
  letI : FiniteDimensional F (chapter13FiniteCompositum 𝓛 s) :=
    chapter13_finite_compositum_finite 𝓛 s
  letI : NumberField (chapter13FiniteCompositum 𝓛 s) :=
    NumberField.of_module_finite F (chapter13FiniteCompositum 𝓛 s)
  exact chapter13RealProportion (chapter13FiniteCompositum 𝓛 s)

theorem chapter13_finite_compositum_rootDiscriminant_eq_canonical
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    chapter13FiniteCompositumRootDiscriminant 𝓛 s =
      NumberField.rootDiscr (chapter13FiniteCompositum 𝓛 s) := by
  sorry

theorem chapter13_finite_compositum_realProportion_eq_canonical
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    chapter13FiniteCompositumRealProportion 𝓛 s =
      (NumberField.InfinitePlace.nrRealPlaces
        (chapter13FiniteCompositum 𝓛 s) : ℝ) /
        (chapter13FiniteCompositumDegree 𝓛 s : ℝ) := by
  sorry

theorem chapter13_finite_compositum_degree_pos
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    0 < chapter13FiniteCompositumDegree 𝓛 s := by
  sorry

theorem chapter13_finite_compositum_rootDiscriminant_pos
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    0 < chapter13FiniteCompositumRootDiscriminant 𝓛 s := by
  sorry

theorem chapter13_finite_compositum_extension_le
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    {s : Finset 𝓛.index} {i : 𝓛.index} (hi : i ∈ s) :
    𝓛.extension i ≤ chapter13FiniteCompositum 𝓛 s := by
  sorry

theorem chapter13_finite_compositum_mono
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    {s t : Finset 𝓛.index} (hst : s ⊆ t) :
    chapter13FiniteCompositum 𝓛 s ≤ chapter13FiniteCompositum 𝓛 t := by
  sorry

theorem chapter13_finite_compositum_degree_mono
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    {s t : Finset 𝓛.index} (hst : s ⊆ t) :
    chapter13FiniteCompositumDegree 𝓛 s ≤
      chapter13FiniteCompositumDegree 𝓛 t := by
  sorry

theorem chapter13_finite_compositum_eq_of_degree_eq
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    {s t : Finset 𝓛.index} (hst : s ⊆ t)
    (hdegree : chapter13FiniteCompositumDegree 𝓛 s =
      chapter13FiniteCompositumDegree 𝓛 t) :
    chapter13FiniteCompositum 𝓛 s = chapter13FiniteCompositum 𝓛 t := by
  sorry

def chapter13UniformCompositumCeiling
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω) (U α₀ : ℝ) : Prop :=
  ∀ s : Finset 𝓛.index,
    chapter13FiniteCompositumRootDiscriminant 𝓛 s ≤ U ∧
      α₀ ≤ chapter13FiniteCompositumRealProportion 𝓛 s

/- The universal quantifier over finite supports is the arithmetic closure
   premise in the source.  It is not inferred from separate bounds on the
   individual extensions. -/
def chapter13CompositumCeilingClosure
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω) (U : ℝ) : Prop :=
  ∀ s : Finset 𝓛.index,
    chapter13FiniteCompositumRootDiscriminant 𝓛 s ≤ U

structure Chapter13FiniteDirectedCompositum
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω) where
  support : Finset 𝓛.index
  contains : ∀ i, 𝓛.extension i ≤ chapter13FiniteCompositum 𝓛 support

theorem chapter13_finite_directed_compositum_finite
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (C : Chapter13FiniteDirectedCompositum 𝓛) :
    FiniteDimensional F (chapter13FiniteCompositum 𝓛 C.support) := by
  exact chapter13_finite_compositum_finite 𝓛 C.support

theorem chapter13_uniform_composita_have_degree_cap
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω) {U α₀ : ℝ}
    (hthreshold : U < 4 * Real.pi * Real.exp
      (Real.eulerMascheroniConstant + α₀))
    (hceiling : chapter13UniformCompositumCeiling 𝓛 U α₀) :
    ∃ N : ℕ, ∀ s : Finset 𝓛.index,
      chapter13FiniteCompositumDegree 𝓛 s < N := by
  sorry

theorem chapter13_maximal_compositum_contains_every_extension
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    {s : Finset 𝓛.index}
    (hmax : ∀ t : Finset 𝓛.index,
      chapter13FiniteCompositumDegree 𝓛 t ≤
        chapter13FiniteCompositumDegree 𝓛 s) :
    ∀ i, 𝓛.extension i ≤ chapter13FiniteCompositum 𝓛 s := by
  sorry

theorem chapter13_exists_maximal_finite_compositum
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω) {N : ℕ}
    (hbound : ∀ s : Finset 𝓛.index,
      chapter13FiniteCompositumDegree 𝓛 s < N) :
    ∃ s : Finset 𝓛.index, ∀ t : Finset 𝓛.index,
      chapter13FiniteCompositumDegree 𝓛 t ≤
        chapter13FiniteCompositumDegree 𝓛 s := by
  sorry

/-! Uniform finite-compositum theorem. -/
theorem chapter13_uniform_finite_compositum
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω) {U α₀ : ℝ}
    (hthreshold : U < 4 * Real.pi * Real.exp
      (Real.eulerMascheroniConstant + α₀))
    (hceiling : chapter13UniformCompositumCeiling 𝓛 U α₀) :
    Nonempty (Chapter13FiniteDirectedCompositum 𝓛) := by
  rcases chapter13_uniform_composita_have_degree_cap 𝓛 hthreshold hceiling with
    ⟨N, hN⟩
  rcases chapter13_exists_maximal_finite_compositum 𝓛 hN with ⟨s, hs⟩
  exact ⟨⟨s, chapter13_maximal_compositum_contains_every_extension 𝓛 hs⟩⟩

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13
