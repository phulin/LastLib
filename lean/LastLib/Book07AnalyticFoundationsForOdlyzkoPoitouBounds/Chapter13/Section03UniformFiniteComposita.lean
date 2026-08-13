import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13.Dependencies

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter13

noncomputable section

open scoped BigOperators
open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01

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
  unfold chapter13FiniteCompositum
  exact IntermediateField.finiteDimensional_iSup_of_finset'
    (fun i hi => 𝓛.finite i)

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
  rfl

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
  exact chapter13_rootDiscriminant_eq_canonical _

theorem chapter13_finite_compositum_realProportion_eq_canonical
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    chapter13FiniteCompositumRealProportion 𝓛 s =
      (NumberField.InfinitePlace.nrRealPlaces
        (chapter13FiniteCompositum 𝓛 s) : ℝ) /
        (chapter13FiniteCompositumDegree 𝓛 s : ℝ) := by
  let : Algebra ℚ Ω :=
    ((algebraMap F Ω).comp (algebraMap ℚ F)).toAlgebra
  let : IsScalarTower ℚ F Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => by rfl)
  let : FiniteDimensional F (chapter13FiniteCompositum 𝓛 s) :=
    chapter13_finite_compositum_finite 𝓛 s
  let : NumberField (chapter13FiniteCompositum 𝓛 s) :=
    NumberField.of_module_finite F (chapter13FiniteCompositum 𝓛 s)
  have hmodule : @Algebra.toModule ℚ (chapter13FiniteCompositum 𝓛 s) _ _ _ =
      IntermediateField.module' (chapter13FiniteCompositum 𝓛 s) := Subsingleton.elim _ _
  change chapter13RealProportion (chapter13FiniteCompositum 𝓛 s) = _
  simp only [chapter13RealProportion, chapter01RealProportion, chapter01Degree,
    chapter13FiniteCompositumDegree]
  rw [hmodule]
  congr 1

theorem chapter13_finite_compositum_degree_pos
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    0 < chapter13FiniteCompositumDegree 𝓛 s := by
  exact chapter13_degree_pos _

theorem chapter13_finite_compositum_rootDiscriminant_pos
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    (s : Finset 𝓛.index) :
    0 < chapter13FiniteCompositumRootDiscriminant 𝓛 s := by
  exact chapter13_rootDiscriminant_pos _

theorem chapter13_finite_compositum_extension_le
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    {s : Finset 𝓛.index} {i : 𝓛.index} (hi : i ∈ s) :
    𝓛.extension i ≤ chapter13FiniteCompositum 𝓛 s := by
  unfold chapter13FiniteCompositum
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

theorem chapter13_finite_compositum_mono
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    {s t : Finset 𝓛.index} (hst : s ⊆ t) :
    chapter13FiniteCompositum 𝓛 s ≤ chapter13FiniteCompositum 𝓛 t := by
  unfold chapter13FiniteCompositum
  refine iSup_le fun i => iSup_le fun hi => ?_
  exact le_iSup_of_le i (le_iSup_of_le (hst hi) le_rfl)

theorem chapter13_finite_compositum_degree_mono
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    {s t : Finset 𝓛.index} (hst : s ⊆ t) :
    chapter13FiniteCompositumDegree 𝓛 s ≤
      chapter13FiniteCompositumDegree 𝓛 t := by
  let : Algebra ℚ Ω :=
    ((algebraMap F Ω).comp (algebraMap ℚ F)).toAlgebra
  let : IsScalarTower ℚ F Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => by rfl)
  let : NumberField (chapter13FiniteCompositum 𝓛 s) :=
    chapter13_finite_compositum_numberField 𝓛 s
  let : NumberField (chapter13FiniteCompositum 𝓛 t) :=
    chapter13_finite_compositum_numberField 𝓛 t
  have hrel : Module.finrank F (chapter13FiniteCompositum 𝓛 s) ≤
      Module.finrank F (chapter13FiniteCompositum 𝓛 t) :=
    IntermediateField.finrank_le_of_le_right
      (chapter13_finite_compositum_mono 𝓛 hst)
  have hmodule_s : @Algebra.toModule ℚ (chapter13FiniteCompositum 𝓛 s) _ _ _ =
      IntermediateField.module' (chapter13FiniteCompositum 𝓛 s) :=
    Subsingleton.elim _ _
  have hmodule_t : @Algebra.toModule ℚ (chapter13FiniteCompositum 𝓛 t) _ _ _ =
      IntermediateField.module' (chapter13FiniteCompositum 𝓛 t) :=
    Subsingleton.elim _ _
  have hdegree_s : chapter13FiniteCompositumDegree 𝓛 s =
      Module.finrank ℚ (chapter13FiniteCompositum 𝓛 s) := by
    rw [chapter13_finite_compositum_degree_eq_finrank 𝓛 s, hmodule_s]
  have hdegree_t : chapter13FiniteCompositumDegree 𝓛 t =
      Module.finrank ℚ (chapter13FiniteCompositum 𝓛 t) := by
    rw [chapter13_finite_compositum_degree_eq_finrank 𝓛 t, hmodule_t]
  calc
    chapter13FiniteCompositumDegree 𝓛 s =
        Module.finrank ℚ (chapter13FiniteCompositum 𝓛 s) :=
      hdegree_s
    _ = Module.finrank ℚ F * Module.finrank F (chapter13FiniteCompositum 𝓛 s) :=
      (Module.finrank_mul_finrank ℚ F (chapter13FiniteCompositum 𝓛 s)).symm
    _ ≤ Module.finrank ℚ F * Module.finrank F (chapter13FiniteCompositum 𝓛 t) :=
      Nat.mul_le_mul_left _ hrel
    _ = Module.finrank ℚ (chapter13FiniteCompositum 𝓛 t) :=
      Module.finrank_mul_finrank ℚ F (chapter13FiniteCompositum 𝓛 t)
    _ = chapter13FiniteCompositumDegree 𝓛 t :=
      hdegree_t.symm

theorem chapter13_finite_compositum_eq_of_degree_eq
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    {s t : Finset 𝓛.index} (hst : s ⊆ t)
    (hdegree : chapter13FiniteCompositumDegree 𝓛 s =
      chapter13FiniteCompositumDegree 𝓛 t) :
    chapter13FiniteCompositum 𝓛 s = chapter13FiniteCompositum 𝓛 t := by
  let : Algebra ℚ Ω :=
    ((algebraMap F Ω).comp (algebraMap ℚ F)).toAlgebra
  let : IsScalarTower ℚ F Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => by rfl)
  let : NumberField (chapter13FiniteCompositum 𝓛 s) :=
    chapter13_finite_compositum_numberField 𝓛 s
  let : NumberField (chapter13FiniteCompositum 𝓛 t) :=
    chapter13_finite_compositum_numberField 𝓛 t
  let : FiniteDimensional F (chapter13FiniteCompositum 𝓛 t) :=
    chapter13_finite_compositum_finite 𝓛 t
  have hfield : chapter13FiniteCompositum 𝓛 s ≤
      chapter13FiniteCompositum 𝓛 t :=
    chapter13_finite_compositum_mono 𝓛 hst
  have hmodule_s : @Algebra.toModule ℚ (chapter13FiniteCompositum 𝓛 s) _ _ _ =
      IntermediateField.module' (chapter13FiniteCompositum 𝓛 s) :=
    Subsingleton.elim _ _
  have hmodule_t : @Algebra.toModule ℚ (chapter13FiniteCompositum 𝓛 t) _ _ _ =
      IntermediateField.module' (chapter13FiniteCompositum 𝓛 t) :=
    Subsingleton.elim _ _
  have hdegree_s : chapter13FiniteCompositumDegree 𝓛 s =
      Module.finrank ℚ (chapter13FiniteCompositum 𝓛 s) := by
    rw [chapter13_finite_compositum_degree_eq_finrank 𝓛 s, hmodule_s]
  have hdegree_t : chapter13FiniteCompositumDegree 𝓛 t =
      Module.finrank ℚ (chapter13FiniteCompositum 𝓛 t) := by
    rw [chapter13_finite_compositum_degree_eq_finrank 𝓛 t, hmodule_t]
  have hmul : Module.finrank ℚ F *
      Module.finrank F (chapter13FiniteCompositum 𝓛 s) =
      Module.finrank ℚ F *
        Module.finrank F (chapter13FiniteCompositum 𝓛 t) := by
    calc
      Module.finrank ℚ F * Module.finrank F (chapter13FiniteCompositum 𝓛 s) =
          Module.finrank ℚ (chapter13FiniteCompositum 𝓛 s) :=
        Module.finrank_mul_finrank ℚ F (chapter13FiniteCompositum 𝓛 s)
      _ = chapter13FiniteCompositumDegree 𝓛 s := hdegree_s.symm
      _ = chapter13FiniteCompositumDegree 𝓛 t := hdegree
      _ = Module.finrank ℚ (chapter13FiniteCompositum 𝓛 t) := hdegree_t
      _ = Module.finrank ℚ F * Module.finrank F (chapter13FiniteCompositum 𝓛 t) :=
        (Module.finrank_mul_finrank ℚ F (chapter13FiniteCompositum 𝓛 t)).symm
  have hrel : Module.finrank F (chapter13FiniteCompositum 𝓛 s) =
      Module.finrank F (chapter13FiniteCompositum 𝓛 t) :=
    Nat.eq_of_mul_eq_mul_left
      (show 0 < Module.finrank ℚ F from Module.finrank_pos) hmul
  exact IntermediateField.eq_of_le_of_finrank_eq hfield hrel

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
  obtain ⟨N, hN⟩ := chapter13_threshold_principle_general hthreshold
  refine ⟨N, ?_⟩
  intro s
  let : NumberField (chapter13FiniteCompositum 𝓛 s) :=
    chapter13_finite_compositum_numberField 𝓛 s
  have hcap := hN (chapter13FiniteCompositum 𝓛 s)
    (by
      simpa [chapter13FiniteCompositumRootDiscriminant] using (hceiling s).1)
    (by
      simpa [chapter13FiniteCompositumRealProportion] using (hceiling s).2)
  simpa [chapter13FiniteCompositumDegree, chapter13Degree] using hcap

theorem chapter13_maximal_compositum_contains_every_extension
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω)
    {s : Finset 𝓛.index}
    (hmax : ∀ t : Finset 𝓛.index,
      chapter13FiniteCompositumDegree 𝓛 t ≤
        chapter13FiniteCompositumDegree 𝓛 s) :
    ∀ i, 𝓛.extension i ≤ chapter13FiniteCompositum 𝓛 s := by
  classical
  intro i
  have hst : s ⊆ insert i s := Finset.subset_insert i s
  have hdegree : chapter13FiniteCompositumDegree 𝓛 s =
      chapter13FiniteCompositumDegree 𝓛 (insert i s) :=
    le_antisymm (chapter13_finite_compositum_degree_mono 𝓛 hst) (hmax (insert i s))
  have heq := chapter13_finite_compositum_eq_of_degree_eq 𝓛 hst hdegree
  rw [heq]
  exact chapter13_finite_compositum_extension_le 𝓛 (Finset.mem_insert_self i s)

theorem chapter13_exists_maximal_finite_compositum
    {F Ω : Type*} [Field F] [Field Ω] [NumberField F] [Algebra F Ω]
    (𝓛 : Chapter13UniformCompositumFamily F Ω) {N : ℕ}
    (hbound : ∀ s : Finset 𝓛.index,
      chapter13FiniteCompositumDegree 𝓛 s < N) :
    ∃ s : Finset 𝓛.index, ∀ t : Finset 𝓛.index,
      chapter13FiniteCompositumDegree 𝓛 t ≤
        chapter13FiniteCompositumDegree 𝓛 s := by
  classical
  induction N with
  | zero =>
      have hpos := chapter13_finite_compositum_degree_pos 𝓛
        (∅ : Finset 𝓛.index)
      have hlt := hbound (∅ : Finset 𝓛.index)
      omega
  | succ N ih =>
      by_cases hex : ∃ s : Finset 𝓛.index,
          chapter13FiniteCompositumDegree 𝓛 s = N
      · rcases hex with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        intro t
        have ht := hbound t
        omega
      · apply ih
        intro s
        have hslt := hbound s
        have hsne : chapter13FiniteCompositumDegree 𝓛 s ≠ N := by
          intro hs
          exact hex ⟨s, hs⟩
        omega

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
