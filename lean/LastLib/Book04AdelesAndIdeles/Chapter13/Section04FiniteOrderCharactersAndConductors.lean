import Mathlib.Analysis.Complex.Convex
import LastLib.Book04AdelesAndIdeles.Chapter13.Section03UnitaryCharactersAndModulusTwists
import LastLib.Book04AdelesAndIdeles.Chapter11.Section07ComputingElementaryRayQuotients

open scoped NumberField.AdeleRing RestrictedProduct

namespace LastLib.Book04AdelesAndIdeles.Chapter13

noncomputable section

/-!
## 13.4 Finite-order characters and conductors
-/

def chapter13FiniteOrderClassCharacter
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x, χ x ^ n = 1

theorem chapter13_finite_order_iff_finite_image
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) :
    chapter13FiniteOrderClassCharacter K χ ↔
      Set.Finite (Set.range χ) := by
  sorry

def chapter13ClassCharacterKernel
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) :
    Subgroup (Chapter13IdeleClass K) :=
  χ.toMonoidHom.ker

theorem chapter13_finite_image_kernel_open
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K)
    (hχ : chapter13FiniteOrderClassCharacter K χ) :
    IsOpen (chapter13ClassCharacterKernel K χ : Set (Chapter13IdeleClass K)) := by
  sorry

theorem chapter13_finite_order_kernel_quotient_finite
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K)
    (hχ : chapter13FiniteOrderClassCharacter K χ) :
    Finite (Chapter13IdeleClass K ⧸ chapter13ClassCharacterKernel K χ) := by
  sorry

def chapter13PullbackRayCharacter
    (K : Type*) [Field K] [NumberField K]
    (m : Chapter13RayModulus K)
    (θ : Chapter13RayClassCharacter m) : Chapter13ClassCharacter K :=
  { toMonoidHom :=
      θ.comp
        (LastLib.Book04AdelesAndIdeles.Chapter11.chapter11IdeleClassToRayClass m)
    continuous_toFun := by sorry }

def chapter13RayClassTransitionMap
    (K : Type*) [Field K] [NumberField K]
    {m n : Chapter13RayModulus K}
    (hmn : LastLib.Book04AdelesAndIdeles.Chapter11.RayModulus.LE m n) :
    Chapter13RayClassGroup n →* Chapter13RayClassGroup m :=
  LastLib.Book04AdelesAndIdeles.Chapter11.chapter11RayClassProjectionOfLE hmn

theorem chapter13_pullback_ray_character_compatible_with_transition
    (K : Type*) [Field K] [NumberField K]
    {m n : Chapter13RayModulus K}
    (hmn : LastLib.Book04AdelesAndIdeles.Chapter11.RayModulus.LE m n)
    (θ : Chapter13RayClassCharacter m) :
    chapter13PullbackRayCharacter K m θ =
      chapter13PullbackRayCharacter K n
        (θ.comp (chapter13RayClassTransitionMap K hmn)) := by
  sorry

def chapter13FactorsThroughRayLevel
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (m : Chapter13RayModulus K) : Prop :=
  ∃ θ : Chapter13RayClassCharacter m,
    chapter13PullbackRayCharacter K m θ = χ

theorem chapter13_finite_order_character_factors_through_a_ray_level
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K)
    (hχ : chapter13FiniteOrderClassCharacter K χ) :
    ∃ m, chapter13FactorsThroughRayLevel K χ m := by
  sorry

theorem chapter13_ray_level_factorization_is_finite_order
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (m : Chapter13RayModulus K)
    (hχ : chapter13FactorsThroughRayLevel K χ m) :
    chapter13FiniteOrderClassCharacter K χ := by
  sorry

theorem chapter13_finite_order_characters_directed_union_of_ray_duals
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) :
    chapter13FiniteOrderClassCharacter K χ ↔
      ∃ m, chapter13FactorsThroughRayLevel K χ m := by
  sorry

/- The existential over a single level in this theorem is intentional: a finite-order character
has one finite conductor and is pulled back along refinements; the collection is not a product of
independent levelwise duals. -/

def chapter13IsConductor
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) (m : Chapter13RayModulus K) : Prop :=
  chapter13FactorsThroughRayLevel K χ m ∧
    ∀ n, chapter13FactorsThroughRayLevel K χ n →
      LastLib.Book04AdelesAndIdeles.Chapter11.RayModulus.LE m n

theorem chapter13_finite_order_character_has_conductor
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K)
    (hχ : chapter13FiniteOrderClassCharacter K χ) :
    ∃ m, chapter13IsConductor K χ m := by
  sorry

noncomputable def chapter13Conductor
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K)
    (hχ : chapter13FiniteOrderClassCharacter K χ) : Chapter13RayModulus K :=
  Classical.choose (chapter13_finite_order_character_has_conductor K χ hχ)

theorem chapter13_conductor_specification
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K)
    (hχ : chapter13FiniteOrderClassCharacter K χ) :
    chapter13IsConductor K χ (chapter13Conductor K χ hχ) := by
  sorry

/-! A finite-order character on a connected archimedean local multiplicative group is trivial.
This is the precise obstruction behind the book's warning that complex places do not need a finite
archimedean modulus, while a real sign character does. -/

theorem chapter13_connected_finite_order_character_trivial
    {G : Type*} [Group G] [TopologicalSpace G] [ConnectedSpace G]
    (χ : G →ₜ* ℂˣ)
    (hχ : ∃ n : ℕ, 0 < n ∧ ∀ x, χ x ^ n = 1) :
    χ = 1 := by
  sorry

theorem chapter13_complex_place_finite_order_character_trivial
    (χ : (ℂ)ˣ →ₜ* ℂˣ)
    (hχ : ∃ n : ℕ, 0 < n ∧ ∀ x, χ x ^ n = 1) :
    χ = 1 := by
  sorry

theorem chapter13_real_sign_character_is_not_trivial
    (χ : ℝˣ →ₜ* ℂˣ)
    (hsign : χ (-1) ≠ 1) :
    χ ≠ 1 := by
  sorry

def chapter13InfiniteImageCharacter
    {G : Type*} [Monoid G] [TopologicalSpace G] (χ : G →ₜ* ℂˣ) : Prop :=
  Set.Infinite (Set.range χ)

theorem chapter13_unitary_does_not_imply_finite_order
    (K : Type*) [Field K] [NumberField K] :
    ∃ χ : Chapter13ClassCharacter K,
      chapter13IsUnitaryCharacter χ ∧
        ¬ chapter13FiniteOrderClassCharacter K χ := by
  sorry

theorem chapter13_archimedean_angular_character_can_have_infinite_image :
    ∃ χ : (ℂ)ˣ →ₜ* ℂˣ,
      chapter13IsUnitaryCharacter χ ∧ chapter13InfiniteImageCharacter χ := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter13
