import Mathlib.AlgebraicGeometry.Fiber
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02.Section02EffectiveCartierDivisors

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry nonZeroDivisors

universe u v

/-!
### 2.3 Pullback, restriction, and flatness
-/

/- LOCAL_DEPENDENCY_GUESS: the functorial map on the chosen total quotient
   sheaves.  Denominator admissibility and effective-equation regularity are
   stated separately below. -/
class Chapter02MeromorphicPullbackMap {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) where
  map : ∀ (U : X.Opens) (V : Y.Opens), V ≤ g ⁻¹ᵁ U →
    Chapter02MeromorphicSection X U →+* Chapter02MeromorphicSection Y V

theorem chapter02_flat_ring_hom_preserves_regular
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) (r : R)
    (hr : r ∈ nonZeroDivisors R) : φ r ∈ nonZeroDivisors S := by
  sorry

def chapter02MeromorphicSectionIsAdmissible {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (U : X.Opens) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U)
    (s : Chapter02MeromorphicSection X U) : Prop :=
  ∃ a b : Γ(Y, V), b ∈ nonZeroDivisors (Γ(Y, V)) ∧
    a ∈ nonZeroDivisors (Γ(Y, V)) ∧
    M.map U V hV s =
      chapter02RegularSectionMap Y V a *
        (chapter02RegularSectionMap Y V b)⁻¹

def chapter02PullbackEquationAdmissible {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor X) : Prop :=
  ∀ (i : D.index) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ D.openSet i),
    chapter02MeromorphicSectionIsAdmissible g (D.openSet i) V hV (D.equation i)

def chapter02EffectivePullbackEquationRegular {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02EffectiveCartierDivisor X) : Prop :=
  ∀ (i : D.divisor.index) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ D.divisor.openSet i),
    chapter02MeromorphicSectionIsRegular Y V
      (M.map (D.divisor.openSet i) V hV (D.divisor.equation i))

def chapter02CartierPullbackRepresents {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor X) (E : Chapter02CartierDivisor Y) : Prop :=
  ∀ (j : E.index),
    ∃ (i : D.index) (h : E.openSet j ≤ g ⁻¹ᵁ D.openSet i),
      (E.equation j : Chapter02MeromorphicSection Y (E.openSet j)) =
        M.map (D.openSet i) (E.openSet j) h
          (D.equation i : Chapter02MeromorphicSection X (D.openSet i))

structure Chapter02CartierPullbackData {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor X) where
  divisor : Chapter02CartierDivisor Y
  represents : chapter02CartierPullbackRepresents g D divisor
  equations_are_admissible : chapter02PullbackEquationAdmissible g D

theorem chapter02_cartier_pullback_exists_iff {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor X) :
    Nonempty (Chapter02CartierPullbackData g D) ↔
      chapter02PullbackEquationAdmissible g D := by
  sorry

theorem chapter02_pullback_equations_admissible_of_flat {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [Flat g] [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor X) :
    chapter02PullbackEquationAdmissible g D := by
  sorry

theorem chapter02_cartier_pullback_exists_of_flat {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [Flat g] [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02CartierDivisor X) :
    Nonempty (Chapter02CartierPullbackData g D) := by
  apply (chapter02_cartier_pullback_exists_iff g D).2
  exact chapter02_pullback_equations_admissible_of_flat g D

theorem chapter02_meromorphic_pullback_map_exists_of_flat {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [Flat g] :
    Nonempty (Chapter02MeromorphicPullbackMap g) := by
  sorry

theorem chapter02_cartier_restriction_to_open_exists {X : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] {U : X.Opens}
    [KU : Chapter02MeromorphicSheaf U] [M : Chapter02MeromorphicPullbackMap U.ι]
    (D : Chapter02CartierDivisor X) :
    Nonempty (Chapter02CartierPullbackData U.ι D) := by
  exact chapter02_cartier_pullback_exists_of_flat U.ι D

def Chapter02MapFactorsThroughSupport {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) (D : Chapter02EffectiveCartierDivisor X) : Prop :=
  ∃ h : Y ⟶ D.subscheme, h ≫ D.inclusion = g

/- LOCAL_DEPENDENCY_GUESS: compatibility of the meromorphic pullback map with
   the closed immersion defining an effective divisor is needed to derive the
   displayed zero equation from factorization through the support. -/
theorem chapter02_pullback_can_fail_on_support {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02EffectiveCartierDivisor X)
    (h : Chapter02MapFactorsThroughSupport g D)
    (hzero : ∃ (i : D.divisor.index) (V : Y.Opens)
      (hV : V ≤ g ⁻¹ᵁ D.divisor.openSet i),
      Nontrivial (Γ(Y, V)) ∧
        M.map (D.divisor.openSet i) V hV (D.divisor.equation i) = 0) :
    ¬ chapter02PullbackEquationAdmissible g D.divisor := by
  sorry

def chapter02EffectiveCartierPullbackIdeal {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) (D : Chapter02EffectiveCartierDivisor X) :
    Y.IdealSheafData :=
  D.ideal.comap g

def chapter02EffectiveCartierPullbackSubschemeIso {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) (D : Chapter02EffectiveCartierDivisor X) :
    (chapter02EffectiveCartierPullbackIdeal g D).subscheme ≅
      pullback g D.inclusion :=
  D.ideal.comapIso g

theorem chapter02_effective_pullback_ideal_is_effective {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) [Flat g] (D : Chapter02EffectiveCartierDivisor X) :
    Chapter02IsEffectiveCartierIdeal (chapter02EffectiveCartierPullbackIdeal g D) := by
  sorry

theorem chapter02_effective_pullback_equations_regular_of_flat {X Y : Scheme.{u}}
    [KX : Chapter02MeromorphicSheaf X] [KY : Chapter02MeromorphicSheaf Y]
    (g : Y ⟶ X) [Flat g] [M : Chapter02MeromorphicPullbackMap g]
    (D : Chapter02EffectiveCartierDivisor X) :
    chapter02EffectivePullbackEquationRegular g D := by
  sorry

theorem chapter02_effective_pullback_exact_sequence {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) [Flat g] (D : Chapter02EffectiveCartierDivisor X) :
    Nonempty (Chapter02CartierExactSequence
      (chapter02EffectiveCartierPullbackIdeal g D)) := by
  exact chapter02_effective_cartier_exact_sequence_of_ideal _
    (chapter02_effective_pullback_ideal_is_effective g D)

theorem chapter02_effective_pullback_is_base_change {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) (D : Chapter02EffectiveCartierDivisor X) :
    (chapter02EffectiveCartierPullbackSubschemeIso g D).inv ≫
        (chapter02EffectiveCartierPullbackIdeal g D).subschemeι =
      pullback.fst g D.inclusion := by
  exact D.ideal.comapIso_inv_subschemeι g

theorem chapter02_effective_pullback_is_closed_immersion {X Y : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    (g : Y ⟶ X) (D : Chapter02EffectiveCartierDivisor X) :
    IsClosedImmersion (pullback.fst g D.inclusion) := by
  infer_instance

structure Chapter02RelativeEffectiveCartierDivisor {X S : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X] (f : X ⟶ S) where
  divisor : Chapter02EffectiveCartierDivisor X
  flat_over_base : Flat (divisor.inclusion ≫ f)

def chapter02RelativeFiberIdeal {X S : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    {f : X ⟶ S} (D : Chapter02RelativeEffectiveCartierDivisor f) (s : S) :
    (f.fiber s).IdealSheafData :=
  D.divisor.ideal.comap (f.fiberι s)

def chapter02RelativeFiberSubschemeIso {X S : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    {f : X ⟶ S} (D : Chapter02RelativeEffectiveCartierDivisor f) (s : S) :
    (chapter02RelativeFiberIdeal D s).subscheme ≅
      pullback (f.fiberι s) D.divisor.inclusion :=
  D.divisor.ideal.comapIso (f.fiberι s)

theorem chapter02_relative_fiber_is_effective_cartier {X S : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    {f : X ⟶ S} (D : Chapter02RelativeEffectiveCartierDivisor f) (s : S) :
    Chapter02IsEffectiveCartierIdeal (chapter02RelativeFiberIdeal D s) := by
  sorry

theorem chapter02_relative_fiber_exact_sequence {X S : Scheme.{u}}
    [K : Chapter02MeromorphicSheaf X]
    {f : X ⟶ S} (D : Chapter02RelativeEffectiveCartierDivisor f) (s : S) :
    Nonempty (Chapter02CartierExactSequence (chapter02RelativeFiberIdeal D s)) := by
  exact chapter02_effective_cartier_exact_sequence_of_ideal _
    (chapter02_relative_fiber_is_effective_cartier D s)

/- The parameter-divisor warning is recorded by the elementary family
   `k[t] -> k[t]/(t)`: the parameter is regular upstairs and zero downstairs. -/

abbrev Chapter02BaseParameterRing (k : Type u) [CommRing k] := Polynomial k

abbrev Chapter02BaseSpecialFiberRing (k : Type u) [CommRing k] :=
  Chapter02BaseParameterRing k ⧸
    Ideal.span ({Polynomial.X} : Set (Chapter02BaseParameterRing k))

def chapter02BaseParameter (k : Type u) [CommRing k] : Chapter02BaseParameterRing k :=
  Polynomial.X

def chapter02BaseParameterSpecialization (k : Type u) [CommRing k] :
    Chapter02BaseParameterRing k →+* Chapter02BaseSpecialFiberRing k :=
  Ideal.Quotient.mk _

theorem chapter02_base_parameter_is_regular (k : Type u) [Nontrivial k] [CommRing k] :
    chapter02BaseParameter k ∈ nonZeroDivisors (Chapter02BaseParameterRing k) := by
  sorry

theorem chapter02_base_parameter_restricts_to_zero (k : Type u) [CommRing k] :
    chapter02BaseParameterSpecialization k (chapter02BaseParameter k) = 0 := by
  sorry

theorem chapter02_base_parameter_is_not_regular_on_special_fiber
    (k : Type u) [Field k] :
    chapter02BaseParameterSpecialization k (chapter02BaseParameter k) ∉
      nonZeroDivisors (Chapter02BaseSpecialFiberRing k) := by
  sorry

theorem chapter02_base_parameter_fiber_warning (k : Type u) [Field k] :
    chapter02BaseParameter k ∈ nonZeroDivisors (Chapter02BaseParameterRing k) ∧
      chapter02BaseParameterSpecialization k (chapter02BaseParameter k) = 0 ∧
      chapter02BaseParameterSpecialization k (chapter02BaseParameter k) ∉
        nonZeroDivisors (Chapter02BaseSpecialFiberRing k) := by
  exact ⟨chapter02_base_parameter_is_regular k,
    chapter02_base_parameter_restricts_to_zero k,
    chapter02_base_parameter_is_not_regular_on_special_fiber k⟩

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter02
