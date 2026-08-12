import LastLib.Book04AdelesAndIdeles.Chapter13.Dependencies

open scoped BigOperators NumberField NumberField.AdeleRing RestrictedProduct Classical

namespace LastLib.Book04AdelesAndIdeles.Chapter13

noncomputable section

/-!
## 13.2 Assembling multiplicative characters

The local factors in `Chapter13MultiplicativeCharacterFamily` are continuous characters of the
local multiplicative groups.  The tail condition is the exact “unramified almost everywhere”
condition from the text.
-/

structure Chapter13MultiplicativeCharacterFamily (K : Type*) [Field K] [NumberField K] where
  infinite : ∀ v : NumberField.InfinitePlace K,
    Chapter13ContinuousComplexCharacter ((v.Completion)ˣ)
  finite : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    Chapter13ContinuousComplexCharacter ((v.adicCompletion K)ˣ)
  finite_unramified : ∀ᶠ v in Filter.cofinite,
    chapter13TrivialOnSubgroup (Chapter13LocalUnitSubgroup K v) (finite v).toMonoidHom

abbrev Chapter13HeckeCharacter (K : Type*) [Field K] [NumberField K] :=
  Chapter13ClassCharacter K

def chapter13AssembledMultiplicativeCharacter (K : Type*) [Field K] [NumberField K]
    (F : Chapter13MultiplicativeCharacterFamily K) :
    Chapter13ContinuousComplexCharacter (Chapter13Idele K) :=
  { toMonoidHom :=
      { toFun := fun x =>
          (∏ v, F.infinite v ((MulEquiv.piUnits ((MulEquiv.prodUnits x).1)) v)) *
            ∏ᶠ v, F.finite v
              (chapter13FiniteIdeleCoordinate K ((MulEquiv.prodUnits x).2) v)
        map_one' := by sorry
        map_mul' := by sorry }
    continuous_toFun := by sorry }

theorem chapter13AssembledMultiplicativeCharacter_apply
    (K : Type*) [Field K] [NumberField K]
    (F : Chapter13MultiplicativeCharacterFamily K) (x : Chapter13Idele K) :
    chapter13AssembledMultiplicativeCharacter K F x =
      (∏ v, F.infinite v ((MulEquiv.piUnits ((MulEquiv.prodUnits x).1)) v)) *
        ∏ᶠ v, F.finite v
          (chapter13FiniteIdeleCoordinate K ((MulEquiv.prodUnits x).2) v) :=
  rfl

theorem chapter13AssembledMultiplicativeCharacter_finite_support
    (K : Type*) [Field K] [NumberField K]
    (F : Chapter13MultiplicativeCharacterFamily K) (x : Chapter13Idele K) :
    (Set.Finite {v |
      F.finite v (chapter13FiniteIdeleCoordinate K ((MulEquiv.prodUnits x).2) v) ≠ 1}) := by
  sorry

theorem chapter13AssembledMultiplicativeCharacter_restricts_to_local_factors
    (K : Type*) [Field K] [NumberField K]
    (F : Chapter13MultiplicativeCharacterFamily K) :
    (∀ v : NumberField.InfinitePlace K,
      ∀ x, chapter13AssembledMultiplicativeCharacter K F
          (chapter13InfiniteLocalIdele K v x) = F.infinite v x) ∧
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ∀ x, chapter13AssembledMultiplicativeCharacter K F
          (chapter13FiniteLocalIdele K v x) = F.finite v x) := by
  sorry

/- The converse is the no-small-subgroups argument in the book: continuity of a character on the
idele group forces it to be trivial on the distinguished local unit groups at almost all places. -/

theorem chapter13_continuous_idele_character_factorization
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ContinuousComplexCharacter (Chapter13Idele K)) :
    ∃ F : Chapter13MultiplicativeCharacterFamily K,
      chapter13AssembledMultiplicativeCharacter K F = χ := by
  sorry

def chapter13DescendsToIdeleClass
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ContinuousComplexCharacter (Chapter13Idele K)) : Prop :=
  ∀ a : Kˣ, χ (chapter13PrincipalIdele K a) = 1

theorem chapter13_descends_iff_trivial_on_principal_ideles
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ContinuousComplexCharacter (Chapter13Idele K)) :
    chapter13DescendsToIdeleClass K χ ↔
      ∀ a : Kˣ, χ (chapter13PrincipalIdele K a) = 1 :=
  Iff.rfl

def chapter13DescendIdeleCharacter
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ContinuousComplexCharacter (Chapter13Idele K))
    (hχ : chapter13DescendsToIdeleClass K χ) : Chapter13ClassCharacter K :=
  { toMonoidHom :=
      QuotientGroup.lift (chapter13PrincipalIdeleSubgroup K) χ.toMonoidHom (by
        intro x hx
        rcases hx with ⟨a, rfl⟩
        exact hχ a)
    continuous_toFun := by sorry }

def chapter13PullbackIdeleClassCharacter
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ClassCharacter K) :
    Chapter13ContinuousComplexCharacter (Chapter13Idele K) :=
  χ.comp
    { toMonoidHom := QuotientGroup.mk' (chapter13PrincipalIdeleSubgroup K)
      continuous_toFun := by sorry }

theorem chapter13_pullback_descend_left_inverse
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ContinuousComplexCharacter (Chapter13Idele K))
    (hχ : chapter13DescendsToIdeleClass K χ) :
    chapter13PullbackIdeleClassCharacter K (chapter13DescendIdeleCharacter K χ hχ) = χ := by
  sorry

theorem chapter13_idele_class_character_iff
    (K : Type*) [Field K] [NumberField K]
    (χ : Chapter13ContinuousComplexCharacter (Chapter13Idele K)) :
    (∃ ψ : Chapter13ClassCharacter K,
      chapter13PullbackIdeleClassCharacter K ψ = χ) ↔
      chapter13DescendsToIdeleClass K χ := by
  sorry

/-! The idele module is the normalized absolute value.  Its codomain is kept as `ℝ` here, with a
separate positivity theorem; this avoids prematurely choosing between the equivalent positive-real
group models used by different Mathlib APIs. -/

def chapter13IdeleModule (K : Type*) [Field K] [NumberField K] :
    Chapter13Idele K → ℝ := fun x =>
  (∏ v,
      ‖((MulEquiv.piUnits ((MulEquiv.prodUnits x).1)) v : v.Completion)‖ ^ v.mult) *
    ∏ᶠ v,
      ‖(chapter13FiniteIdeleCoordinate K ((MulEquiv.prodUnits x).2) v : v.adicCompletion K)‖

def chapter13IdeleModuleHom (K : Type*) [Field K] [NumberField K] :
    Chapter13Idele K →* ℝ :=
  { toFun := chapter13IdeleModule K
    map_one' := by sorry
    map_mul' := by sorry }

theorem chapter13_idele_module_apply
    (K : Type*) [Field K] [NumberField K] (x : Chapter13Idele K) :
    chapter13IdeleModule K x =
      (∏ v,
          ‖((MulEquiv.piUnits ((MulEquiv.prodUnits x).1)) v : v.Completion)‖ ^ v.mult) *
        ∏ᶠ v,
          ‖(chapter13FiniteIdeleCoordinate K ((MulEquiv.prodUnits x).2) v : v.adicCompletion K)‖ :=
  rfl

theorem chapter13_idele_module_positive
    (K : Type*) [Field K] [NumberField K] (x : Chapter13Idele K) :
    0 < chapter13IdeleModule K x := by
  sorry

theorem chapter13_idele_module_continuous
    (K : Type*) [Field K] [NumberField K] :
    Continuous (chapter13IdeleModule K) := by
  sorry

theorem chapter13_idele_module_principal
    (K : Type*) [Field K] [NumberField K] (a : Kˣ) :
    chapter13IdeleModule K (chapter13PrincipalIdele K a) = 1 := by
  sorry

def chapter13IdeleClassModule (K : Type*) [Field K] [NumberField K] :
    Chapter13IdeleClass K →* ℝ :=
  QuotientGroup.lift (chapter13PrincipalIdeleSubgroup K)
    (chapter13IdeleModuleHom K) (by
      intro x hx
      rcases hx with ⟨a, rfl⟩
      exact chapter13_idele_module_principal K a)

theorem chapter13_idele_class_module_apply
    (K : Type*) [Field K] [NumberField K] (x : Chapter13Idele K) :
    chapter13IdeleClassModule K (QuotientGroup.mk' (chapter13PrincipalIdeleSubgroup K) x) =
      chapter13IdeleModule K x :=
  rfl

theorem chapter13_idele_class_module_positive
    (K : Type*) [Field K] [NumberField K] (x : Chapter13IdeleClass K) :
    0 < chapter13IdeleClassModule K x := by
  sorry

theorem chapter13_idele_module_has_infinite_image
    (K : Type*) [Field K] [NumberField K] :
    Set.Infinite (Set.range (chapter13IdeleClassModule K)) := by
  sorry

/- A finite-image class character is the book's ray-class character only after a modulus is chosen;
the finite-order/conductor API in Section 04 makes that choice explicit. -/

end
end LastLib.Book04AdelesAndIdeles.Chapter13
