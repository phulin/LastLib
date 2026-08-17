import LastLib.Book04AdelesAndIdeles.Chapter15.Section04DoubleQuotientsAndLattices

namespace LastLib.Book04AdelesAndIdeles.Chapter15

noncomputable section

open Set Filter NumberField
open scoped RestrictedProduct

/-! ## 15.5. Automorphic functions in adelic form -/

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-! ### The quotient and regularity data -/

/-- A function on the double quotient, before imposing analytic conditions. -/
abbrev Chapter15FunctionOnAutomorphicQuotient (n : ℕ)
    (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) :=
  chapter15MatrixAutomorphicDoubleQuotient (R := R) (K := K) n Kf → ℂ

/- The chapter intentionally does not choose one analytic category at infinity.
   The specification is shared by all functions at the chosen level: keeping
   it separate from an individual function prevents the conditions from being
   discharged by choosing `Set.univ` separately for that function. -/
structure Chapter15AutomorphicConditionSpec (n : ℕ) where
  regularity : Set (Chapter15GLnAdeles n R K → ℂ)
  growth : Set (Chapter15GLnAdeles n R K → ℂ)
  finiteness : Set (Chapter15GLnAdeles n R K → ℂ)

structure Chapter15AutomorphicConditions (n : ℕ)
    (S : Chapter15AutomorphicConditionSpec (R := R) (K := K) n)
    (F : Chapter15GLnAdeles n R K → ℂ) : Prop where
  regularity_holds : F ∈ S.regularity
  growth_holds : F ∈ S.growth
  finiteness_holds : F ∈ S.finiteness

/- Cuspidality is an optional extra condition in the source, so it is not a
required field of the ambient automorphic-function interface. -/

/-- An adelic automorphic function at a finite level, represented on the ambient group. -/
structure Chapter15AutomorphicFunction (n : ℕ)
    (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (S : Chapter15AutomorphicConditionSpec (R := R) (K := K) n) where
  toFun : Chapter15GLnAdeles n R K → ℂ
  left_invariant : ∀ γ : Matrix.GeneralLinearGroup (Fin n) K,
    ∀ g, toFun (chapter15PrincipalMatrix n γ * g) = toFun g
  right_invariant : ∀ g k, k ∈ chapter15GlobalLevelSubgroup n Kf →
    toFun (g * k) = toFun g
  conditions : Chapter15AutomorphicConditions n S toFun

instance (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (S : Chapter15AutomorphicConditionSpec (R := R) (K := K) n) :
    CoeFun (Chapter15AutomorphicFunction (R := R) (K := K) n Kf S)
      (fun _ => Chapter15GLnAdeles n R K → ℂ) :=
  ⟨Chapter15AutomorphicFunction.toFun⟩

/-- Pull a function on the quotient back to the ambient adelic group. -/
def chapter15AutomorphicFunctionPullback
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (F : Chapter15FunctionOnAutomorphicQuotient n Kf) :
    Chapter15GLnAdeles n R K → ℂ :=
  fun g => F (chapter15DoubleQuotientMk
    (chapter15PrincipalMatrix (R := R) (K := K) n).range
    (chapter15GlobalLevelSubgroup n Kf) g)

def chapter15AutomorphicFunctionDescend
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (F : Chapter15GLnAdeles n R K → ℂ)
    {S : Chapter15AutomorphicConditionSpec (R := R) (K := K) n}
    (_hconditions : Chapter15AutomorphicConditions n S F)
    (hleft : ∀ γ : Matrix.GeneralLinearGroup (Fin n) K, ∀ g,
      F (chapter15PrincipalMatrix n γ * g) = F g)
    (hright : ∀ g k, k ∈ chapter15GlobalLevelSubgroup n Kf →
      F (g * k) = F g) :
    Chapter15FunctionOnAutomorphicQuotient n Kf := by
  refine Quotient.lift F ?_
  intro x y hxy
  rcases hxy with ⟨h, hh, k, hk, heq⟩
  rcases hh with ⟨γ, rfl⟩
  calc
    F x = F (x * k) := (hright x k hk).symm
    _ = F (chapter15PrincipalMatrix n γ * (x * k)) :=
      (hleft γ (x * k)).symm
    _ = F (chapter15PrincipalMatrix n γ * x * k) := by rw [mul_assoc]
    _ = F y := by rw [heq]

theorem chapter15AutomorphicFunctionDescend_pullback
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (F : Chapter15GLnAdeles n R K → ℂ)
    {S : Chapter15AutomorphicConditionSpec (R := R) (K := K) n}
    (hconditions : Chapter15AutomorphicConditions n S F)
    (hleft : ∀ γ : Matrix.GeneralLinearGroup (Fin n) K, ∀ g,
      F (chapter15PrincipalMatrix n γ * g) = F g)
    (hright : ∀ g k, k ∈ chapter15GlobalLevelSubgroup n Kf →
      F (g * k) = F g) :
    chapter15AutomorphicFunctionPullback n Kf
        (chapter15AutomorphicFunctionDescend n Kf F hconditions hleft hright) = F := by
  sorry

theorem chapter15AutomorphicFunctionPullback_injective
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K)) :
    Function.Injective (chapter15AutomorphicFunctionPullback (R := R) (K := K) n Kf) := by
  sorry

theorem chapter15AutomorphicFunctionPullback_left_invariant
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (F : Chapter15FunctionOnAutomorphicQuotient n Kf)
    (γ : Matrix.GeneralLinearGroup (Fin n) K)
    (g : Chapter15GLnAdeles n R K) :
    chapter15AutomorphicFunctionPullback n Kf F
        (chapter15PrincipalMatrix n γ * g) =
      chapter15AutomorphicFunctionPullback n Kf F g := by
  sorry

theorem chapter15AutomorphicFunctionPullback_right_invariant
    (n : ℕ) (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (F : Chapter15FunctionOnAutomorphicQuotient n Kf)
    (g : Chapter15GLnAdeles n R K) (k : Chapter15GLnAdeles n R K)
    (hk : k ∈ chapter15GlobalLevelSubgroup n Kf) :
    chapter15AutomorphicFunctionPullback n Kf F (g * k) =
      chapter15AutomorphicFunctionPullback n Kf F g := by
  sorry

/-! ### Right translation and level change -/

/-- Functions on the left quotient, with no fixed finite level. -/
structure Chapter15LeftAutomorphicFunction (n : ℕ) where
  toFun : Chapter15GLnAdeles n R K → ℂ
  left_invariant : ∀ γ : Matrix.GeneralLinearGroup (Fin n) K,
    ∀ g, toFun (chapter15PrincipalMatrix n γ * g) = toFun g

instance (n : ℕ) :
    CoeFun (Chapter15LeftAutomorphicFunction (R := R) (K := K) n)
      (fun _ => Chapter15GLnAdeles n R K → ℂ) :=
  ⟨Chapter15LeftAutomorphicFunction.toFun⟩

/-- Right translation by an adelic matrix. -/
def chapter15RightTranslate (n : ℕ) (a : Chapter15GLnAdeles n R K)
    (F : Chapter15LeftAutomorphicFunction (R := R) (K := K) n) :
    Chapter15LeftAutomorphicFunction (R := R) (K := K) n where
  toFun g := F (g * a)
  left_invariant := by
    intro γ g
    simpa [mul_assoc] using F.left_invariant γ (g * a)

theorem chapter15RightTranslate_apply
    (n : ℕ) (a g : Chapter15GLnAdeles n R K)
    (F : Chapter15LeftAutomorphicFunction (R := R) (K := K) n) :
    chapter15RightTranslate n a F g = F (g * a) :=
  rfl

theorem chapter15RightTranslate_comp
    (n : ℕ) (a b : Chapter15GLnAdeles n R K)
    (F : Chapter15LeftAutomorphicFunction (R := R) (K := K) n) :
    chapter15RightTranslate n b (chapter15RightTranslate n a F) =
      chapter15RightTranslate n (b * a) F := by
  sorry

/-- Right invariance under a finite level, separated from analytic regularity. -/
def chapter15RightKInvariant (n : ℕ)
    (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (F : Chapter15LeftAutomorphicFunction (R := R) (K := K) n) : Prop :=
  ∀ g k, k ∈ chapter15GlobalLevelSubgroup n Kf → F (g * k) = F g

/-- Right invariance under an arbitrary subgroup of the ambient adelic group. -/
def chapter15RightSubgroupInvariant {G : Type*} [Group G]
    (H : Subgroup G) (F : G → ℂ) : Prop :=
  ∀ g h, h ∈ H → F (g * h) = F g

/-- Conjugation of a level by right translation. -/
def chapter15ConjugateLevel {G : Type*} [Group G]
    (a : G) (Kf : Subgroup G) : Subgroup G :=
  Subgroup.map (MulAut.conj a).toMonoidHom Kf

theorem chapter15RightTranslate_preserves_level_up_to_conjugacy
    (n : ℕ) (a : Chapter15GLnAdeles n R K)
    (Kf : Subgroup (Chapter15FiniteMatrixGroup n R K))
    (F : Chapter15LeftAutomorphicFunction (R := R) (K := K) n)
    (hF : chapter15RightKInvariant n Kf F) :
    chapter15RightSubgroupInvariant
      (chapter15ConjugateLevel a (chapter15GlobalLevelSubgroup n Kf))
      (chapter15RightTranslate n a F) := by
  sorry

/-! ### A translation supported at one finite place -/

noncomputable def chapter15FiniteMatrixTranslationAt
    (n : ℕ) (v : Chapter15FinitePlace R)
    (h : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    Chapter15FiniteMatrixGroup n R K := by
  classical
  exact RestrictedProduct.mulSingle
    (fun w => chapter15FiniteMatrixIntegralSubgroup n w) v h

def chapter15GlobalMatrixTranslationAt
    (n : ℕ) (v : Chapter15FinitePlace R)
    (h : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    Chapter15GLnAdeles n R K :=
  chapter15FiniteMatrixInclusion
    (R := R) (K := K) n (chapter15FiniteMatrixTranslationAt n v h)

theorem chapter15FiniteMatrixTranslationAt_apply_same
    (n : ℕ) (v : Chapter15FinitePlace R)
    (h : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    chapter15FiniteMatrixTranslationAt n v h v = h := by
  classical
  simp [chapter15FiniteMatrixTranslationAt]

theorem chapter15FiniteMatrixTranslationAt_apply_ne
    (n : ℕ) (v w : Chapter15FinitePlace R) (h : w ≠ v)
    (x : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    chapter15FiniteMatrixTranslationAt n v x w = 1 := by
  classical
  simp [chapter15FiniteMatrixTranslationAt, h]

theorem chapter15FiniteMatrixTranslationAt_is_integral_off_place
    (n : ℕ) (v : Chapter15FinitePlace R)
    (h : Matrix.GeneralLinearGroup (Fin n) (v.adicCompletion K)) :
    ∀ᶠ w : Chapter15FinitePlace R in Filter.cofinite,
      chapter15FiniteMatrixTranslationAt n v h w ∈
        chapter15FiniteMatrixIntegralSubgroup n w := by
  sorry

/-! ### Almost-everywhere unramified tails -/

/-- The exact almost-everywhere condition used by restricted tensor products. -/
def chapter15AlmostEverywhereUnramified
    (P : Chapter15FinitePlace R → Prop) : Prop :=
  ∀ᶠ v : Chapter15FinitePlace R in Filter.cofinite, P v

structure Chapter15UnramifiedTail (ι : Type*) (P : ι → Prop) where
  unramified : ∀ᶠ i : ι in Filter.cofinite, P i

theorem chapter15_level_changes_only_at_finitely_many_places
    (n : ℕ) (L : Chapter15FiniteMatrixLevel (R := R) (K := K) n) :
    ∃ S : Finset (Chapter15FinitePlace R),
      ∀ v ∉ S, L.localSubgroup v = chapter15FiniteMatrixIntegralSubgroup n v :=
  L.standard_outside_finite

/- The chapter records no irreducible-decomposition, multiplicity, cuspidal-spectrum,
or trace-formula theorem.  Those are analytic results beyond the ambient quotient. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter15
