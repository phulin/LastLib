import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Dependencies

/-!
# 5.4 Necessary hypotheses and failures

The counterexample predicates below make the warnings in the text explicit without asserting an
universal counterexample where the source only gives a qualitative obstruction.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05

noncomputable section

structure OpenPositivityCounterexample {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (U : S.Opens) : Prop where
  not_faithfullyFlat : ¬ IsFaithfullyFlat U.ι
  upstairs_veryAmple : IsVeryAmple (f ∣_ U) (L.pullback (f ⁻¹ᵁ U).ι)
  downstairs_not_veryAmple : ¬ IsVeryAmple f L

/- A nilpotent thickening is the intended geometric instance of this non-flat warning: a
surjective map of schemes alone does not supply the faithful tensor-reflection used in §5.2. -/
structure SurjectiveNonflatDescentFailure {X S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (L : LineBundle X) : Prop where
  surjective : Surjective g
  not_flat : ¬ Flat g
  upstairs_veryAmple : IsVeryAmple (baseChangeToBase f g) (baseChangeLineBundle f g L)
  downstairs_not_veryAmple : ¬ IsVeryAmple f L

def HasFiniteLinearSystem {X : Scheme.{u}} (M : X.Modules) : Prop :=
  Nonempty (FiniteSectionFamily M)

def FiberwiseProjectiveButNotGloballyFinite {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  (∀ s, IsProjectiveMorphism (f.fiberToSpecResidueField s)) ∧
    ¬ IsProjectiveMorphism f

def FiberwiseVeryAmpleButNotUniform {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) : Prop :=
  IsFiberwiseVeryAmple f L ∧ ¬ IsVeryAmple f L

theorem veryAmple_after_positive_power_implies_ample
    {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X) (P : LineBundlePowers L)
    (h : IsVeryAmpleAfterPositivePower f L P) :
    IsAmple f L := by sorry

theorem veryAmple_positive_power_after_faithfullyFlat_baseChange_implies_ample
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (P : LineBundlePowers L)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (h : ∃ n, 0 < n ∧
      IsVeryAmple (baseChangeToBase f g) (baseChangeLineBundle f g (P.power n))) :
    IsAmple f L := by sorry

/- SOURCE_ISSUE (§5.4): “For example, $\mathcal O_{\mathbf P^1}(2)$ is very ample while
$\mathcal O_{\mathbf P^1}(1)$ is also very ample, but on other varieties a square can embed when
the original bundle has too few sections.”  The displayed pair does not witness the warning
because both bundles are very ample; the final clause is also underspecified without a variety and
bundle.  Minimal replacement: “On an elliptic curve, a line bundle of degree 2 need not be very
ample, whereas its square has degree 4 and is very ample.” -/
def PowerRootSeparationFailureIsTheRelevantObstruction {X S : Scheme.{u}}
    (f : X ⟶ S) (L : LineBundle X) (P : LineBundlePowers L) : Prop :=
    PowerRootSeparationFailure f L P

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
