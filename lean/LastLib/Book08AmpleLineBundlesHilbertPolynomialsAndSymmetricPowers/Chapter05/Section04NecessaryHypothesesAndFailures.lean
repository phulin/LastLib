import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Section03DescentOfAmplenessAndProjectivity

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
  nonempty : ∃ s : S, s ∈ U
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

/- A proper morphism can still exhibit the gap between fiberwise and relative positivity when
the finite-presentation and uniformity hypotheses are absent. -/
structure ProperFiberwiseAmpleButNotRelativelyAmple {X S : Scheme.{u}}
    (f : X ⟶ S) (L : LineBundle X) : Prop where
  proper : IsProper f
  fiberwise_ample : IsFiberwiseAmple f L
  not_relatively_ample : ¬ IsAmple f L

theorem veryAmple_after_positive_power_implies_ample
    {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
    (hfqc : QuasiCompact f) (P : LineBundlePowers L)
    (h : IsVeryAmpleAfterPositivePower f L P) :
    IsAmple f L := by sorry

theorem veryAmple_positive_power_after_faithfullyFlat_baseChange_implies_ample
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (P : LineBundlePowers L)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (h : ∃ n, 0 < n ∧
      IsVeryAmple (baseChangeToBase f g) (baseChangeLineBundle f g (P.power n))) :
    IsAmple f L := by
  obtain ⟨n, hn, hV⟩ := h
  let _ : QuasiCompact f := hfqc
  let _ : QuasiCompact g := hgqc
  let _ : QuasiSeparated f := hfqs
  let _ : QuasiCompact (baseChangeToBase f g) := by
    change QuasiCompact (pullback.snd f g)
    infer_instance
  have hA : IsAmple (baseChangeToBase f g)
      (baseChangeLineBundle f g (P.power n)) :=
    Chapter04.chapter04_veryAmple_implies_ample
      (baseChangeToBase f g) (baseChangeLineBundle f g (P.power n)) hV
  let Q := P.pullback (baseChangeToSource f g)
  have hQ : IsAmple (baseChangeToBase f g) (Q.power n) := by
    change IsAmple (baseChangeToBase f g)
      (baseChangeLineBundle f g (P.power n))
    exact hA
  have hTensor : IsAmple (baseChangeToBase f g)
      ((baseChangeLineBundle f g L).tensorPower n) :=
    (isAmple_congr (baseChangeToBase f g) (Q.power_iso n)).mp hQ
  have hBase : IsAmple (baseChangeToBase f g)
      (baseChangeLineBundle f g L) :=
    Chapter04.chapter04_ample_of_ample_tensorPower
      (baseChangeToBase f g) (baseChangeLineBundle f g L) n hn hTensor
  exact ample_faithfullyFlat_descent f g L hfqc hfqs hgff hgqc hBase

/- This predicate records the corrected §5.4 warning: on an elliptic curve, a line bundle of degree
2 need not be very ample, whereas its square has degree 4 and is very ample. -/
def PowerRootSeparationFailureIsTheRelevantObstruction {X S : Scheme.{u}}
    (f : X ⟶ S) (L : LineBundle X) (P : LineBundlePowers L) : Prop :=
    PowerRootSeparationFailure f L P

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
