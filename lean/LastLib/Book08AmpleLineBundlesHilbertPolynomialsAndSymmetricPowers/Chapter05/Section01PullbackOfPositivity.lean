import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Dependencies

/-!
# 5.1 Pullback of positivity

The declarations in this section deliberately have no flatness hypotheses: arbitrary scheme
base change preserves the explicit embedding and affine-chart tests used by positivity.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05

noncomputable section

theorem veryAmple_baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (L : LineBundle X)
    (hL : IsVeryAmple f L) :
    IsVeryAmple (baseChangeToBase f g) (baseChangeLineBundle f g L) := by sorry

theorem ample_baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (L : LineBundle X)
    (hL : IsAmple f L) :
    IsAmple (baseChangeToBase f g) (baseChangeLineBundle f g L) := by sorry

theorem quasiProjective_baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsQuasiProjectiveMorphism f) :
    IsQuasiProjectiveMorphism (baseChangeToBase f g) := by sorry

theorem projective_baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsProjectiveMorphism f) :
    IsProjectiveMorphism (baseChangeToBase f g) := by sorry

theorem veryAmple_restrict {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (L : LineBundle X)
    (hL : IsVeryAmple f L) :
    IsVeryAmple (f ∣_ U) (L.pullback (f ⁻¹ᵁ U).ι) := by sorry

theorem ample_restrict {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (L : LineBundle X)
    (hL : IsAmple f L) :
    IsAmple (f ∣_ U) (L.pullback (f ⁻¹ᵁ U).ι) := by sorry

theorem fiber_projective_of_projective {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (hf : IsProjectiveMorphism f) :
    IsProjectiveMorphism (f.fiberToSpecResidueField s) := by sorry

theorem fiber_veryAmple_of_veryAmple {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (L : LineBundle X) (hL : IsVeryAmple f L) :
    IsVeryAmple (f.fiberToSpecResidueField s) (L.pullback (f.fiberι s)) := by sorry

theorem fiber_ample_of_ample {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (L : LineBundle X)
    (hL : IsAmple f L) :
    IsAmple (f.fiberToSpecResidueField s) (L.pullback (f.fiberι s)) := by sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
