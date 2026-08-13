import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Section05TensorPowersAndOperations

/-!
# 5.3 Descent of ampleness and projectivity

The projectivity statement is recorded in its polarized form: an arbitrary embedding line bundle
chosen upstairs is not silently treated as descended data.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05

noncomputable section

theorem ample_iff_faithfullyFlat_baseChange
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g) :
    IsAmple f L ↔ IsAmple (baseChangeToBase f g) (baseChangeLineBundle f g L) := by sorry

theorem ample_faithfullyFlat_descent
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (hL : IsAmple (baseChangeToBase f g) (baseChangeLineBundle f g L)) :
    IsAmple f L := by sorry

theorem projectivity_descent_with_polarization
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hproper : IsProper f) (hfp : LocallyOfFinitePresentation f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (hL : IsAmple (baseChangeToBase f g) (baseChangeLineBundle f g L)) :
    IsAmple f L ∧ IsProjectiveMorphism f := by sorry

theorem projectivity_descent_from_upstairs_polarized_data
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (M : LineBundle (baseChange f g)) (hM : IsBaseChangeOf f g L M)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hproper : IsProper f) (hfp : LocallyOfFinitePresentation f)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (hMample : IsAmple (baseChangeToBase f g) M) :
    IsAmple f L ∧ IsProjectiveMorphism f := by sorry

/- A projective morphism upstairs supplies some polarization, but the source warning says that
this chosen line bundle is not automatically a pullback from `X`.  This structure records exactly
the available upstairs data without claiming a descent that has not been supplied. -/
structure UnpolarizedUpstairsProjectivityData {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) where
  embeddingLineBundle : LineBundle (baseChange f g)
  projective : IsProjectiveMorphism (baseChangeToBase f g)

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
