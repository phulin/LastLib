import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Dependencies

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
    IsAmple f L := by
  exact (ample_iff_faithfullyFlat_baseChange f g L hfqc hfqs hgff hgqc).2 hL

theorem projectivity_descent_with_polarization
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hproper : IsProper f) (hfp : LocallyOfFinitePresentation f)
    (hS : CompactSpace S)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (hL : IsAmple (baseChangeToBase f g) (baseChangeLineBundle f g L)) :
    IsAmple f L ∧ IsProjectiveMorphism f := by
  have hL' := ample_faithfullyFlat_descent f g L hfqc hfqs hgff hgqc hL
  let _ : CompactSpace S := hS
  let _ : QuasiCompact (𝟙 S) := by infer_instance
  let _ : IsProper f := hproper
  let _ : QuasiCompact f := hfqc
  let _ : LocallyOfFinitePresentation f := hfp
  exact ⟨hL', Chapter04.chapter04_proper_ample_is_projective f L hL'⟩

theorem projectivity_descent_from_upstairs_polarized_data
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : LineBundle X)
    (M : LineBundle (baseChange f g)) (hM : IsBaseChangeOf f g L M)
    (hfqc : QuasiCompact f) (hfqs : QuasiSeparated f)
    (hproper : IsProper f) (hfp : LocallyOfFinitePresentation f)
    (hS : CompactSpace S)
    (hgff : IsFaithfullyFlat g) (hgqc : QuasiCompact g)
    (hMample : IsAmple (baseChangeToBase f g) M) :
    IsAmple f L ∧ IsProjectiveMorphism f := by
  have hbase : IsAmple (baseChangeToBase f g)
      (baseChangeLineBundle f g L) :=
    (isAmple_congr (baseChangeToBase f g) hM).mp hMample
  exact projectivity_descent_with_polarization f g L hfqc hfqs hproper hfp hS hgff hgqc hbase

/- A projective morphism upstairs supplies some polarization, but the source warning says that
 this chosen polarization is not automatically a pullback from `X`.  Record its positivity and the
 independent projectivity datum without claiming descent data for the line bundle. -/
structure UnpolarizedUpstairsProjectivityData {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) where
  cover : IsFpqcCover g
  embeddingLineBundle : LineBundle (baseChange f g)
  embeddingLineBundle_ample :
    IsAmple (baseChangeToBase f g) embeddingLineBundle
  projective : IsProjectiveMorphism (baseChangeToBase f g)

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
