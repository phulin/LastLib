import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Section01FamiliesOfLength
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Section02RelativeEffectiveCartierDivisors
import Mathlib.CategoryTheory.NatIso

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

/-! ## 10.3. Divisors on smooth relative curves -/

abbrev Chapter10SmoothRelativeCurve {C S : Scheme} (c : C ⟶ S) : Prop :=
  SmoothOfRelativeDimension 1 c

def Chapter10RelativeDivisorOnBaseChange {C S T : Scheme} (c : C ⟶ S) (t : T ⟶ S)
    (d : ℕ) : Type u :=
  Chapter10RelativeEffectiveCartierDivisor (pullback.snd c t) d

theorem chapter10_smooth_curve_family_is_cartier
    {C S T : Scheme} (c : C ⟶ S) [Chapter10SmoothRelativeCurve c]
    (t : T ⟶ S) (d : ℕ) (Z : Chapter10FamilyOfLength c t d) :
    ∃ D : Chapter10RelativeDivisorOnBaseChange c t d, D.divisor.ideal = Z.1 := by
  sorry

noncomputable def chapter10FamilyToRelativeDivisor
    {C S T : Scheme} (c : C ⟶ S) [Chapter10SmoothRelativeCurve c]
    (t : T ⟶ S) (d : ℕ) (Z : Chapter10FamilyOfLength c t d) :
    Chapter10RelativeDivisorOnBaseChange c t d :=
  Classical.choose (chapter10_smooth_curve_family_is_cartier c t d Z)

theorem chapter10FamilyToRelativeDivisor_ideal
    {C S T : Scheme} (c : C ⟶ S) [Chapter10SmoothRelativeCurve c]
    (t : T ⟶ S) (d : ℕ) (Z : Chapter10FamilyOfLength c t d) :
    (chapter10FamilyToRelativeDivisor c t d Z).divisor.ideal = Z.1 := by
  exact Classical.choose_spec (chapter10_smooth_curve_family_is_cartier c t d Z)

def chapter10RelativeDivisorToFamily {C S T : Scheme} (c : C ⟶ S) (t : T ⟶ S) (d : ℕ)
    (D : Chapter10RelativeDivisorOnBaseChange c t d) :
    Chapter10FamilyOfLength c t d :=
  ⟨D.divisor.ideal, D.finiteLocallyFree⟩

theorem chapter10RelativeDivisorToFamily_ideal {C S T : Scheme} (c : C ⟶ S) (t : T ⟶ S)
    (d : ℕ) (D : Chapter10RelativeDivisorOnBaseChange c t d) :
    (chapter10RelativeDivisorToFamily c t d D).1 = D.divisor.ideal := by
  rfl

noncomputable def chapter10_length_d_family_divisor_equiv
    {C S T : Scheme} (c : C ⟶ S) [Chapter10SmoothRelativeCurve c]
    (t : T ⟶ S) (d : ℕ) :
    Chapter10FamilyOfLength c t d ≃ Chapter10RelativeDivisorOnBaseChange c t d where
  toFun := chapter10FamilyToRelativeDivisor c t d
  invFun := chapter10RelativeDivisorToFamily c t d
  left_inv := by
    intro Z
    apply Subtype.ext
    exact chapter10FamilyToRelativeDivisor_ideal c t d Z
  right_inv := by
    intro D
    apply chapter10_relative_effectiveCartierDivisor_ext
    exact (chapter10FamilyToRelativeDivisor_ideal c t d
      (chapter10RelativeDivisorToFamily c t d D)).trans
      (chapter10RelativeDivisorToFamily_ideal c t d D)

theorem chapter10_smooth_curve_length_and_divisor_functors_agree
    {C S T : Scheme} (c : C ⟶ S) [Chapter10SmoothRelativeCurve c]
    (t : T ⟶ S) (d : ℕ) :
    Nonempty (Chapter10FamilyOfLength c t d ≃
      Chapter10RelativeDivisorOnBaseChange c t d) :=
  ⟨chapter10_length_d_family_divisor_equiv c t d⟩

noncomputable def chapter10RelativeDivisorBaseChange
    {C S T T' : Scheme} (c : C ⟶ S) [Chapter10SmoothRelativeCurve c]
    (t : T ⟶ S) (u : T' ⟶ T) (d : ℕ)
    (D : Chapter10RelativeDivisorOnBaseChange c t d) :
    Chapter10RelativeDivisorOnBaseChange c (u ≫ t) d :=
  chapter10FamilyToRelativeDivisor c (u ≫ t) d
    (chapter10FamilyBaseChange c t u d
      (chapter10RelativeDivisorToFamily c t d D))

def chapter10RelativeDivisorFunctor {C S : Scheme} (c : C ⟶ S)
    [Chapter10SmoothRelativeCurve c] (d : ℕ) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := Chapter10RelativeDivisorOnBaseChange c T.unop.hom d
  map := fun {T U} (f : T ⟶ U) =>
    TypeCat.ofHom (fun D : Chapter10RelativeDivisorOnBaseChange c T.unop.hom d => by
      simpa only [Over.w] using
        (chapter10RelativeDivisorBaseChange c T.unop.hom f.unop.left d D))
  map_id := by
    intro T
    sorry
  map_comp := by
    intro T U V f g
    sorry

noncomputable def chapter10_length_d_family_divisor_functors_natIso
    {C S : Scheme} (c : C ⟶ S) [Chapter10SmoothRelativeCurve c] (d : ℕ) :
    chapter10FamilyFunctor c d ≅ chapter10RelativeDivisorFunctor c d := by
  refine NatIso.ofComponents (fun T => ?_) ?_
  · exact (chapter10_length_d_family_divisor_equiv c T.unop.hom d).toIso
  · intro T U f
    sorry

/-!
The preceding equivalence is where smoothness is used.  The node model from
§10.2 supplies the promised failure mode: its length-one point has a
non-principal ideal, so the finite-length and Cartier predicates separate.
-/

theorem chapter10_node_is_not_cartier_without_smoothness (k : Type u) [Field k] :
    ¬ ∃ a : chapter10NodeRing k,
      chapter10NodeIdeal k = Ideal.span {a} := by
  exact chapter10_node_ideal_is_not_principal k

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
