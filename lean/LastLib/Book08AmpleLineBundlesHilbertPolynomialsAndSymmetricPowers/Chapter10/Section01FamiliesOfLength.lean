import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Dependencies
import Mathlib.RingTheory.AdjoinRoot

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Set

universe u

/-! ## 10.1. Families of length `d` -/

/-- A closed subscheme of `X_T` which is finite locally free of constant rank `d`. -/
def Chapter10FamilyOfLength {X S T : Scheme} (q : X ⟶ S) (t : T ⟶ S) (d : ℕ) : Type u :=
  {Z : Chapter10ClosedSubscheme (pullback q t) //
    Chapter10FiniteLocallyFreeProfile (Z.subschemeι ≫ pullback.snd q t) d}

def chapter10FamilyProjection {X S T : Scheme} (q : X ⟶ S) (t : T ⟶ S)
    (Z : Chapter10ClosedSubscheme (pullback q t)) : Z.subscheme ⟶ T :=
  Z.subschemeι ≫ pullback.snd q t

theorem chapter10FamilyOfLength_rank {X S T : Scheme} (q : X ⟶ S) (t : T ⟶ S) (d : ℕ)
    (Z : Chapter10FamilyOfLength q t d) (y : T) :
    Chapter10FiberLength (chapter10FamilyProjection q t Z.1) y = d := by
  exact Z.2.rank y

theorem chapter10FamilyOfLength_geometricFiber_isArtinian {X S T : Scheme}
    (q : X ⟶ S) (t : T ⟶ S) (d : ℕ) (Z : Chapter10FamilyOfLength q t d) (y : T) :
    IsArtinianScheme ((chapter10FamilyProjection q t Z.1).fiber y) := by
  sorry

abbrev chapter10TruncatedPolynomialRing (k : Type u) [Field k] (d : ℕ) :=
  Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ d}

def Chapter10NonreducedPointLengthProfile (k : Type u) [Field k] (d : ℕ) : Prop :=
    Module.Finite k (chapter10TruncatedPolynomialRing k d) ∧
    Module.Flat k (chapter10TruncatedPolynomialRing k d) ∧
    Module.finrank k (chapter10TruncatedPolynomialRing k d) = d ∧
    ¬ _root_.IsReduced (chapter10TruncatedPolynomialRing k d)

theorem chapter10_truncated_polynomial_is_a_nonreduced_point_of_length
    (k : Type u) [Field k] {d : ℕ} (hd : 2 ≤ d) :
    Chapter10NonreducedPointLengthProfile k d := by
  sorry

/-!
The next definition is the actual base-change operation on the canonical
ideal-sheaf presentation.  Its rank proof is deferred to the global
finite-flat base-change API, while the object itself is not hidden behind an
axiom or a second notion of closed subscheme.
-/

def chapter10FamilyBaseChange {X S T T' : Scheme} (q : X ⟶ S) (t : T ⟶ S)
    (u : T' ⟶ T) (d : ℕ) (Z : Chapter10FamilyOfLength q t d) :
    Chapter10FamilyOfLength q (u ≫ t) d :=
  ⟨Z.1.comap (chapter10BaseChangeMap q t u), by sorry⟩

theorem chapter10FamilyBaseChange_rank {X S T T' : Scheme} (q : X ⟶ S) (t : T ⟶ S)
    (u : T' ⟶ T) (d : ℕ) (Z : Chapter10FamilyOfLength q t d) (y : T') :
    Chapter10FiberLength
        (chapter10FamilyProjection q (u ≫ t)
          (chapter10FamilyBaseChange q t u d Z).1) y = d := by
  sorry

/-!
The functor is written on the over-category of `S`, so the source's phrase
"set-valued functor" has an explicit domain.  The separatedness assumption is
kept on the book-facing alias because it is what makes the moduli interpretation
set-valued via uniqueness of maps between closed subschemes over `X_T`.
-/

def chapter10FamilyFunctor {X S : Scheme} (q : X ⟶ S) (d : ℕ) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := Chapter10FamilyOfLength q T.unop.hom d
  map := fun {T U} (f : T ⟶ U) =>
    TypeCat.ofHom (fun Z : Chapter10FamilyOfLength q T.unop.hom d => by
      simpa only [Over.w] using
        (chapter10FamilyBaseChange q T.unop.hom f.unop.left d Z))
  map_id := by
    intro T
    ext Z
    sorry
  map_comp := by
    intro T U V f g
    ext Z
    sorry

def chapter10SeparatedFamilyFunctor {X S : Scheme} (q : X ⟶ S) (d : ℕ)
    [IsSeparated q] : (Over S)ᵒᵖ ⥤ Type u :=
  chapter10FamilyFunctor q d

structure Chapter10FamilyIsomorphism {X S T : Scheme} {q : X ⟶ S} {t : T ⟶ S} {d : ℕ}
    (Z W : Chapter10FamilyOfLength q t d) where
  hom : Z.1.subscheme ≅ W.1.subscheme
  over : hom.hom ≫ W.1.subschemeι = Z.1.subschemeι

theorem chapter10_family_isomorphism_unique {X S T : Scheme} (q : X ⟶ S) (t : T ⟶ S)
    (d : ℕ) [IsSeparated q] (Z W : Chapter10FamilyOfLength q t d)
    (α β : Chapter10FamilyIsomorphism Z W) : α = β := by
  sorry

structure Chapter10RelativeSection {X S T : Scheme} (q : X ⟶ S) (t : T ⟶ S) where
  section_ : T ⟶ X
  over : section_ ≫ q = t

def chapter10SectionGraph {X S T : Scheme} {q : X ⟶ S} {t : T ⟶ S}
    (s : Chapter10RelativeSection q t) : T ⟶ pullback q t :=
  pullback.lift s.section_ (𝟙 T) (by simp [s.over])

def Chapter10GraphsPairwiseDisjoint {X S T : Scheme} {q : X ⟶ S} {t : T ⟶ S}
    {ι : Type u} (sections : ι → Chapter10RelativeSection q t) : Prop :=
  ∀ i j, i ≠ j →
    Disjoint (Set.range (chapter10SectionGraph (sections i)))
      (Set.range (chapter10SectionGraph (sections j)))

def Chapter10GraphCollision {X S T : Scheme} {q : X ⟶ S} {t : T ⟶ S}
    {ι : Type u} (sections : ι → Chapter10RelativeSection q t) : Prop :=
  ∃ i j, i ≠ j ∧
    (Set.range (chapter10SectionGraph (sections i)) ∩
      Set.range (chapter10SectionGraph (sections j))).Nonempty

theorem chapter10_graph_collision_not_pairwise_disjoint {X S T : Scheme}
    {q : X ⟶ S} {t : T ⟶ S} {ι : Type u}
    (sections : ι → Chapter10RelativeSection q t)
    (h : Chapter10GraphCollision sections) :
    ¬ Chapter10GraphsPairwiseDisjoint sections := by
  sorry

theorem chapter10_disjoint_graphs_give_family {X S T : Scheme} (q : X ⟶ S) (t : T ⟶ S)
    {ι : Type u} [Fintype ι] (sections : ι → Chapter10RelativeSection q t)
    (h : Chapter10GraphsPairwiseDisjoint sections) :
    Nonempty (Chapter10FamilyOfLength q t (Fintype.card ι)) := by
  sorry

/-!
The predicate below is the scheme-theoretic content of the warning that a
collision cannot retain multiplicity inside a reduced union: the replacement
family must carry a non-reduced infinitesimal thickening.
-/
def Chapter10InfinitesimalThickening {X : Scheme}
    (Z : Chapter10ClosedSubscheme X) : Prop :=
  ¬ IsReduced Z.subscheme

structure Chapter10CollisionMultiplicityData {X S T : Scheme} (q : X ⟶ S) (t : T ⟶ S)
    {ι : Type u} (sections : ι → Chapter10RelativeSection q t) [Fintype ι] where
  family : Chapter10FamilyOfLength q t (Fintype.card ι)
  thickening : Chapter10InfinitesimalThickening family.1
  support_eq_graphs :
    family.1.support.carrier =
      ⋃ i, Set.range (chapter10SectionGraph (sections i))

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
