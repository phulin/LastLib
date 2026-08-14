import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01.Dependencies

/-!
# 1.1 Local descriptions and global objects

The declarations here isolate the double-overlap calculation and the two categorical words used
throughout descent: full faithfulness and effectivity.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01

noncomputable section

/-- The affine double overlap of an `A`-algebra `B`. -/
abbrev Chapter01DoubleOverlap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  Chapter01TensorProduct A B

/-- The first scalar view on the affine double overlap. -/
def chapter01DoubleOverlapLeft (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    B →ₐ[A] Chapter01DoubleOverlap A B :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)

/-- The second scalar view on the affine double overlap. -/
def chapter01DoubleOverlapRight (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    B →ₐ[A] Chapter01DoubleOverlap A B :=
  (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)

@[simp]
theorem chapter01DoubleOverlapLeft_apply
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (b : B) :
    chapter01DoubleOverlapLeft A B b = b ⊗ₜ[A] 1 := by
  rfl

@[simp]
theorem chapter01DoubleOverlapRight_apply
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (b : B) :
    chapter01DoubleOverlapRight A B b = 1 ⊗ₜ[A] b := by
  rfl

/-- The two scalar views agree on elements already coming from the base. -/
theorem chapter01DoubleOverlap_agrees_on_base
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (a : A) :
    chapter01DoubleOverlapLeft A B (algebraMap A B a) =
      chapter01DoubleOverlapRight A B (algebraMap A B a) := by
  simp [chapter01DoubleOverlapLeft, chapter01DoubleOverlapRight]

/-- The scheme-theoretic double overlap is the spectrum of the tensor product. -/
noncomputable def chapter01SpecDoubleOverlapIso
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    pullback (chapter01SpecMap (algebraMap A B)) (chapter01SpecMap (algebraMap A B)) ≅
      Spec (.of <| Chapter01DoubleOverlap A B) :=
  pullbackSpecIso A B B

/-- Under the double-overlap isomorphism, the first projection is the first scalar view. -/
theorem chapter01SpecDoubleOverlapIso_inv_fst
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (chapter01SpecDoubleOverlapIso A B).inv ≫
        pullback.fst (chapter01SpecMap (algebraMap A B))
          (chapter01SpecMap (algebraMap A B)) =
      chapter01SpecMap (chapter01DoubleOverlapLeft A B).toRingHom := by
  sorry

/-- Under the double-overlap isomorphism, the second projection is the second scalar view. -/
theorem chapter01SpecDoubleOverlapIso_inv_snd
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (chapter01SpecDoubleOverlapIso A B).inv ≫
        pullback.snd (chapter01SpecMap (algebraMap A B))
          (chapter01SpecMap (algebraMap A B)) =
      chapter01SpecMap (chapter01DoubleOverlapRight A B).toRingHom := by
  sorry

/-- A field spectrum has no nontrivial nonempty open pieces. -/
theorem chapter01_field_spec_open_is_empty_or_univ
    (K : Type u) [Field K] (U : (Spec (.of K)).Opens) :
    U = ⊥ ∨ U = ⊤ := by
  sorry

/-- An abstract cocycle records the three compatible identifications on a triple overlap. -/
structure Chapter01Cocycle (C : Type u) [Category C] where
  first second third : C
  firstToSecond : first ≅ second
  secondToThird : second ≅ third
  firstToThird : first ≅ third
  cocycle : firstToSecond ≪≫ secondToThird = firstToThird

/-- The full-faithfulness part of a descent comparison functor. -/
def Chapter01FullyFaithful {C D : Type u} [Category C] [Category D] (F : C ⥤ D) : Prop :=
  F.Full ∧ F.Faithful

/-- An upstairs object equipped with the compatibility predicate relevant to descent. -/
structure Chapter01CompatibleObject {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) (Compatible : D → Prop) where
  carrier : D
  compatible : Compatible carrier

/-- A witness that a compatible upstairs object is induced from downstairs. -/
structure Chapter01EffectivityWitness {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) (Compatible : D → Prop)
    (Z : Chapter01CompatibleObject F Compatible) where
  downstairs : C
  comparison : F.obj downstairs ≅ Z.carrier

/-- Effectivity for a specified class of compatible upstairs objects. -/
def Chapter01EffectiveFor {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) (Compatible : D → Prop) : Prop :=
  ∀ Z : Chapter01CompatibleObject F Compatible,
    Nonempty (Chapter01EffectivityWitness F Compatible Z)

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter01
