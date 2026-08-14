import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07.Dependencies

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07

open CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct

universe u

/-- The module-descent object attached to extension and restriction of scalars.

This is the canonical comonadic packaging of a module descent datum.  It is used here instead
of duplicating the two overlap maps and their cocycle in every algebraic structure. -/
abbrev Chapter07ModuleDescentDatum (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).toComonad).Coalgebra

theorem chapter07_faithfully_flat_reflects_linear_map_equality
    {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module.FaithfullyFlat A B] (f g : M →ₗ[A] N)
    (h : LinearMap.lTensor B f = LinearMap.lTensor B g) : f = g := by
  sorry

/- The Amitsur equalizer used by affine descent.  This is the exact sequence/equalizer interface
behind the informal phrase “equality of maps is reflected”. -/
theorem chapter07_amitsur_is_effective
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] : Algebra.IsEffective A B := by
  exact Algebra.IsEffective.of_faithfullyFlat

theorem chapter07_amitsur_equalizer_is_the_algebra_image
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] :
    TensorProduct.includeLeftRingHom.eqLocus TensorProduct.includeRight.toRingHom =
      Set.range (algebraMap A B) := by
  exact Algebra.IsEffective.eqLocus_includeLeft_includeRight
    (chapter07_amitsur_is_effective A B)

/-- The maps and equations which present an `A`-algebra structure on a commutative ring. -/
structure Chapter07AlgebraStructureData (A R : Type u) [CommRing A] [CommRing R]
    [Algebra A R] where
  mul : R ⊗[A] R →ₗ[A] R
  unit : A →ₗ[A] R
  mul_on_pure : ∀ x y : R, mul (x ⊗ₜ[A] y) = x * y
  unit_on_scalar : ∀ a : A, unit a = algebraMap A R a
  associative : ∀ x y z : R,
    mul (x ⊗ₜ[A] (y * z)) = mul ((x * y) ⊗ₜ[A] z)
  commutative : ∀ x y : R, mul (x ⊗ₜ[A] y) = mul (y ⊗ₜ[A] x)
  left_unit : ∀ x : R, mul (1 ⊗ₜ[A] x) = x
  right_unit : ∀ x : R, mul (x ⊗ₜ[A] 1) = x

/-- The canonical algebra structure data associated to an existing algebra instance. -/
def Chapter07AlgebraStructureData.canonical (A R : Type u) [CommRing A] [CommRing R]
    [Algebra A R] : Chapter07AlgebraStructureData A R where
  mul := (Algebra.TensorProduct.lmul' A).toLinearMap
  unit := Algebra.linearMap A R
  mul_on_pure := by sorry
  unit_on_scalar := by sorry
  associative := by sorry
  commutative := by sorry
  left_unit := by sorry
  right_unit := by sorry

@[ext]
theorem Chapter07AlgebraStructureData.ext {A R : Type u} [CommRing A] [CommRing R]
    [Algebra A R] (x y : Chapter07AlgebraStructureData A R)
    (hmul : x.mul = y.mul) (hunit : x.unit = y.unit) : x = y := by
  cases x
  cases y
  simp_all

/-- A descended algebra, including its comparison with the given algebra after base change. -/
structure Chapter07AlgebraDescentResult (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] where
  carrier : Type u
  commRing : CommRing carrier
  algebra :
    letI : CommRing carrier := commRing
    Algebra A carrier
  comparison :
    letI : CommRing carrier := commRing
    letI : Algebra A carrier := algebra
    Nonempty (B ⊗[A] carrier ≃ₐ[B] C)

structure Chapter07AlgebraDescentEquivalence
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (X Y : Chapter07AlgebraDescentResult A B C) where
  equivalence :
    letI : CommRing X.carrier := X.commRing
    letI : Algebra A X.carrier := X.algebra
    letI : CommRing Y.carrier := Y.commRing
    letI : Algebra A Y.carrier := Y.algebra
    Nonempty (X.carrier ≃ₐ[A] Y.carrier)

/-- An algebra descent datum consists of a module descent datum whose overlap is algebraic.

`overlap_is_algebra_equivalence` is intentionally kept as a named interface until the earlier
book's algebra-object presentation of the comonad is available.  It is not a free proposition:
the field is the compatibility assertion that the coaction/overlap map is an algebra equivalence. -/
structure Chapter07AlgebraDescentData (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] where
  moduleDatum : Chapter07ModuleDescentDatum A B
  carrier : moduleDatum.A = ModuleCat.of B C
  algebra_structure : Chapter07AlgebraStructureData B C
  overlap_is_algebra_equivalence : Prop

/- LOCAL_DEPENDENCY_GUESS: the earlier chapters' module full-faithfulness interface is not present
in this isolated workspace, so the algebra-object compatibility field above is the book-facing
bridge consumed by the descent theorem. -/
theorem chapter07_algebra_structure_descends
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    Nonempty (Chapter07AlgebraDescentResult A B C) := by
  sorry

theorem chapter07_algebra_structure_descends_unique_up_to_equivalence
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (D : Chapter07AlgebraDescentData A B C)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    ∀ X Y : Chapter07AlgebraDescentResult A B C,
      Nonempty (Chapter07AlgebraDescentEquivalence X Y) := by
  sorry

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07
