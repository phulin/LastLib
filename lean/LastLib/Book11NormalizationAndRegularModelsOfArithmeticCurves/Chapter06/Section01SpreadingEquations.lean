import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02
open scoped AlgebraicGeometry

universe u v

/-! ### 6.1 Spreading equations -/

abbrev chapter06EquationIdeal
    (E : Chapter06HomogeneousEquations A N) : Ideal (MvPolynomial (Fin (N + 1)) A) :=
  Ideal.span (Set.range E.equation)

structure Chapter06SpreadFamily
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C) where
  open : (Chapter06BaseScheme R).Opens
  open_nonempty : open ≠ ⊥
  complement_finite : Set.Finite ((open : Set (Chapter06BaseScheme R))ᶜ)
  baseEquations : Chapter06HomogeneousEquations R E.dimension
  genericEquations : Chapter06HomogeneousEquations (FractionRing R) E.dimension
  clearedEquations : Chapter06ClearedHomogeneousEquations R genericEquations
  baseEquations_eq_cleared : baseEquations = clearedEquations.base
  carrier : Scheme.{u}
  structureMap : carrier ⟶ open.toScheme
  ambient : chapter02ProjectiveSpace open.toScheme E.dimension
  ambientMap : ambient ⟶ open.toScheme
  ambientMap_eq : ambientMap = chapter02ProjectiveSpaceProjection open.toScheme E.dimension
  embedding : carrier ⟶ ambient
  closedImmersion : IsClosedImmersion embedding
  over : embedding ≫ ambientMap = structureMap
  genericMap : Spec (.of (FractionRing R)) ⟶ open.toScheme
  genericMap_over : genericMap ≫ open.ι = chapter06GenericBaseMap R
  genericFiber : Chapter06GenericFiberIdentification R C (structureMap ≫ open.ι)
  locallyOfFiniteType : LocallyOfFiniteType structureMap
  locallyOfFinitePresentation : LocallyOfFinitePresentation structureMap
  /- LOCAL_DEPENDENCY_GUESS: the pinned relative-Proj API does not yet expose
  the comparison between a finite homogeneous list and the resulting
  scheme-theoretic ideal sheaf on a non-affine base open. -/
  equations_define_carrier : Prop
  generic_equations_are_equations_of_embedding : Prop

structure Chapter06GoodSpreadFamily
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C)
    extends Chapter06SpreadFamily C E where
  flat : Flat structureMap
  smooth : Smooth structureMap

theorem chapter06_clear_denominators
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C)
    (G : Chapter06HomogeneousEquations (FractionRing R) E.dimension) :
    Nonempty (Chapter06ClearedHomogeneousEquations R G) := by
  sorry

theorem chapter06_spreading_out
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C) :
    Nonempty (Chapter06SpreadFamily C E) := by
  sorry

theorem chapter06_spread_can_be_made_flat_and_smooth
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C)
    (F : Chapter06SpreadFamily C E) :
    ∃ G : Chapter06GoodSpreadFamily C E,
      G.open ≤ F.open := by
  sorry

theorem chapter06_spread_restriction_preserves_generic_fiber
    (C : Chapter06SmoothProjectiveCurve R)
    (E : Chapter06ProjectiveEmbedding C)
    (F : Chapter06GoodSpreadFamily C E) :
    F.genericFiber.iso.hom ≫ C.structureMap =
      pullback.snd (F.structureMap ≫ F.open.ι) (chapter06GenericBaseMap R) :=
  F.genericFiber.over

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06
