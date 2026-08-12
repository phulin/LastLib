import LastLib.Book04AdelesAndIdeles.Chapter06.Section07ConsequencesAndBoundaries

namespace LastLib.Book04AdelesAndIdeles.Chapter06

noncomputable section

/-! # Book 4, Chapter 6, Section 6.8: Adelic lattices and finite intersections -/

universe uK uO uInf uFin uHat uV uVA

variable {K : Type uK} {O : Type uO} {KInf : Type uInf} {Af : Type uFin}
  {Ohat : Type uHat}
variable [Field K] [CommRing O] [AddCommGroup KInf] [AddCommGroup Af]
  [AddCommGroup Ohat] [TopologicalSpace KInf] [TopologicalSpace Af]
  [TopologicalSpace Ohat]

variable {P : Chapter06AdeleData K O KInf Af Ohat}

/-- The box power `S^m`, represented as functions on `Fin m`. -/
def chapter06PiSet {α : Type*} (S : Set α) (m : ℕ) : Set (Fin m → α) :=
  Set.pi Set.univ fun _ => S

/-- The coordinatewise diagonal embedding into the rank-`m` full adeles. -/
def chapter06CoordinatewiseDiagonal
    (P : Chapter06AdeleData K O KInf Af Ohat) (m : ℕ) :
    (Fin m → K) →+
      ((Fin m → KInf) × (Fin m → Af)) where
  toFun x :=
    (fun i => P.globalToInfinite (x i), fun i => P.globalToFinite (x i))
  map_zero' := by
    apply Prod.ext <;> funext i <;> simp
  map_add' x y := by
    apply Prod.ext <;> funext i <;> simp

@[simp] theorem chapter06CoordinatewiseDiagonal_apply
    (P : Chapter06AdeleData K O KInf Af Ohat) (m : ℕ) (x : Fin m → K) :
    chapter06CoordinatewiseDiagonal P m x =
      (fun i => P.globalToInfinite (x i), fun i => P.globalToFinite (x i)) := rfl

/-- The compact covering set in rank `m`. -/
def chapter06CoordinatewiseFundamentalSet
    (P : Chapter06AdeleData K O KInf Af Ohat) (D : Set KInf) (m : ℕ) :
    Set ((Fin m → KInf) × (Fin m → Af)) :=
  chapter06PiSet D m ×ˢ
    chapter06PiSet (Set.range P.finiteIntegralEmbedding) m

theorem chapter06_coordinatewise_fundamental_set_compact
    (P : Chapter06AdeleData K O KInf Af Ohat) (D : Set KInf)
    (m : ℕ) (hD : IsCompact D) :
    IsCompact (chapter06CoordinatewiseFundamentalSet P D m) := by
  sorry

/-- The coordinatewise version of Lemma 6.1 and the archimedean reduction. -/
theorem chapter06_coordinatewise_reduced_to_fundamental_set
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) (m : ℕ)
    (x : (Fin m → KInf) × (Fin m → Af)) :
    ∃ a : Fin m → K,
      x - chapter06CoordinatewiseDiagonal P m a ∈
        chapter06CoordinatewiseFundamentalSet P D.carrier m := by
  sorry

theorem chapter06_coordinatewise_adelic_lattice
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) (m : ℕ) :
    Chapter06AdditiveLattice (chapter06CoordinatewiseDiagonal P m) := by
  sorry

/-- A basis-coordinate interface for a finite-dimensional adelic vector space.
It makes the reduction to the coordinatewise statement explicit without
choosing a noncanonical tensor-product presentation in this chapter. -/
structure Chapter06AdelicVectorSpaceData
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (V : Type uV) (VA : Type uVA)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup VA] [TopologicalSpace VA] where
  diagonal : V →+ VA
  rank : ℕ
  globalCoordinates : V ≃+ (Fin rank → K)
  adelicCoordinates : VA ≃+
    ((Fin rank → KInf) × (Fin rank → Af))
  diagonal_closed : IsClosed (Set.range diagonal)
  coordinates_compatible :
    adelicCoordinates.toAddMonoidHom.comp diagonal =
      (chapter06CoordinatewiseDiagonal P rank).comp
        globalCoordinates.toAddMonoidHom

namespace Chapter06AdelicVectorSpaceData

variable {V : Type uV} {VA : Type uVA}
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup VA] [TopologicalSpace VA]

@[simp] theorem coordinates_compatible_apply
    (W : Chapter06AdelicVectorSpaceData P V VA) (x : V) :
    W.adelicCoordinates (W.diagonal x) =
      chapter06CoordinatewiseDiagonal P W.rank (W.globalCoordinates x) := by
  change (W.adelicCoordinates.toAddMonoidHom.comp W.diagonal) x = _
  rw [W.coordinates_compatible]
  rfl

end Chapter06AdelicVectorSpaceData

/-- Finite-dimensional adelic vector spaces inherit discreteness and
cocompactness from the coordinatewise lattice. -/
theorem chapter06_finite_dimensional_adelic_lattice
    {V : Type uV} {VA : Type uVA}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup VA] [TopologicalSpace VA]
    (W : Chapter06AdelicVectorSpaceData P V VA)
    (D : Chapter06ArchimedeanCell P) :
    Chapter06AdditiveLattice W.diagonal := by
  sorry

/-- A compact set meets a discrete lattice in finitely many points. -/
theorem chapter06_compact_intersects_discrete_lattice_finitely
    {G : Type*} {H : Type*} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] (ι : G →+ H)
    (hι : Chapter06DiscreteEmbedding ι)
    (hclosed : IsClosed (Set.range ι)) (C : Set H)
    (hC : IsCompact C) :
    (Set.range ι ∩ C).Finite ∧ (ι ⁻¹' C).Finite := by
  sorry

/-- The bounded algebraic-integer finiteness consequence of the archimedean
lattice. -/
theorem chapter06_bounded_integral_elements_finite
    (P : Chapter06AdeleData K O KInf Af Ohat) (C : Set KInf)
    (hC : IsCompact C)
    (hι : Chapter06DiscreteEmbedding P.integerToInfinite)
    (hclosed : IsClosed (Set.range P.integerToInfinite)) :
    (P.integerToInfinite ⁻¹' C).Finite := by
  exact (chapter06_compact_intersects_discrete_lattice_finitely
    P.integerToInfinite hι hclosed C hC).2

/-- The finite-intersection statement for an arbitrary finite-dimensional
adelic vector space. -/
theorem chapter06_compact_intersects_adelic_vector_lattice_finitely
    {V : Type uV} {VA : Type uVA}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup VA] [TopologicalSpace VA]
    (W : Chapter06AdelicVectorSpaceData P V VA) (C : Set VA)
    (hC : IsCompact C) :
    (Set.range W.diagonal ∩ C).Finite := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter06
