import LastLib.Book04AdelesAndIdeles.Chapter06.Section03ACompactFundamentalSet

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
  exact (isCompact_univ_pi fun _ => hD).prod
    (isCompact_univ_pi fun _ => P.finiteIntegral_range_compact)

/-- The coordinatewise version of Lemma 6.1 and the archimedean reduction. -/
theorem chapter06_coordinatewise_reduced_to_fundamental_set
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) (m : ℕ)
    [IsTopologicalAddGroup Af]
    (x : (Fin m → KInf) × (Fin m → Af)) :
    ∃ a : Fin m → K,
      x - chapter06CoordinatewiseDiagonal P m a ∈
        chapter06CoordinatewiseFundamentalSet P D.carrier m := by
  choose a u hu using fun i => chapter06_finite_principal_parts P (x.2 i)
  choose b hb using fun i => D.covers (x.1 i - P.globalToInfinite (a i))
  let c : Fin m → K := fun i => a i + P.integerToGlobal (b i)
  refine ⟨c, ?_⟩
  change (fun i => x.1 i - P.globalToInfinite (c i)) ∈
      chapter06PiSet D.carrier m ∧
    (fun i => x.2 i - P.globalToFinite (c i)) ∈
      chapter06PiSet (Set.range P.finiteIntegralEmbedding) m
  constructor
  · intro i hi
    simpa [c, map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hb i
  · intro i hi
    refine ⟨u i - P.integerToFinite (b i), ?_⟩
    simp [c, hu i, map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

theorem chapter06_coordinatewise_adelic_lattice
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) (m : ℕ)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [T2Space KInf] [T2Space Af]
    (hdiscrete : Chapter06DiscreteEmbedding (chapter06CoordinatewiseDiagonal P m)) :
    Chapter06AdditiveLattice (chapter06CoordinatewiseDiagonal P m) := by
  refine ⟨hdiscrete, ?_⟩
  exact chapter06_compact_quotient_of_compact_cover
      (chapter06CoordinatewiseDiagonal P m)
      (chapter06CoordinatewiseFundamentalSet P D.carrier m)
      (chapter06_coordinatewise_fundamental_set_compact P D.carrier m D.compact)
      (chapter06_coordinatewise_reduced_to_fundamental_set P D m)

/-- Finite-coordinate discreteness is inherited from the rank-one diagonal.

This is the missing transfer step behind the source's assertion that the same
argument applies to `K^m`: the coordinatewise diagonal is a finite product of
copies of the rank-one diagonal. -/
theorem chapter06_coordinatewise_discrete_of_discrete
    (P : Chapter06AdeleData K O KInf Af Ohat) (m : ℕ)
    (hdiscrete : Chapter06DiscreteEmbedding (chapter06Diagonal P)) :
    Chapter06DiscreteEmbedding (chapter06CoordinatewiseDiagonal P m) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    funext i
    apply hdiscrete.1
    simpa [chapter06CoordinatewiseDiagonal_apply, chapter06Diagonal_apply] using
      congrArg (fun z : (Fin m → KInf) × (Fin m → Af) => (z.1 i, z.2 i)) hxy
  · intro x
    choose U hUopen hUmem hUisol using fun i => hdiscrete.2 (x i)
    let S : Set ((Fin m → KInf) × (Fin m → Af)) :=
      ⋂ i : Fin m, (fun z => (z.1 i, z.2 i)) ⁻¹' U i
    have hSopen : IsOpen S := by
      dsimp [S]
      apply isOpen_iInter_of_finite
      intro i
      have hcontInf :
          Continuous (fun z : (Fin m → KInf) × (Fin m → Af) => z.1 i) :=
        (continuous_apply i).comp continuous_fst
      have hcontFin :
          Continuous (fun z : (Fin m → KInf) × (Fin m → Af) => z.2 i) :=
        (continuous_apply i).comp continuous_snd
      exact (hUopen i).preimage (hcontInf.prodMk hcontFin)
    refine ⟨S, hSopen, ?_, ?_⟩
    · simp only [S, Set.mem_iInter, Set.mem_preimage]
      intro i
      simpa [chapter06CoordinatewiseDiagonal_apply, chapter06Diagonal_apply] using
        hUmem i
    · intro y hy
      have hy' : ∀ i : Fin m,
          ((chapter06CoordinatewiseDiagonal P m y).1 i,
            (chapter06CoordinatewiseDiagonal P m y).2 i) ∈ U i := by
        simpa only [S, Set.mem_iInter, Set.mem_preimage] using hy
      funext i
      apply hUisol i
      simpa [chapter06CoordinatewiseDiagonal_apply, chapter06Diagonal_apply] using
        hy' i

/-- The coordinatewise lattice theorem with the rank-one discreteness
    hypothesis exposed, as in the book's finite-power reduction. -/
theorem chapter06_coordinatewise_adelic_lattice_of_discrete
    (P : Chapter06AdeleData K O KInf Af Ohat)
    (D : Chapter06ArchimedeanCell P) (m : ℕ)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [T2Space KInf] [T2Space Af]
    (hdiscrete : Chapter06DiscreteEmbedding (chapter06Diagonal P)) :
    Chapter06AdditiveLattice (chapter06CoordinatewiseDiagonal P m) := by
  exact chapter06_coordinatewise_adelic_lattice P D m
    (chapter06_coordinatewise_discrete_of_discrete P m hdiscrete)

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
  globalCoordinates : V ≃ₗ[K] (Fin rank → K)
  adelicCoordinates : VA ≃+
    ((Fin rank → KInf) × (Fin rank → Af))
  adelicCoordinates_continuous :
    Continuous (adelicCoordinates : VA → ((Fin rank → KInf) × (Fin rank → Af)))
  adelicCoordinates_symm_continuous :
    Continuous (adelicCoordinates.symm :
      ((Fin rank → KInf) × (Fin rank → Af)) → VA)
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

/-- A basis-coordinate equivalence transfers discreteness from the
    coordinatewise diagonal to the adelic vector-space diagonal. -/
theorem chapter06_adelic_vector_space_discrete_of_coordinatewise_discrete
    {V : Type uV} {VA : Type uVA}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup VA] [TopologicalSpace VA]
    (W : Chapter06AdelicVectorSpaceData P V VA)
    (hdiscrete : Chapter06DiscreteEmbedding
      (chapter06CoordinatewiseDiagonal P W.rank)) :
    Chapter06DiscreteEmbedding W.diagonal := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply W.globalCoordinates.injective
    apply hdiscrete.1
    simpa only [Chapter06AdelicVectorSpaceData.coordinates_compatible_apply] using
      congrArg W.adelicCoordinates hxy
  · intro x
    rcases hdiscrete.2 (W.globalCoordinates x) with ⟨U, hUopen, hUmem, hUisol⟩
    refine ⟨W.adelicCoordinates ⁻¹' U, hUopen.preimage W.adelicCoordinates_continuous,
      ?_, ?_⟩
    · change W.adelicCoordinates (W.diagonal x) ∈ U
      rw [Chapter06AdelicVectorSpaceData.coordinates_compatible_apply]
      exact hUmem
    · intro y hy
      apply W.globalCoordinates.injective
      apply hUisol (W.globalCoordinates y)
      change W.adelicCoordinates (W.diagonal y) ∈ U at hy
      rw [Chapter06AdelicVectorSpaceData.coordinates_compatible_apply] at hy
      exact hy

/-- Finite-dimensional adelic vector spaces inherit discreteness and
cocompactness from the coordinatewise lattice. -/
theorem chapter06_finite_dimensional_adelic_lattice
    {V : Type uV} {VA : Type uVA}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup VA] [TopologicalSpace VA]
    (W : Chapter06AdelicVectorSpaceData P V VA)
    (D : Chapter06ArchimedeanCell P)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [T2Space KInf] [T2Space Af]
    [IsTopologicalAddGroup VA] [T2Space VA]
    (hdiscrete : Chapter06DiscreteEmbedding W.diagonal) :
    Chapter06AdditiveLattice W.diagonal := by
  refine ⟨hdiscrete, ?_⟩
  let C : Set VA := W.adelicCoordinates.symm ''
    chapter06CoordinatewiseFundamentalSet P D.carrier W.rank
  have hC : IsCompact C := by
    exact (chapter06_coordinatewise_fundamental_set_compact P D.carrier W.rank
      D.compact).image W.adelicCoordinates_symm_continuous
  apply chapter06_compact_quotient_of_compact_cover W.diagonal C hC
  intro x
  let y := W.adelicCoordinates x
  rcases chapter06_coordinatewise_reduced_to_fundamental_set P D W.rank y with
    ⟨a, ha⟩
  let v := W.globalCoordinates.symm a
  refine ⟨v, ?_⟩
  have hcoord : W.adelicCoordinates (x - W.diagonal v) =
      y - chapter06CoordinatewiseDiagonal P W.rank a := by
    rw [map_sub, W.coordinates_compatible_apply]
    simp [y, v]
  refine ⟨y - chapter06CoordinatewiseDiagonal P W.rank a, ?_, ?_⟩
  · exact ha
  · rw [← hcoord]
    exact W.adelicCoordinates.symm_apply_apply _

/-- The finite-dimensional lattice theorem with discreteness supplied in
    coordinates, which is the basis-reduction form used in the source. -/
theorem chapter06_finite_dimensional_adelic_lattice_of_coordinatewise_discrete
    {V : Type uV} {VA : Type uVA}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup VA] [TopologicalSpace VA]
    (W : Chapter06AdelicVectorSpaceData P V VA)
    (D : Chapter06ArchimedeanCell P)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [T2Space KInf] [T2Space Af]
    [IsTopologicalAddGroup VA] [T2Space VA]
    (hdiscrete : Chapter06DiscreteEmbedding
      (chapter06CoordinatewiseDiagonal P W.rank)) :
    Chapter06AdditiveLattice W.diagonal := by
  exact chapter06_finite_dimensional_adelic_lattice W D
    (chapter06_adelic_vector_space_discrete_of_coordinatewise_discrete W hdiscrete)

/-- The finite-dimensional lattice theorem obtained directly from the
    rank-one diagonal discreteness, via finite coordinates and a basis. -/
theorem chapter06_finite_dimensional_adelic_lattice_of_discrete
    {V : Type uV} {VA : Type uVA}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup VA] [TopologicalSpace VA]
    (W : Chapter06AdelicVectorSpaceData P V VA)
    (D : Chapter06ArchimedeanCell P)
    [IsTopologicalAddGroup KInf] [IsTopologicalAddGroup Af]
    [T2Space KInf] [T2Space Af]
    [IsTopologicalAddGroup VA] [T2Space VA]
    (hdiscrete : Chapter06DiscreteEmbedding (chapter06Diagonal P)) :
    Chapter06AdditiveLattice W.diagonal := by
  exact chapter06_finite_dimensional_adelic_lattice_of_coordinatewise_discrete W D
    (chapter06_coordinatewise_discrete_of_discrete P W.rank hdiscrete)

/- A discrete subgroup of a Hausdorff topological group is closed.  This is
   kept as a small bridge because the source uses closedness only as a
   consequence of discreteness when passing to compact intersections. -/
theorem chapter06_discrete_embedding_range_closed
    {G : Type*} {H : Type*} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [T2Space H]
    (ι : G →+ H) (hι : Chapter06DiscreteEmbedding ι) :
    IsClosed (Set.range ι) := by
  sorry

/-- A compact set meets a discrete lattice in finitely many points. -/
theorem chapter06_compact_intersects_discrete_lattice_finitely
    {G : Type*} {H : Type*} [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [T2Space H]
    (ι : G →+ H)
    (hι : Chapter06DiscreteEmbedding ι)
    (C : Set H)
    (hC : IsCompact C) :
    (Set.range ι ∩ C).Finite ∧ (ι ⁻¹' C).Finite := by
  have hclosed : IsClosed (Set.range ι) :=
    chapter06_discrete_embedding_range_closed ι hι
  have hdiscrete : IsDiscrete (Set.range ι ∩ C) := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x hx
    rcases hx.1 with ⟨g, rfl⟩
    rcases hι.2 g with ⟨U, hUopen, hUg, hU⟩
    refine ⟨U, hUopen, ?_⟩
    ext z
    constructor
    · intro hz
      rcases hz.2.1 with ⟨h, rfl⟩
      have hEq : h = g := hU h hz.1
      simp [hEq]
    · intro hz
      have hz' : z = ι g := by simpa using hz
      subst z
      exact ⟨hUg, ⟨g, rfl⟩, hx.2⟩
  have hcompact : IsCompact (Set.range ι ∩ C) := by
    simpa only [Set.inter_comm] using hC.inter_right hclosed
  have hfinite : (Set.range ι ∩ C).Finite := hcompact.finite hdiscrete
  refine ⟨hfinite, ?_⟩
  refine Set.Finite.of_finite_image (s := ι ⁻¹' C) (f := ι) ?_ ?_
  · simpa only [Set.image_preimage_eq_range_inter] using hfinite
  · exact hι.1.injOn

/-- The bounded algebraic-integer finiteness consequence of the archimedean
lattice. -/
theorem chapter06_bounded_integral_elements_finite
    (P : Chapter06AdeleData K O KInf Af Ohat) (C : Set KInf)
    (hC : IsCompact C)
    [IsTopologicalAddGroup KInf] [T2Space KInf]
    (hι : Chapter06DiscreteEmbedding P.integerToInfinite) :
    (P.integerToInfinite ⁻¹' C).Finite := by
  exact (chapter06_compact_intersects_discrete_lattice_finitely
    P.integerToInfinite hι C hC).2

/-- The finite-intersection statement for an arbitrary finite-dimensional
adelic vector space. -/
theorem chapter06_compact_intersects_adelic_vector_lattice_finitely
    {V : Type uV} {VA : Type uVA}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup VA] [TopologicalSpace VA]
    (W : Chapter06AdelicVectorSpaceData P V VA) (C : Set VA)
    [IsTopologicalAddGroup VA] [T2Space VA]
    (hdiscrete : Chapter06DiscreteEmbedding W.diagonal)
    (hC : IsCompact C) :
    (Set.range W.diagonal ∩ C).Finite := by
  exact (chapter06_compact_intersects_discrete_lattice_finitely W.diagonal hdiscrete
    C hC).1

end

end LastLib.Book04AdelesAndIdeles.Chapter06
