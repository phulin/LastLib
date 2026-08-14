import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03.Dependencies

/-!
## 3.3 Separatedness, finite type, and properness

The predicates below keep the distinctions between quasi-compactness, locally finite type, and
locally finite presentation explicit.  This matters for quasi-projective morphisms, since an open
immersion need not be quasi-compact.
-/

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

variable {X Y S : Scheme.{u}}

/-- The finite-type package for a morphism. -/
def chapter03FiniteType (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ LocallyOfFiniteType f

/-- The finite-presentation package for a morphism. -/
def chapter03FinitelyPresented (f : X ⟶ S) : Prop :=
  QuasiCompact f ∧ LocallyOfFinitePresentation f

/-- Finite type is the conjunction of quasi-compactness and locally finite type. -/
theorem chapter03_finiteType_iff (f : X ⟶ S) :
    chapter03FiniteType f ↔ QuasiCompact f ∧ LocallyOfFiniteType f :=
  Iff.rfl

/-- Finite presentation is the conjunction of quasi-compactness and locally finite presentation. -/
theorem chapter03_finitelyPresented_iff (f : X ⟶ S) :
    chapter03FinitelyPresented f ↔ QuasiCompact f ∧ LocallyOfFinitePresentation f :=
  Iff.rfl

/-- Relative projective bundles are separated. -/
theorem chapter03_relativeProjectiveBundle_isSeparated
    (S : Scheme.{u}) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    IsSeparated P.projection := by
  let : IsProper P.projection := P.proper
  infer_instance

/-- Relative projective bundles are quasi-compact. -/
theorem chapter03_relativeProjectiveBundle_quasiCompact
    (S : Scheme.{u}) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    QuasiCompact P.projection := by
  let : IsProper P.projection := P.proper
  infer_instance

/-- Relative projective bundles are locally of finite type. -/
theorem chapter03_relativeProjectiveBundle_locallyOfFiniteType
    (S : Scheme.{u}) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    LocallyOfFiniteType P.projection := by
  let : LocallyOfFinitePresentation P.projection := P.finite_presentation
  infer_instance

/-- Relative projective bundles are proper. -/
theorem chapter03_relativeProjectiveBundle_isProper
    (S : Scheme.{u}) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    IsProper P.projection := by
  exact P.proper

/-- Over a locally noetherian base, relative projective bundles are locally of finite
presentation. -/
theorem chapter03_relativeProjectiveBundle_locallyOfFinitePresentation
    (S : Scheme.{u}) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation P.projection := by
  exact P.finite_presentation

/-- A finite-rank relative projective bundle is finitely presented over its base. -/
theorem chapter03_relativeProjectiveBundle_finitelyPresented
    (S : Scheme.{u}) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    chapter03FinitelyPresented P.projection := by
  let : IsProper P.projection := P.proper
  exact ⟨inferInstance, P.finite_presentation⟩

/-- Every projective morphism is separated. -/
theorem chapter03_projective_isSeparated (f : X ⟶ S)
    (hf : chapter03Projective f) : IsSeparated f := by
  apply Nonempty.elim hf
  intro P
  let : IsClosedImmersion P.embedding := P.isClosedImmersion
  let : IsProper P.ambient.projection := P.ambient.proper
  rw [← P.overBase]
  infer_instance

/-- Every projective morphism is quasi-compact. -/
theorem chapter03_projective_quasiCompact (f : X ⟶ S)
    (hf : chapter03Projective f) : QuasiCompact f := by
  apply Nonempty.elim hf
  intro P
  let : IsClosedImmersion P.embedding := P.isClosedImmersion
  let : IsProper P.ambient.projection := P.ambient.proper
  rw [← P.overBase]
  infer_instance

/-- Every projective morphism is locally of finite type. -/
theorem chapter03_projective_locallyOfFiniteType (f : X ⟶ S)
    (hf : chapter03Projective f) : LocallyOfFiniteType f := by
  apply Nonempty.elim hf
  intro P
  let : IsClosedImmersion P.embedding := P.isClosedImmersion
  let : LocallyOfFinitePresentation P.ambient.projection :=
    P.ambient.finite_presentation
  rw [← P.overBase]
  infer_instance

/-- Every projective morphism is proper. -/
theorem chapter03_projective_isProper (f : X ⟶ S)
    (hf : chapter03Projective f) : IsProper f := by
  apply Nonempty.elim hf
  intro P
  let : IsClosedImmersion P.embedding := P.isClosedImmersion
  let : IsProper P.ambient.projection := P.ambient.proper
  rw [← P.overBase]
  infer_instance

/-- Projective morphisms have finite type. -/
theorem chapter03_projective_finiteType (f : X ⟶ S)
    (hf : chapter03Projective f) : chapter03FiniteType f := by
  exact ⟨chapter03_projective_quasiCompact f hf,
    chapter03_projective_locallyOfFiniteType f hf⟩

/-- A quasi-projective morphism is separated. -/
theorem chapter03_quasiProjective_isSeparated (f : X ⟶ S)
    (hf : chapter03QuasiProjective f) : IsSeparated f := by
  apply Nonempty.elim hf
  intro P
  let : IsImmersion P.embedding := P.isImmersion
  let : IsProper P.ambient.projection := P.ambient.proper
  rw [← P.overBase]
  infer_instance

/-- A quasi-projective morphism is locally of finite type. -/
theorem chapter03_quasiProjective_locallyOfFiniteType (f : X ⟶ S)
    (hf : chapter03QuasiProjective f) : LocallyOfFiniteType f := by
  apply Nonempty.elim hf
  intro P
  let : IsImmersion P.embedding := P.isImmersion
  let : LocallyOfFinitePresentation P.ambient.projection :=
    P.ambient.finite_presentation
  rw [← P.overBase]
  infer_instance

/-- A quasi-compact quasi-projective morphism has finite type. -/
theorem chapter03_quasiProjective_finiteType (f : X ⟶ S)
    (hf : chapter03QuasiProjective f) (hq : QuasiCompact f) :
    chapter03FiniteType f := by
  exact ⟨hq, chapter03_quasiProjective_locallyOfFiniteType f hf⟩

/-- A projective presentation with a finitely presented closed immersion is finitely presented. -/
theorem chapter03_finitelyPresented_of_projectivePresentation
    (f : X ⟶ S) (P : Chapter03ProjectivePresentation f)
    [LocallyOfFinitePresentation P.embedding]
    [LocallyOfFinitePresentation P.ambient.projection] :
    chapter03FinitelyPresented f := by
  let : IsClosedImmersion P.embedding := P.isClosedImmersion
  let : IsProper P.ambient.projection := P.ambient.proper
  refine ⟨?_, ?_⟩
  · rw [← P.overBase]
    infer_instance
  · rw [← P.overBase]
    infer_instance

/-- A quasi-projective presentation with a finitely presented immersion is finitely presented. -/
theorem chapter03_finitelyPresented_of_quasiProjectivePresentation
    (f : X ⟶ S) (P : Chapter03QuasiProjectivePresentation f)
    [LocallyOfFinitePresentation P.embedding]
    [LocallyOfFinitePresentation P.ambient.projection] (hq : QuasiCompact f) :
    chapter03FinitelyPresented f := by
  exact ⟨hq, by
    rw [← P.overBase]
    infer_instance⟩

/-- Projective morphisms are finitely presented over a locally noetherian base. -/
theorem chapter03_projective_finitelyPresented_of_locallyNoetherian
    (f : X ⟶ S) (hf : chapter03Projective f) [IsLocallyNoetherian S] :
    chapter03FinitelyPresented f := by
  refine ⟨chapter03_projective_quasiCompact f hf, ?_⟩
  let : LocallyOfFiniteType f := chapter03_projective_locallyOfFiniteType f hf
  infer_instance

/-- Quasi-projective morphisms are finitely presented when the morphism is quasi-compact and the
base is locally noetherian. -/
theorem chapter03_quasiProjective_finitelyPresented_of_locallyNoetherian
    (f : X ⟶ S) (hf : chapter03QuasiProjective f) (hq : QuasiCompact f)
    [IsLocallyNoetherian S] :
    chapter03FinitelyPresented f := by
  refine ⟨hq, ?_⟩
  let : LocallyOfFiniteType f := chapter03_quasiProjective_locallyOfFiniteType f hf
  infer_instance

/-- A closed immersion into a proper scheme is proper. -/
theorem chapter03_closedImmersion_comp_proper_isProper
    (i : X ⟶ Y) (g : Y ⟶ S) [IsClosedImmersion i] [IsProper g] :
    IsProper (i ≫ g) := by
  infer_instance

/-- The existence part of the valuative criterion for a relative projective bundle. -/
theorem chapter03_relativeProjectiveBundle_valuativeCriterion_existence
    (S : Scheme.{u}) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    ValuativeCriterion.Existence P.projection := by
  have h : IsProper P.projection := P.proper
  rw [IsProper.eq_valuativeCriterion] at h
  exact ValuativeCriterion.existence h.1.1.1

/-- The uniqueness part of the valuative criterion for a relative projective bundle. -/
theorem chapter03_relativeProjectiveBundle_valuativeCriterion_uniqueness
    (S : Scheme.{u}) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    ValuativeCriterion.Uniqueness P.projection := by
  have h : IsProper P.projection := P.proper
  rw [IsProper.eq_valuativeCriterion] at h
  exact ValuativeCriterion.uniqueness h.1.1.1

/-- The relative projective bundle satisfies the full valuative criterion. -/
theorem chapter03_relativeProjectiveBundle_valuativeCriterion
    (S : Scheme.{u}) (E : S.Modules) (_hE : chapter03FiniteLocallyFree E)
    (P : Chapter03RelativeProjectiveBundle S E) :
    ValuativeCriterion P.projection := by
  have h : IsProper P.projection := P.proper
  rw [IsProper.eq_valuativeCriterion] at h
  exact h.1.1.1

/-- A projective-bundle point is represented by a tuple with at least one unit coefficient. -/
def chapter03PrimitiveTuple (V : Type u) [CommRing V] (r : ℕ) : Type u :=
  {a : Fin (r + 1) → V // ∃ i, IsUnit (a i)}

/-- Primitive tuples give normalized representatives of one-dimensional quotients over a
valuation ring. -/
def chapter03ScalarMultiple {K : Type u} (r : ℕ) [Field K]
    (x y : Fin (r + 1) → K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ ∀ i, y i = c * x i

/-- Primitive tuples give normalized representatives of one-dimensional quotients over a
valuation ring, up to the scalar used to normalize the original tuple. -/
theorem chapter03_primitiveTuple_normalization
    (V K : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (r : ℕ) :
    ∀ x : Fin (r + 1) → K,
      (∃ i, x i ≠ 0) →
        ∃ a : chapter03PrimitiveTuple V r,
          chapter03ScalarMultiple r x (fun i => algebraMap V K (a.1 i)) := by
  classical
  intro x hx
  have hdom :
      ∀ (s : Finset (Fin (r + 1))),
        (∀ i ∈ s, x i ≠ 0) → s.Nonempty →
          ∃ j ∈ s, ∀ i ∈ s, IsLocalization.IsInteger V (x i / x j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _ hs
        simp at hs
    | @insert a s ha ih =>
        intro hnonzero hs
        by_cases hs' : s.Nonempty
        · obtain ⟨j, hj, hjs⟩ := ih
            (by
              intro i hi
              exact hnonzero i (Finset.mem_insert_of_mem hi)) hs'
          rcases ValuationRing.isInteger_or_isInteger V (x a / x j) with hleft | hright
          · refine ⟨j, Finset.mem_insert_of_mem hj, ?_⟩
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact hleft
            · exact hjs i hi
          · refine ⟨a, by simp, ?_⟩
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · have hi0 := hnonzero i (by simp)
              convert (IsLocalization.isInteger_one (R := V) (S := K)) using 1
              field_simp [hi0]
            · have hprod := IsLocalization.isInteger_mul (hjs i hi) hright
              convert hprod using 1 ;
                field_simp [hnonzero i (Finset.mem_insert_of_mem hi),
                  hnonzero a (by simp),
                  hnonzero j (Finset.mem_insert_of_mem hj)]
        · refine ⟨a, by simp, ?_⟩
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · have ha0 := hnonzero i (Finset.mem_insert_self i s)
            convert (IsLocalization.isInteger_one (R := V) (S := K)) using 1
            field_simp [ha0]
          · exact (hs' ⟨i, hi⟩).elim
  let s := Finset.univ.filter (fun i : Fin (r + 1) => x i ≠ 0)
  have hs : s.Nonempty := by
    rcases hx with ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hs_nonzero : ∀ i ∈ s, x i ≠ 0 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨j, hj, hjs⟩ := hdom s hs_nonzero hs
  have hjx : x j ≠ 0 := hs_nonzero j hj
  have hratio : ∀ i, IsLocalization.IsInteger V (x i / x j) := by
    intro i
    by_cases hi : x i = 0
    · simpa [hi] using (IsLocalization.isInteger_zero (R := V) (S := K))
    · exact hjs i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  choose a ha using hratio
  have haj : a j = 1 := by
    apply (IsFractionRing.injective V K)
    rw [ha j]
    simp [hjx]
  refine ⟨⟨a, ⟨j, haj ▸ isUnit_one⟩⟩, (x j)⁻¹, inv_ne_zero hjx, ?_⟩
  intro i
  change algebraMap V K (a i) = _
  rw [ha i]
  field_simp [hjx]

/-- Two primitive representatives of one projective point differ by a unit of the valuation ring. -/
theorem chapter03_primitiveTuple_unique_up_to_unit
    (V K : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (r : ℕ)
    (a b : chapter03PrimitiveTuple V r)
    (h : chapter03ScalarMultiple r
      (fun i => algebraMap V K (a.1 i))
      (fun i => algebraMap V K (b.1 i))) :
    ∃ u : V, IsUnit u ∧ ∀ i, b.1 i = u * a.1 i := by
  rcases h with ⟨c, hc, hcoord⟩
  have hcoord' : ∀ k, algebraMap V K (b.1 k) = c * algebraMap V K (a.1 k) := by
    intro k
    simpa using hcoord k
  rcases a.2 with ⟨i, hai⟩
  rcases (isUnit_iff_exists.mp hai) with ⟨ai, hai_right, hai_left⟩
  have haiK : algebraMap V K (a.1 i) * algebraMap V K ai = 1 := by
    simpa only [map_mul, map_one] using congrArg (algebraMap V K) hai_right
  let u : V := b.1 i * ai
  have hu_map : algebraMap V K u = c := by
    dsimp [u]
    rw [map_mul, hcoord' i, mul_assoc, haiK, mul_one]
  rcases b.2 with ⟨j, hbj⟩
  rcases (isUnit_iff_exists.mp hbj) with ⟨bj, hbj_right, hbj_left⟩
  have hbjK : algebraMap V K (b.1 j) * algebraMap V K bj = 1 := by
    simpa only [map_mul, map_one] using congrArg (algebraMap V K) hbj_right
  let v : V := a.1 j * bj
  have hv_map : algebraMap V K v * c = 1 := by
    dsimp [v]
    rw [map_mul]
    calc
      algebraMap V K (a.1 j) * algebraMap V K bj * c =
          c * algebraMap V K (a.1 j) * algebraMap V K bj := by ring
      _ = algebraMap V K (b.1 j) * algebraMap V K bj := by rw [hcoord' j]
      _ = 1 := hbjK
  have huv : u * v = 1 := by
    apply (IsFractionRing.injective V K)
    rw [map_mul, hu_map, map_one]
    calc
      c * algebraMap V K v = algebraMap V K v * c := mul_comm _ _
      _ = 1 := hv_map
  have hu : IsUnit u :=
    isUnit_iff_exists.mpr ⟨v, huv, by simpa [mul_comm] using huv⟩
  refine ⟨u, hu, ?_⟩
  intro k
  apply (IsFractionRing.injective V K)
  rw [map_mul, hu_map]
  exact hcoord' k

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter03
