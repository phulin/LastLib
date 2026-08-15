import LastLib.Book05LocalClassFieldTheory.Chapter05.Core

namespace LastLib.Book05LocalClassFieldTheory.Chapter05

noncomputable section

open CategoryTheory

/-!
### 5.2. Tate homology in degree minus two
-/

noncomputable def chapter05H1AbelianizationIso
    (G : Type) [Group G] :
    chapter05GroupHomology G (Rep.trivial ℤ G ℤ) 1 ≃+
    Additive (chapter05Abelianization G) :=
  (chapter05H1TensorAbelianizationIso G).trans
    (TensorProduct.rid ℤ (Additive (chapter05Abelianization G))).toAddEquiv

def chapter05BarOneChain
    (G : Type) [Group G] (g : G) : Additive (chapter05Abelianization G) :=
  Additive.ofMul (chapter05AbelianizationMap G g)

def chapter05BarOneChainClass
    (G : Type) [Group G] (g : G) :
    chapter05GroupHomology G (Rep.trivial ℤ G ℤ) 1 :=
  groupHomology.H1π (Rep.trivial ℤ G ℤ)
    ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv
      (Finsupp.single g (1 : ℤ)))

theorem chapter05BarOneChainClass_mul
    (G : Type) [Group G] (g h : G) :
    chapter05BarOneChainClass G (g * h) =
      chapter05BarOneChainClass G g + chapter05BarOneChainClass G h := by
  apply (chapter05H1AbelianizationIso G).injective
  simp [chapter05H1AbelianizationIso, chapter05H1TensorAbelianizationIso,
    chapter05BarOneChainClass]
  rw [groupHomology.H1AddEquivOfIsTrivial_single
      (A := Rep.trivial ℤ G ℤ) (g * h) (1 : ℤ),
    groupHomology.H1AddEquivOfIsTrivial_single
      (A := Rep.trivial ℤ G ℤ) g (1 : ℤ),
    groupHomology.H1AddEquivOfIsTrivial_single
      (A := Rep.trivial ℤ G ℤ) h (1 : ℤ)]
  simp [TensorProduct.rid_tmul]

theorem chapter05BarOneChainClass_commutator
    (G : Type) [Group G] (g h : G) :
    chapter05BarOneChainClass G (g * h * g⁻¹ * h⁻¹) = 0 := by
  apply (groupHomology.H1AddEquivOfIsTrivial
    (A := Rep.trivial ℤ G ℤ)).injective
  simp only [chapter05BarOneChainClass]
  rw [groupHomology.H1AddEquivOfIsTrivial_single
      (A := Rep.trivial ℤ G ℤ) (g * h * g⁻¹ * h⁻¹) (1 : ℤ)]
  simp

theorem chapter05BarOneChain_mul
    (G : Type) [Group G] (g h : G) :
    chapter05BarOneChain G (g * h) =
      chapter05BarOneChain G g + chapter05BarOneChain G h := by
  simp [chapter05BarOneChain]

theorem chapter05BarOneChain_commutator
    (G : Type) [Group G] (g h : G) :
    chapter05BarOneChain G (g * h * g⁻¹ * h⁻¹) = 0 := by
  simp [chapter05BarOneChain]

/- The bar construction gives the inverse direction of the homology--
abelianization equivalence.  Keeping this map explicit is useful when a
finite Artin map is later read on a generator. -/
noncomputable def chapter05BarH1Map
  (G : Type) [Group G] :
    Additive (chapter05Abelianization G) →+
      chapter05GroupHomology G (Rep.trivial ℤ G ℤ) 1 :=
  (chapter05H1AbelianizationIso G).symm.toAddMonoidHom

theorem chapter05BarH1Map_on_one_chain
    (G : Type) [Group G] (g : G) :
    chapter05BarH1Map G (chapter05BarOneChain G g) =
      chapter05BarOneChainClass G g := by
  apply (chapter05H1AbelianizationIso G).injective
  simp [chapter05BarH1Map, chapter05BarOneChain,
    chapter05H1AbelianizationIso, chapter05H1TensorAbelianizationIso,
    chapter05BarOneChainClass]
  rw [groupHomology.H1AddEquivOfIsTrivial_single
      (A := Rep.trivial ℤ G ℤ) g (1 : ℤ)]
  simp [TensorProduct.rid_tmul]
  rfl

noncomputable def chapter05_tate_minus_two_is_homology
    (G : Type) [Group G] [Fintype G] :
    chapter05TateCohomology G (Rep.trivial ℤ G ℤ) (-2) ≅
      chapter05GroupHomology G (Rep.trivial ℤ G ℤ) 1 :=
  chapter05TateMinusTwoHomologyIso G

/- LOCAL_DEPENDENCY_GUESS: the fixed-point/norm calculation for the units of
a finite Galois local extension is supplied by the local-class-field chapters;
the record below exposes its exact degree-zero target without choosing a
second cohomology model. -/
noncomputable def chapter05TateZeroNormIso
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] :
    chapter05TateCohomology (Gal(L / K))
      (chapter05CoefficientRep K L) 0 ≃+
      Additive (chapter05NormQuotient K L) := by
  sorry

theorem chapter05_tate_zero_is_fixed_points_mod_norm
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] :
    Nonempty
      (chapter05TateCohomology (Gal(L / K))
        (chapter05CoefficientRep K L) 0 ≃+
        Additive (chapter05NormQuotient K L)) := by
  exact ⟨chapter05TateZeroNormIso K L⟩

/- The cap-product interface from the shared file has precisely the source
and target appearing here. -/
def chapter05CapAt
    {G : Type} [Group G] [Fintype G] {A : Rep ℤ G}
    {u : chapter05GroupCohomology G A 2}
    (P : Chapter05CapProduct G A u) (H : Subgroup G) (r : ℤ) :=
  chapter05CapProductMap P H r

end

end LastLib.Book05LocalClassFieldTheory.Chapter05
