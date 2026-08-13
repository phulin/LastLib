import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Section02RelativeEffectiveCartierDivisors

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/-! ## 10.4. Norms and addition -/

def chapter10EffectiveCartierDivisorAdd {X : Scheme}
    (D E : Chapter10EffectiveCartierDivisor X) :
    Chapter10EffectiveCartierDivisor X :=
  { ideal := D.ideal * E.ideal
    locallyRegularPrincipal := by sorry
    closed := by infer_instance }

instance {X : Scheme} : Add (Chapter10EffectiveCartierDivisor X) where
  add := chapter10EffectiveCartierDivisorAdd

theorem chapter10_add_ideal {X : Scheme} (D E : Chapter10EffectiveCartierDivisor X) :
    (D + E).ideal = D.ideal * E.ideal :=
  rfl

theorem chapter10_add_locally_is_cut_out_by_product {X : Scheme}
    (D E : Chapter10EffectiveCartierDivisor X) :
    Chapter10LocallyRegularPrincipal (D + E).ideal :=
  (D + E).locallyRegularPrincipal

theorem chapter10_add_local_generator_product {X : Scheme}
    (D E : Chapter10EffectiveCartierDivisor X) :
    ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ a b : Γ(X, U),
      D.ideal.ideal U = Ideal.span {a} ∧ E.ideal.ideal U = Ideal.span {b} ∧
        (D + E).ideal.ideal U = Ideal.span {a * b} ∧ IsRegular (a * b) := by
  sorry

def chapter10RelativeEffectiveCartierDivisorAdd {C T : Scheme} {c : C ⟶ T}
    {d e : ℕ} (D : Chapter10RelativeEffectiveCartierDivisor c d)
    (E : Chapter10RelativeEffectiveCartierDivisor c e) :
    Chapter10RelativeEffectiveCartierDivisor c (d + e) :=
  { divisor := D.divisor + E.divisor
    finiteLocallyFree := by sorry }

theorem chapter10_add_degree {C T : Scheme} {c : C ⟶ T} {d e : ℕ}
    (D : Chapter10RelativeEffectiveCartierDivisor c d)
    (E : Chapter10RelativeEffectiveCartierDivisor c e) :
    ∀ t : T,
      Chapter10FiberLength
          ((D.divisor + E.divisor).ideal.subschemeι ≫ c) t = d + e := by
  intro t
  sorry

def chapter10_O_add_is_tensor {X : Scheme}
    (D E : Chapter10EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X]
    [Chapter10PicardOperations X] :
    Chapter10LineBundleIso (chapter10OofD (D + E))
      (chapter10PicardTensor (chapter10OofD D) (chapter10OofD E)) := by
  sorry

/-!
For a finite locally free morphism `q`, the pushforward module is canonical in
the scheme-module category.  The determinant-line constructor is separated
out because that is precisely the piece not supplied by the pinned snapshot.
-/

noncomputable def chapter10PushforwardModule {Z T : Scheme} (q : Z ⟶ T)
    (M : Z.Modules) : T.Modules :=
  (Scheme.Modules.pushforward q).obj M

noncomputable def chapter10DeterminantLine {Z T : Scheme} (q : Z ⟶ T)
    [Chapter10DeterminantLineAPI q] (M : Chapter10LineBundle Z) : Chapter10LineBundle T :=
  Chapter10DeterminantLineAPI.determinant (q := q) M

noncomputable def chapter10Norm {Z T : Scheme} (q : Z ⟶ T)
    [Chapter10PicardOperations T] [Chapter10DeterminantLineAPI q]
    (M : Chapter10LineBundle Z) : Chapter10LineBundle T :=
  chapter10PicardTensor
    (chapter10DeterminantLine q M)
    (Chapter10PicardOperations.dual
      (chapter10DeterminantLine q (chapter10StructureSheafLineBundle Z)))

theorem chapter10_norm_determinant_formula {Z T : Scheme} (q : Z ⟶ T)
    [Chapter10PicardOperations T] [Chapter10DeterminantLineAPI q]
    (M : Chapter10LineBundle Z) :
    chapter10Norm q M =
        chapter10PicardTensor
        (chapter10DeterminantLine q M)
        (Chapter10PicardOperations.dual
          (chapter10DeterminantLine q (chapter10StructureSheafLineBundle Z))) :=
  rfl

noncomputable def chapter10PullbackLineBundle {X Y : Scheme} (f : X ⟶ Y)
    (L : Chapter10LineBundle Y) :
    Chapter10LineBundle X :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09PullbackLineBundle f L

def chapter10_norm_commutes_baseChange {Z T T' : Scheme} (q : Z ⟶ T) (g : T' ⟶ T)
    [Chapter10PicardOperations T] [Chapter10PicardOperations T']
    [Chapter10DeterminantLineAPI q]
    [Chapter10DeterminantLineAPI (pullback.snd q g)]
    (M : Chapter10LineBundle Z) :
    Chapter10LineBundleIso
      (chapter10PullbackLineBundle g (chapter10Norm q M))
      (chapter10Norm (pullback.snd q g)
        (chapter10PullbackLineBundle (pullback.fst q g) M)) := by
  sorry

def chapter10_norm_commutes_tensor_product {Z T : Scheme} (q : Z ⟶ T)
    [Chapter10PicardOperations Z] [Chapter10PicardOperations T]
    [Chapter10DeterminantLineAPI q]
    (M N : Chapter10LineBundle Z) :
    Chapter10LineBundleIso (chapter10Norm q
      (chapter10PicardTensor M N))
      (chapter10PicardTensor (chapter10Norm q M) (chapter10Norm q N)) := by
  sorry

structure Chapter10UniversalDivisor {C P : Scheme} (p : C ⟶ P) (d : ℕ) where
  divisor : Chapter10EffectiveCartierDivisor C
  finiteLocallyFree :
    Chapter10FiniteLocallyFreeProfile (divisor.ideal.subschemeι ≫ p) d

noncomputable def chapter10NormAlongUniversalDivisor {C P : Scheme} (p : C ⟶ P) (d : ℕ)
    [Chapter10IdealDualAPI C]
    [Chapter10PicardOperations P]
    (U : Chapter10UniversalDivisor p d)
    [Chapter10DeterminantLineAPI (U.divisor.ideal.subschemeι ≫ p)] :
    Chapter10LineBundle P :=
  chapter10Norm (U.divisor.ideal.subschemeι ≫ p)
    (chapter10PullbackLineBundle U.divisor.ideal.subschemeι (chapter10OofD U.divisor))

/- LOCAL_DEPENDENCY_GUESS (10.4): the preceding definition is intentionally
  parameterized by the universal-divisor projection and the determinant API;
  the chapter invokes this construction, while the actual universal divisor
  is introduced by the surrounding book chapters. -/

theorem chapter10_norm_along_universal_divisor_is_norm {C P : Scheme} (p : C ⟶ P)
    (d : ℕ) [Chapter10IdealDualAPI C]
    [Chapter10PicardOperations P]
    (U : Chapter10UniversalDivisor p d)
    [Chapter10DeterminantLineAPI (U.divisor.ideal.subschemeι ≫ p)] :
    chapter10NormAlongUniversalDivisor p d U =
      chapter10Norm (U.divisor.ideal.subschemeι ≫ p)
        (chapter10PullbackLineBundle U.divisor.ideal.subschemeι (chapter10OofD U.divisor)) :=
  rfl

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
