module
public import SerrePositivity.DifferentialGraded.Quotient.ScalarExtensionComposition
public import SerrePositivity.DifferentialGraded.Quotient.ScalarExtensionEpsilon
public import SerrePositivity.DifferentialGraded.Quotient.ErasureHead
public import SerrePositivity.DifferentialGraded.Quotient.ErasureOperator

/-! # 固定 path 上の ε 消去と係数変更 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded.ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma eraseHead_baseChange {P : Complex A} {P' : Complex A'} (a : (extension φ).obj P ⟶ P') :
    CochainSquare φ (compareTensor φ (sphereIso φ (-1)).hom a) a
      (eraseHead A P) (eraseHead A' P') := by
  have hε := cochainSquare_tensorRight φ a (eraseEpsilon_baseChange φ)
  have hunitor := cochainSquare_ofHom φ (compareTensor φ (unitIso φ).hom a) a
    (λ_ P).hom (λ_ P').hom (compareTensor_leftUnitor φ a)
  exact cochainSquare_comp φ hε hunitor (add_zero 1)

lemma eraseMiddle_baseChange {P Q : Complex A} {P' Q' : Complex A'}
    (a : (extension φ).obj P ⟶ P') (b : (extension φ).obj Q ⟶ Q') :
    CochainSquare φ (compareTensor φ a (compareTensor φ (sphereIso φ (-1)).hom b))
      (compareTensor φ a b) (eraseMiddle A P Q) (eraseMiddle A' P' Q') := by
  rw [eraseMiddle_eq_tensorLeft, eraseMiddle_eq_tensorLeft]
  exact cochainSquare_tensorLeft φ a (eraseHead_baseChange φ b)

variable (D : Type v) [DGCategory A D]

lemma eraseFirst_baseChange {S : Set D} (b : S) (w : Word S) (x y : D) :
    CochainSquare φ (termBaseChangeIso φ D (b :: w) x y).hom
      (termBaseChangeIso φ D w x y).hom (eraseFirst A D b w x y)
        (eraseFirst A' (DGBaseChange φ D) b w x y) := by
  rw [termBaseChangeIso_cons_compare]
  have hm := eraseMiddle_baseChange φ
    (𝟙 ((extension φ).obj (homObject A D x b.val)))
    (termBaseChangeIso φ D w b.val y).hom
  have hp := cochainSquare_ofHom φ
    (compareTensor φ (𝟙 ((extension φ).obj (homObject A D x b.val)))
      (termBaseChangeIso φ D w b.val y).hom)
    (termBaseChangeIso φ D w x y).hom
    (prependMap A D w x b.val y) (prependMap A' (DGBaseChange φ D) w x b.val y)
    (prependMap_baseChange φ D w x b.val y)
  exact cochainSquare_comp φ hm hp (add_zero 1)

lemma eraseFace_baseChange {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    CochainSquare φ (termBaseChangeIso φ D w x y).hom
      (termBaseChangeIso φ D (w.eraseIdx i) x y).hom (eraseFace A D w i x y)
        (eraseFace A' (DGBaseChange φ D) w i x y) := by
  induction w generalizing i x y with
  | nil => exact cochainSquare_zero φ _ _
  | cons b w ih =>
    cases i with
    | zero => exact eraseFirst_baseChange φ D b w x y
    | succ i =>
      have hε := cochainSquare_tensorLeft φ (sphereIso φ (-1)).hom (ih i b.val y)
      have hH := cochainSquare_tensorLeft φ
        (𝟙 ((extension φ).obj (homObject A D x b.val))) hε
      simp only [List.eraseIdx_cons_succ, termBaseChangeIso_cons_compare]
      convert hH using 1 <;> rfl

variable [Small.{u} D]

lemma eraseSummand_baseChange {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    CochainSquare φ (termBaseChangeIso φ D w x y).hom
      (internalHomBaseChangeIso φ D S x y).hom (eraseSummand A D w i x y)
        (eraseSummand A' (DGBaseChange φ D) w i x y) :=
  cochainSquare_comp φ (eraseFace_baseChange φ D w i x y)
    (cochainSquare_ofHom φ _ _ (ι A D S x y (w.eraseIdx i))
      (ι A' (DGBaseChange φ D) S x y (w.eraseIdx i))
        (map_ι_internalHomBaseChangeIso φ D S x y (w.eraseIdx i))) (add_zero 1)

lemma eraseRow_baseChange {S : Set D} (w : Word S) (x y : D) :
    CochainSquare φ (termBaseChangeIso φ D w x y).hom
      (internalHomBaseChangeIso φ D S x y).hom (eraseRow A D w x y)
        (eraseRow A' (DGBaseChange φ D) w x y) := by
  have hs (s : Finset ℕ) : CochainSquare φ (termBaseChangeIso φ D w x y).hom
      (internalHomBaseChangeIso φ D S x y).hom
      (∑ i ∈ s, eraseSummand A D w i x y)
      (∑ i ∈ s, eraseSummand A' (DGBaseChange φ D) w i x y) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using (cochainSquare_zero φ
        (termBaseChangeIso φ D w x y).hom (internalHomBaseChangeIso φ D S x y).hom)
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact cochainSquare_add φ (eraseSummand_baseChange φ D w i x y) ih
  exact hs (Finset.range w.length)

lemma erasure_baseChange (S : Set D) (x y : D) :
    CochainSquare φ (internalHomBaseChangeIso φ D S x y).hom
      (internalHomBaseChangeIso φ D S x y).hom (erasure A D S x y)
        (erasure A' (DGBaseChange φ D) S x y) := by
  intro i j hij
  let E := HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i
  let hc := isColimitOfHasCoproductOfPreservesColimit E (fun w : Word S => term A D w x y)
  apply (isColimitOfPreserves (ModuleCat.extendScalars φ) hc).hom_ext
  rintro ⟨w⟩
  change (ModuleCat.extendScalars φ).map ((ι A D S x y w).f i) ≫
      (ModuleCat.extendScalars φ).map ((erasure A D S x y).v i j hij) ≫
        (internalHomBaseChangeIso φ D S x y).hom.f j =
    (ModuleCat.extendScalars φ).map ((ι A D S x y w).f i) ≫
      (internalHomBaseChangeIso φ D S x y).hom.f i ≫
        (erasure A' (DGBaseChange φ D) S x y).v i j hij
  have hι := congrArg (fun f => f.f i) (map_ι_internalHomBaseChangeIso φ D S x y w)
  have hrow := eraseRow_baseChange φ D w x y i j hij
  have hsrc := congrArg (fun f => f.v i j hij) (erasure_precomp A D S x y w)
  have htgt := congrArg (fun f => f.v i j hij)
    (erasure_precomp A' (DGBaseChange φ D) S x y w)
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at hsrc htgt
  simp only [HomologicalComplex.comp_f] at hι
  change (ModuleCat.extendScalars φ).map ((ι A D S x y w).f i) ≫
      (internalHomBaseChangeIso φ D S x y).hom.f i =
    (termBaseChangeIso φ D w x y).hom.f i ≫ (ι A' (DGBaseChange φ D) S x y w).f i at hι
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hsrc, hrow,
    ← Category.assoc, hι, Category.assoc, htgt]

end SerrePositivity.DifferentialGraded.DGQuotient
