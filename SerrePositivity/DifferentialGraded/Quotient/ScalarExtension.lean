module
public import SerrePositivity.DifferentialGraded.Quotient.ScalarExtensionErasure
public import SerrePositivity.DifferentialGraded.Quotient.Category

/-! # 明示的 dg 商の最終 Hom の係数変更

固定した有限語添字の同型が、内部微分と ε 消去の両方に可換する。
係数環の flatness は要求しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded.ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- ε 消去を加えた最終微分に関する固定 path 係数変更同型。 -/
def quotientHomBaseChangeIso (S : Set D) (x y : D) :
    (extension φ).obj (quotientHom A D S x y) ≅
      quotientHom A' (DGBaseChange φ D) S x y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (HomologicalComplex.eval (ModuleCat.{u} A') (.up ℤ) n).mapIso
      (internalHomBaseChangeIso φ D S x y)) (fun i j hij => by
      change i + 1 = j at hij
      subst j
      change (internalHomBaseChangeIso φ D S x y).hom.f i ≫
          (quotientHom A' (DGBaseChange φ D) S x y).d i (i + 1) =
        (ModuleCat.extendScalars φ).map ((quotientHom A D S x y).d i (i + 1)) ≫
          (internalHomBaseChangeIso φ D S x y).hom.f (i + 1)
      rw [quotientHom_d, quotientHom_d, Preadditive.comp_add,
        CategoryTheory.Functor.map_add, Preadditive.add_comp]
      exact congrArg₂ (· + ·) ((internalHomBaseChangeIso φ D S x y).hom.comm i (i + 1))
        (erasure_baseChange φ D S x y i (i + 1) rfl).symm)

lemma quotientHomBaseChangeIso_hom_f (S : Set D) (x y : D) (n : ℤ) :
    (quotientHomBaseChangeIso φ D S x y).hom.f n =
      (internalHomBaseChangeIso φ D S x y).hom.f n := rfl

@[reassoc]
lemma originalHomInclusion_baseChange (S : Set D) (x y : D) :
    (extension φ).map (originalHomInclusion A D S x y) ≫
        (quotientHomBaseChangeIso φ D S x y).hom =
      originalHomInclusion A' (DGBaseChange φ D) S x y := by
  apply HomologicalComplex.hom_ext
  intro n
  have h := congrArg (fun f => f.f n) (map_originalHom_internalHomBaseChangeIso φ D S x y)
  simp only [HomologicalComplex.comp_f] at h ⊢
  rw [quotientHomBaseChangeIso_hom_f, originalHomInclusion_f]
  convert h using 1 <;> rfl

lemma quotientIdentity_baseChange (S : Set D) (x : D) :
    (unitIso φ).inv ≫ (extension φ).map (quotientIdentity A D S x) ≫
        (quotientHomBaseChangeIso φ D S x x).hom =
      quotientIdentity A' (DGBaseChange φ D) S x := by
  simp only [quotientIdentity, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [originalHomInclusion_baseChange]
  rfl

private lemma matrix_four {C : Type*} [Category* C]
    {V₀ V₁ V₂ V₃ V₄ W₁ W₂ W₃ : C}
    {a : V₀ ⟶ V₁} {b : V₁ ⟶ V₂} {c : V₂ ⟶ V₃} {d : V₃ ⟶ V₄}
    {p : V₀ ⟶ W₁} {q : W₁ ⟶ V₂} {r : W₁ ⟶ W₂}
    {s : W₂ ⟶ V₃} {t : W₂ ⟶ W₃} {u : W₃ ⟶ V₄}
    (h₁ : a ≫ b = p ≫ q) (h₂ : q ≫ c = r ≫ s) (h₃ : s ≫ d = t ≫ u) :
    a ≫ b ≫ c ≫ d = p ≫ r ≫ t ≫ u := by
  rw [← Category.assoc a b (c ≫ d), h₁]
  simp only [Category.assoc]
  rw [← Category.assoc q c d, h₂]
  simp only [Category.assoc]
  rw [h₃]

lemma quotientComposition_baseChange (S : Set D) (x y z : D) :
    (extension φ).map (quotientComposition A D S x y z) ≫
        (quotientHomBaseChangeIso φ D S x z).hom =
      compareTensor φ (quotientHomBaseChangeIso φ D S x y).hom
        (quotientHomBaseChangeIso φ D S y z).hom ≫
          quotientComposition A' (DGBaseChange φ D) S x y z := by
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorBaseChange_hom_ext φ (quotientHom A D S x y) (quotientHom A D S y z)
  intro i j hij
  let uq := (ModuleCat.extendScalars φ).map
    (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) i j n hij)
  let ui := (ModuleCat.extendScalars φ).map
    (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) i j n hij)
  let fq := (ModuleCat.extendScalars φ).map ((quotientComposition A D S x y z).f n)
  let fi := (ModuleCat.extendScalars φ).map ((internalComposition A D S x y z).f n)
  let eq := (quotientHomBaseChangeIso φ D S x z).hom.f n
  let ei := (internalHomBaseChangeIso φ D S x z).hom.f n
  let dq := (cochainTensorBaseChangeXIso φ (quotientHom A D S x y) (quotientHom A D S y z) n).hom
  let di := (cochainTensorBaseChangeXIso φ (internalHom A D S x y) (internalHom A D S y z) n).hom
  let tq := ((quotientHomBaseChangeIso φ D S x y).hom ⊗ₘ
    (quotientHomBaseChangeIso φ D S y z).hom).f n
  let ti := ((internalHomBaseChangeIso φ D S x y).hom ⊗ₘ
    (internalHomBaseChangeIso φ D S y z).hom).f n
  let cq := (quotientComposition A' (DGBaseChange φ D) S x y z).f n
  let ci := (internalComposition A' (DGBaseChange φ D) S x y z).f n
  let gq := ιTensorObj ((extension φ).obj (quotientHom A D S x y))
    ((extension φ).obj (quotientHom A D S y z)) i j n hij
  let gi := ιTensorObj ((extension φ).obj (internalHom A D S x y))
    ((extension φ).obj (internalHom A D S y z)) i j n hij
  let kq := ιTensorObj (quotientHom A' (DGBaseChange φ D) S x y)
    (quotientHom A' (DGBaseChange φ D) S y z) i j n hij
  let ki := ιTensorObj (internalHom A' (DGBaseChange φ D) S x y)
    (internalHom A' (DGBaseChange φ D) S y z) i j n hij
  let ds := CategoryTheory.Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ)
    ((internalHom A D S x y).X i) ((internalHom A D S y z).X j)
  let ts := (internalHomBaseChangeIso φ D S x y).hom.f i ⊗ₘ
    (internalHomBaseChangeIso φ D S y z).hom.f j
  have hs : uq ≫ fq = ui ≫ fi := by
    have h := congrArg (ModuleCat.extendScalars φ).map
      (quotientComposition_ι A D S x y z i j n hij)
    simpa only [CategoryTheory.Functor.map_comp] using h
  have he : eq = ei := quotientHomBaseChangeIso_hom_f φ D S x z n
  have hl : uq ≫ fq ≫ eq = ui ≫ fi ≫ ei := by
    rw [← Category.assoc, hs, Category.assoc, he]
  have hdq : uq ≫ dq = ds ≫ gq :=
    map_ι_cochainTensorBaseChangeXIso φ (quotientHom A D S x y) (quotientHom A D S y z) i j n hij
  have hdi : ui ≫ di = ds ≫ gi :=
    map_ι_cochainTensorBaseChangeXIso φ (internalHom A D S x y) (internalHom A D S y z) i j n hij
  have hmq : gq ≫ tq = ts ≫ kq := by
    have h := ιTensorObj_cochainTensorMap (quotientHomBaseChangeIso φ D S x y).hom
      (quotientHomBaseChangeIso φ D S y z).hom i j n hij
    have hc := congrArg₂ (fun f g => f ⊗ₘ g)
      (quotientHomBaseChangeIso_hom_f φ D S x y i)
      (quotientHomBaseChangeIso_hom_f φ D S y z j)
    exact h.trans (congrArg (fun f => f ≫ kq) hc)
  have hmi : gi ≫ ti = ts ≫ ki :=
    ιTensorObj_cochainTensorMap (internalHomBaseChangeIso φ D S x y).hom
      (internalHomBaseChangeIso φ D S y z).hom i j n hij
  have hq : kq ≫ cq = ki ≫ ci := quotientComposition_ι A' (DGBaseChange φ D) S x y z i j n hij
  have hrq : uq ≫ dq ≫ tq ≫ cq = ds ≫ ts ≫ ki ≫ ci := matrix_four hdq hmq hq
  have hri : ui ≫ di ≫ ti ≫ ci = ds ≫ ts ≫ ki ≫ ci := matrix_four hdi hmi rfl
  have hi : ui ≫ fi ≫ ei = ui ≫ di ≫ ti ≫ ci := by
    have h := congrArg (fun f => ui ≫ f.f n) (internalComposition_baseChange φ D S x y z)
    exact h
  change uq ≫ fq ≫ eq = uq ≫ dq ≫ tq ≫ cq
  exact hl.trans (hi.trans (hri.trans hrq.symm))

/-- 最終 Hom 上の同型を持つ、係数変更と明示的商を交換する実際の dg 関手。 -/
def quotientBaseChangeDGFunctor (S : Set D) :
    DGFunctor A' (DGBaseChange φ (QuotientObject D S))
      (QuotientObject (DGBaseChange φ D) S) where
  obj x := ⟨x.val⟩
  map x y := (quotientHomBaseChangeIso φ D S x.val y.val).hom
  map_id x := quotientIdentity_baseChange φ D S x.val
  map_comp x y z := by
    have h := congrArg (fun f => (tensorIso φ (quotientHom A D S x.val y.val)
      (quotientHom A D S y.val z.val)).inv ≫ f)
      (quotientComposition_baseChange φ D S x.val y.val z.val)
    simp only [compareTensor, Category.assoc, Iso.inv_hom_id_assoc] at h
    exact h

instance quotientBaseChangeDGFunctor_hom_isIso (S : Set D)
    (x y : DGBaseChange φ (QuotientObject D S)) :
    IsIso ((quotientBaseChangeDGFunctor φ D S).map x y) :=
  Iso.isIso_hom (quotientHomBaseChangeIso φ D S x.val y.val)

/-- 最終 Hom の比較も同じ有限語 w の包含成分を保つ。 -/
lemma quotientHomBaseChangeIso_path_component (S : Set D) (x y : D) (w : Word S) (n : ℤ) :
    (ModuleCat.extendScalars φ).map ((ι A D S x y w).f n) ≫
        (quotientHomBaseChangeIso φ D S x y).hom.f n =
      (termBaseChangeIso φ D w x y).hom.f n ≫ (ι A' (DGBaseChange φ D) S x y w).f n := by
  have h := congrArg (fun f => f.f n) (map_ι_internalHomBaseChangeIso φ D S x y w)
  convert h using 1 <;> rfl

lemma quotientBaseChangeDGFunctor_inclusion (S : Set D) :
    (dgFunctor φ (inclusion A D S)).comp (quotientBaseChangeDGFunctor φ D S) =
      inclusion A' (DGBaseChange φ D) S := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (dgFunctor φ (inclusion A D S)).comp (quotientBaseChangeDGFunctor φ D S))
    (G := inclusion A' (DGBaseChange φ D) S) (fun _ => rfl)
  intro x y
  exact originalHomInclusion_baseChange φ D S x y

end SerrePositivity.DifferentialGraded.DGQuotient
