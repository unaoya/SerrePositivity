module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeSectionAction
public import SerrePositivity.InfinityCategories.F1.CocartesianSectionsEnrichedEvaluation

/-!
概要：元の全空間の結合同型の豊穣 section 評価は、既存の結合比較の curry。
方針：同じ全パラメーターの section 作用の等式を curry し、core の通常の射へ戻す。
規約：元の結合共役の分類像を別の比較へ置き換えない。
使われ方：同じ分類像の辺と既存の結合 Hom 輸送の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 元の結合同型の豊穣 section 評価は、既存の同じ結合比較成分を表す。 -/
lemma cocartesianBaseChangeNativeObjectIso_sectionPostHom
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C)) (a : A) :
    (eHomEquiv SSet.{u} (cocartesianBaseChangeNativeObjectIso l k p).hom ≫
      (quasicategoryCore (cocartesianRelativeFunctorSpace
        (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom))
        (pullback.fst (nerveMap (l ⋙ k)) p.val.hom))).ι) ≫
      cocartesianSectionsPostHom (Over.mk (nerveMap (Under.forget a)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)))
        (Over.mk (pullback.fst (nerveMap (l ⋙ k)) p.val.hom)) =
    curry' (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom := by
  apply uncurry_injective
  rw [uncurry_natural_left, cocartesianSectionsPostHom, uncurry_curry,
    curry', uncurry_curry]
  apply (cancel_epi (ρ_ (kanCocartesianStrictTransport
    (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom)) a)).inv).mp
  simpa only [kanCocartesianStrictTransport, Over.mk_hom, Category.assoc,
    Iso.inv_hom_id_assoc] using
    cocartesianBaseChangeNativeObjectIso_sectionAction l k p a

/-- 同じ結合同型の core 豊穣評価も、既存の同じ結合比較成分の豊穣表示そのもの。 -/
lemma cocartesianBaseChangeNativeObjectIso_sectionCoreHom
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C)) (a : A) :
    let S := cocartesianSectionsCoreEnrichedEvaluation (Over.mk (nerveMap (Under.forget a)))
    let P₂ := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
    let P₁ := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p
    eHomEquiv SSet.{u} (cocartesianBaseChangeNativeObjectIso l k p).hom ≫ S.map P₂ P₁ =
      eHomEquiv SSet.{u} (show S.obj P₂ ⟶ S.obj P₁ from
        (cocartesianBaseChangeAssociativityComponent p.val.hom l k a).hom) := by
  dsimp only
  apply (SSet.unitHomEquiv _).injective
  apply Subtype.ext
  exact congrArg (SSet.unitHomEquiv _)
    (cocartesianBaseChangeNativeObjectIso_sectionPostHom l k p a)

end SerrePositivity.InfinityCategories
