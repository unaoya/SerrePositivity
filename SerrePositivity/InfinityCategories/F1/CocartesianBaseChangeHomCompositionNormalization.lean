module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomSpan
public import SerrePositivity.InfinityCategories.F1.PointedRightFiberComparison

/-!
概要：合成した底の射と二回の制限の元の分類 Hom の端点表示を揃える。
方針：nerve と宇宙持ち上げの合成公式を使い、恒等写像の同じ Hom 作用で表示を変える。
規約：元の分類図式と Hom の全区間族を保持する厳密な同型。
使われ方：元の直接の Hom 輸送を含む合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 元の分類図式の底の合成による制限は、元の二回の制限と厳密に一致。 -/
lemma cocartesianBaseChangeClassifiedRestriction_comp
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ CatInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k)) ≫ F =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫ F := by
  have h : nerveMap (l ⋙ k) = nerveMap l ≫ nerveMap k := rfl
  rw [h, Functor.map_comp, Category.assoc]

/-- 元の二つの制限の端点表示を、同じ恒等写像の Hom 作用で揃える。 -/
def cocartesianBaseChangeHomCompositionNormalization
    (p q : CocartesianFibrationCategory (nerve C)) :
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k)) ≫
        cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k)) ≫
        cocartesianStrictTransportCoherentDiagram q.val.hom)) ⟶
    intervalMappingSpace
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram p.val.hom))
      (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k) ≫
          cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  intervalMappingPostOfEq (𝟙 (CatInfinityFunctor
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve A))))
    (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k)) ≫
      cocartesianStrictTransportCoherentDiagram p.val.hom))
    (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k)) ≫
      cocartesianStrictTransportCoherentDiagram q.val.hom))
    (congrArg functorVertex (cocartesianBaseChangeClassifiedRestriction_comp l k _))
    (congrArg functorVertex (cocartesianBaseChangeClassifiedRestriction_comp l k _))

/-- 同じ端点の表示変更そのものは厳密な同型。 -/
instance cocartesianBaseChangeHomCompositionNormalization_isIso
    (p q : CocartesianFibrationCategory (nerve C)) :
    IsIso (cocartesianBaseChangeHomCompositionNormalization l k p q) :=
  intervalMappingPostOfEq_id_isIso _ _

end SerrePositivity.InfinityCategories
