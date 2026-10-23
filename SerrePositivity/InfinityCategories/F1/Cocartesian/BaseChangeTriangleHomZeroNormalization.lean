module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomMiddle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomCompositionNormalization

/-!
概要：元の直接の比較と底制限した比較の Hom の零評価は、同じ端点表示変更で一致。
方針：元の恒等写像による表示変更を合成し、同じ三角形の初頂点を比較する。
規約：元の直接の比較 span と底制限した元の span を保持する。
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

/-- 元の直接の零評価は、同じ表示変更後に元の底制限した零評価と厳密に一致。 -/
lemma cocartesianBaseChangeTriangleHom_zero_normalization
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    (cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanZero (l ⋙ k) p q) ≫
          cocartesianBaseChangeHomCompositionNormalization l k p q =
      cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanZero l k p q := by
  unfold cocartesianBaseChangeTriangleHomLong cocartesianBaseChangeHomSpanZero
    cocartesianBaseChangeHomCompositionNormalization cocartesianBaseChangeTriangleHomFirst
    cocartesianBaseChangeRestrictedHomSpanZero intervalHomPathEndpoint
  rw [Category.assoc, intervalMappingPostOfEq_comp]
  apply intervalMappingPostOfEq_comp_congr
  rw [Category.comp_id, equivalenceTriangleFace_endpoint, equivalenceTriangleFace_endpoint]
  exact congrArg (equivalenceTriangleEvaluation _) (show
    (1 : Fin 3).succAbove (0 : Fin 2) = (2 : Fin 3).succAbove (0 : Fin 2) by decide)

end SerrePositivity.InfinityCategories
