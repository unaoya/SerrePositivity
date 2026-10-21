module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleHomSecond
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleHomFirst
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeRestrictedHomSpan
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeHomSpan
public import SerrePositivity.InfinityCategories.F1.IntervalHomPostcompositionEquality
public import SerrePositivity.InfinityCategories.F1.EquivalenceTriangleFaceEvaluation

/-!
概要：元の比較三角形の共有頂点における Hom 射影の厳密な一致。
方針：元の面の合成の等式を、正規化した同じ Hom 作用へ移す。
規約：元の制限した比較・第二面・直接の比較の同じ span を使う。
使われ方：元の直接の Hom 輸送を含む三角形則。
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
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の比較三角形の最初の面と第二面は、同じ中間の分類 Hom を厳密に共有する。 -/
lemma cocartesianBaseChangeTriangleHom_middle :
    cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanOne l k p q =
      cocartesianBaseChangeTriangleHomSecond l k p q ≫
        cocartesianBaseChangeSecondHomSpanZero l k p q := by
  unfold cocartesianBaseChangeTriangleHomFirst cocartesianBaseChangeRestrictedHomSpanOne
    cocartesianBaseChangeTriangleHomSecond intervalHomFamilyProjection
    cocartesianBaseChangeSecondHomSpanZero intervalHomPathEndpoint
  apply intervalMappingPostOfEq_comp_congr
  rw [equivalenceTriangleFace_endpoint, equivalenceTriangleFace_endpoint]
  exact congrArg (equivalenceTriangleEvaluation _) (show
    (2 : Fin 3).succAbove (1 : Fin 2) = (0 : Fin 3).succAbove (0 : Fin 2) by decide)

/-- 元の直接の比較と第二面は、同じ終点の分類 Hom を厳密に共有する。 -/
lemma cocartesianBaseChangeTriangleHom_second_one :
    cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q =
      cocartesianBaseChangeTriangleHomSecond l k p q ≫
        cocartesianBaseChangeSecondHomSpanOne l k p q := by
  unfold cocartesianBaseChangeTriangleHomLong cocartesianBaseChangeHomSpanOne
    cocartesianBaseChangeTriangleHomSecond intervalHomFamilyProjection
    cocartesianBaseChangeSecondHomSpanOne intervalHomPathEndpoint
  apply intervalMappingPostOfEq_comp_congr
  rw [equivalenceTriangleFace_endpoint, equivalenceTriangleFace_endpoint]
  exact congrArg (equivalenceTriangleEvaluation _) (show
    (1 : Fin 3).succAbove (1 : Fin 2) = (0 : Fin 3).succAbove (1 : Fin 2) by decide)

end SerrePositivity.InfinityCategories
