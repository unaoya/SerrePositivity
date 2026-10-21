module

public import SerrePositivity.InfinityCategories.F1.CocartesianIsoTransportNativeHomFactor

/-!
概要：全局所 Hom の結合共役の分類像は、既存の結合 Hom 輸送で元の分類作用へ戻る。
方針：同じ結合 span の両評価を回収し、元の一射影の指定切断による輸送を使う。
規約：同じ元の全局所 Hom・比較 path・切断を保持する。
使われ方：共有頂点での局所 Hom 比較の自然性と Segal 降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の全局所 Hom の共役分類作用を、既存の同じ結合 Hom 輸送で戻す関手同型。 -/
def cocartesianIsoTransportNativeHomTransportIso :
    FunctorIso
      (((SSet.uliftFunctor.{u + 1, u}).map (cocartesianIsoTransportNativeHomMap l k p q) ≫
        cocartesianStraighteningHomInterval
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q)) ≫
        cocartesianBaseChangeAssociativityHomTransport l k p q)
      (cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) :=
  F2.functorIsoOfEq (cocartesianIsoTransportNativeHomFactorIso l k p q)
    (congrArg (fun f ↦ f ≫ cocartesianBaseChangeAssociativityHomTransport l k p q)
      (cocartesianIsoTransportNativeHomComparison_one l k p q))
    (cocartesianIsoTransportNativeHomComparison_zero l k p q)

end SerrePositivity.InfinityCategories
