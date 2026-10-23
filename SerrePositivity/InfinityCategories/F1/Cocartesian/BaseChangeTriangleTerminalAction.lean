module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondCompositeNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleHomMiddle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeHomRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportNativeHomMap

/-!
概要：元の三角形の終点作用は、二重底変換と指定結合共役後の同じ分類作用。
方針：二つの三角形の同じ終点を射影し、全局所比較の同じ大域制限を回収する。
規約：元の全 Hom 作用と指定共役を保持する。
使われ方：結合輸送同型を前合成する二つの元の引数を厳密に照合する。
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

/-- 元の主三角形の終点作用と、分解三角形の結合辺の同じ終点作用は一致する。 -/
lemma cocartesianBaseChangeTriangleHomComparison_terminal :
    cocartesianBaseChangeTriangleHomComparison l k p q ≫
      (cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q) =
    cocartesianBaseChangeSecondTriangleHomComparison l k p q ≫
      (cocartesianBaseChangeSecondTriangleHomSecond l k p q ≫
        cocartesianBaseChangeAssociativityHomSpanOne l k p q) := by
  rw [cocartesianBaseChangeTriangleHom_second_one, ← Category.assoc,
    ← cocartesianBaseChangeSecondTriangleHomComparison_decomposition,
    Category.assoc, cocartesianBaseChangeSecondHomDecomposition_one]

/-- 元の終点作用は、元の二重底変換と同じ指定 Hom 共役に続く分類作用そのもの。 -/
lemma cocartesianBaseChangeTriangleHomComparison_terminal_native :
    cocartesianBaseChangeTriangleHomComparison l k p q ≫
      (cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q) =
    ((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
        cocartesianStraighteningHomInterval
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q)) := by
  have h := congrArg (fun f ↦ f ≫ cocartesianBaseChangeAssociativityHomSpanOne l k p q)
    ((cocartesianBaseChangeSecondTriangleHomComparison_second l k p q).trans
      (cocartesianIsoTransportNativeHomComparison_doubleBaseChange l k p q).symm)
  simp only [Category.assoc] at h
  rw [cocartesianIsoTransportNativeHomComparison_one,
    cocartesianIsoTransportNativeHomMap_eq] at h
  exact (cocartesianBaseChangeTriangleHomComparison_terminal l k p q).trans h

end SerrePositivity.InfinityCategories
