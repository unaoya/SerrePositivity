module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFilteredGeometricDetection
public import SerrePositivity.InfinityCategories.Core.CatInfinity.CoconeValEquality

/-!
概要：filtered 余極限と幾何学的実現の保存は関手の合成で保たれる。
方針：元の全余錐を順に写す。
規約：同じ指定全余錐の像を比較する。
使われ方：有限余積の座標ごとの Yoneda 生成による検出。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open Ind

/-- 概要：小さい filtered 余極限を保つ二関手の合成も同じ余極限を保つ。
方針：指定全余錐を順に写す。
規約：元の小さい形状を保つ。
使われ方：各座標での生成表示の保存。 -/
lemma preservesSmallFilteredColimits_comp {X Y Z : SSet.{u + 1}}
    {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : PreservesSmallKappaFilteredColimits Cardinal.aleph0 F)
    (hG : PreservesSmallKappaFilteredColimits Cardinal.aleph0 G) :
    PreservesSmallKappaFilteredColimits Cardinal.aleph0 (F ≫ G) := by
  intro I hI hκ p c hc
  have h := hG I _ _ (hF I p c hc)
  exact (isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc c.val F G).symm).mpr h

/-- 概要：幾何学的実現を保つ二関手の合成も同じ実現を保つ。
方針：元の単体的全余錐の像を順に取る。
規約：元の指定実現余錐を保つ。
使われ方：各座標での単体的 Ind 表示の保存。 -/
lemma preservesSmallGeometricRealizations_comp {X Y Z : SSet.{u + 1}}
    {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : PreservesSmallGeometricRealizations F) (hG : PreservesSmallGeometricRealizations G) :
    PreservesSmallGeometricRealizations (F ≫ G) := by
  intro p c hc
  have h := hG _ _ (hF p c hc)
  exact (isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc c.val F G).symm).mpr h

end SerrePositivity.InfinityCategories.F2.Presentable
