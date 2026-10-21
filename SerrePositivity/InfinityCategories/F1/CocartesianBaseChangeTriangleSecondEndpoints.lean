module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleTerminalAction
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleFirstNaturality

/-!
概要：元の第二辺の大域 Hom 上の両端を、局所結合輸送と大域自然性の合成の両端へ移す。
方針：同じ終点作用の回収と、最初の面の制限 span の両射影を使う。
規約：元の全 Hom・指定共役・分類作用を保持する。
使われ方：第二辺をさらに制限した指定値を元の三角等式に代入する。
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

/-- 第二辺の始点は、二重底変換・指定共役の分類作用に続く同じ二回の輸送。 -/
lemma cocartesianBaseChangeTriangleSecond_originalHom_source :
    cocartesianBaseChangeTriangleHomComparison l k p q ≫
      ((cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q) ≫
        (cocartesianBaseChangeAssociativityHomTransport l k p q ≫
          cocartesianBaseChangeHomTransport l
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) =
    (((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) ≫
      (((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
        cocartesianStraighteningHomInterval
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q)) ≫
        cocartesianBaseChangeAssociativityHomTransport l k p q)) ≫
      cocartesianBaseChangeHomTransport l
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) := by
  have h := congrArg (fun m ↦ m ≫
    (cocartesianBaseChangeAssociativityHomTransport l k p q ≫
      cocartesianBaseChangeHomTransport l
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))
    (cocartesianBaseChangeTriangleHomComparison_terminal_native l k p q)
  simpa only [Category.assoc] using h

/-- 第二辺の終点は、元の底変換後の分類作用を同じ底で制限したもの。 -/
lemma cocartesianBaseChangeTriangleSecond_originalHom_target :
    cocartesianBaseChangeTriangleHomComparison l k p q ≫
      (cocartesianBaseChangeTriangleHomFirst l k p q ≫
        cocartesianBaseChangeRestrictedHomSpanOne l k p q) =
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫
      cocartesianBaseChangeHomRestrictionOne l k p q := by
  have h := congrArg (fun m ↦ m ≫
    cocartesianBaseChangeRestrictedHomSpanOne l k p q)
    (cocartesianBaseChangeTriangleHomComparison_first_restriction l k p q)
  have h₂ := congrArg (fun m ↦ cocartesianBaseChangeHomComparison k p q ≫ m)
    (cocartesianBaseChangeRestrictedHomMap_one l k p q).symm
  have h₃ := congrArg (fun m ↦ m ≫ cocartesianBaseChangeHomRestrictionOne l k p q)
    (cocartesianBaseChangeHomComparison_one k p q)
  exact Eq.trans ((Category.assoc _ _ _).symm.trans h)
    (Eq.trans ((Category.assoc _ _ _).trans (h₂.trans (Category.assoc _ _ _).symm)) h₃)

end SerrePositivity.InfinityCategories
