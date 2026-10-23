module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondAssociativityNaturality

/-!
概要：第二面の結合比較を元の全 Hom に戻した両端を、同じ二重底変換 Hom 作用で表示する。
方針：元の結合 Hom 比較の回収則と同じ両射影の等式を使う。
規約：元の全 Hom・指定共役・分類作用を保持する。
使われ方：第二辺の指定比較を既存の局所自然性の合成へ正規化する。
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

/-- 同じ結合比較の始点は、二重底変換に続く元の指定共役の分類作用と輸送。 -/
lemma cocartesianBaseChangeSecondAssociativity_originalHom_source :
    cocartesianBaseChangeSecondTriangleHomComparison l k p q ≫
      ((cocartesianBaseChangeSecondTriangleHomSecond l k p q ≫
        cocartesianBaseChangeAssociativityHomSpanOne l k p q) ≫
          cocartesianBaseChangeAssociativityHomTransport l k p q) =
    ((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) ≫
      (((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
        cocartesianStraighteningHomInterval
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q)) ≫
        cocartesianBaseChangeAssociativityHomTransport l k p q) := by
  have h := congrArg (fun f ↦ f ≫
    (cocartesianBaseChangeAssociativityHomSpanOne l k p q ≫
      cocartesianBaseChangeAssociativityHomTransport l k p q))
    ((cocartesianBaseChangeSecondTriangleHomComparison_second l k p q).trans
      (cocartesianIsoTransportNativeHomComparison_doubleBaseChange l k p q).symm)
  simp only [Category.assoc] at h ⊢
  rw [← Category.assoc (cocartesianIsoTransportNativeHomComparison l k p q)
      (cocartesianBaseChangeAssociativityHomSpanOne l k p q)
      (cocartesianBaseChangeAssociativityHomTransport l k p q),
    cocartesianIsoTransportNativeHomComparison_one, cocartesianIsoTransportNativeHomMap_eq] at h
  simpa only [Category.assoc] using h

/-- 同じ中間評価は、元の二回の底変換後の分類作用そのもの。 -/
lemma cocartesianBaseChangeSecondAssociativity_originalHom_target :
    cocartesianBaseChangeSecondTriangleHomComparison l k p q ≫
      (cocartesianBaseChangeSecondTriangleHomFirst l k p q ≫
        cocartesianBaseChangeHomSpanOne l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) =
    ((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) := by
  have h := congrArg (fun f ↦ f ≫ cocartesianBaseChangeAssociativityHomSpanZero l k p q)
    ((cocartesianBaseChangeSecondTriangleHomComparison_second l k p q).trans
      (cocartesianIsoTransportNativeHomComparison_doubleBaseChange l k p q).symm)
  simp only [Category.assoc] at h
  rw [← cocartesianBaseChangeSecondTriangleHom_middle,
    cocartesianIsoTransportNativeHomComparison_zero] at h
  exact h

end SerrePositivity.InfinityCategories
