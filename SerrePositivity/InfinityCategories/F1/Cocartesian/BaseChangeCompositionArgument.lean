module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleTerminalAction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomTransportComposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoPrecompositionProjection

/-!
概要：元の大域三角形と局所結合比較で輸送結合同型を引き戻す二つの引数は一致する。
方針：同じ終点作用の厳密な回収と指定同型の二段の前合成則を使う。
規約：既存の輸送結合同型と元の全 Hom 作用を保持する。
使われ方：元の三角形の貼り合わせ等式を局所自然性の指定値へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全 Hom 上で、大域三角形と局所比較は同じ輸送結合同型の指定値を回収する。 -/
lemma cocartesianBaseChangeHomTransport_compositionIso_argument_heq
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    HEq (((cocartesianBaseChangeHomTransport_compositionIso l k p q).precomp
      (cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q)).precomp
          (cocartesianBaseChangeTriangleHomComparison l k p q))
      (((cocartesianBaseChangeHomTransport_compositionIso l k p q).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
          cocartesianStraighteningHomInterval
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q))).precomp
              ((SSet.uliftFunctor.{u + 1, u}).map
                  ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
                (SSet.uliftFunctor.{u + 1, u}).map
                  ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
                    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
                    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))) := by
  exact functorIso_precomp_square_heq
    (cocartesianBaseChangeHomTransport_compositionIso l k p q)
    (cocartesianBaseChangeTriangleHomLong l k p q ≫
      cocartesianBaseChangeHomSpanOne (l ⋙ k) p q)
    (cocartesianBaseChangeTriangleHomComparison l k p q)
    ((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q))
    _ (cocartesianBaseChangeTriangleHomComparison_terminal_native l k p q)

end SerrePositivity.InfinityCategories
