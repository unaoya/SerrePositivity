module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeGlobalTransportTriangle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeCompositionArgument
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalNativeFactorization

/-!
概要：元の三角形の結合因子は、既存の局所結合比較と同じ指定値・両端を回収する。
方針：同じ終点作用の二分解から前合成の両端と指定値を回収する。
規約：元の二重底変換・全 Hom・指定輸送結合同型を保持する。
使われ方：既存の局所結合比較の前合成と三辺の第一因子を照合する。
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

/-- 元の全 Hom に作用する同じ二回の底変換。 -/
def cocartesianDoubleBaseChangeHomAction :=
  (SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
  (SSet.uliftFunctor.{u + 1, u}).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))

/-- 同じ結合同型の前合成は、大域三角形と局所結合比較で両端の同じ作用を回収する。 -/
lemma cocartesianBaseChangeOriginalGlobalComposition_native_endpoints :
    (cocartesianBaseChangeOriginalGlobalCompositionIso l k p q).sourceMap =
      ((cocartesianIteratedLocalNativeCompositionIso l k p q).precomp
        (cocartesianDoubleBaseChangeHomAction l k p q)).sourceMap ∧
    (cocartesianBaseChangeOriginalGlobalCompositionIso l k p q).targetMap =
      ((cocartesianIteratedLocalNativeCompositionIso l k p q).precomp
        (cocartesianDoubleBaseChangeHomAction l k p q)).targetMap := by
  exact FunctorIso.precomp_square_endpoints
    (cocartesianBaseChangeHomTransport_compositionIso l k p q)
    (cocartesianBaseChangeTriangleHomLong l k p q ≫
      cocartesianBaseChangeHomSpanOne (l ⋙ k) p q)
    (cocartesianBaseChangeTriangleHomComparison l k p q)
    ((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q))
    (cocartesianDoubleBaseChangeHomAction l k p q)
    (cocartesianBaseChangeTriangleHomComparison_terminal_native l k p q)

/-- 端点正規化した結合因子の始点も、同じ既存の局所結合比較から回収される。 -/
lemma cocartesianBaseChangeGlobalComposition_native_source :
    ((cocartesianIteratedLocalNativeCompositionIso l k p q).precomp
      (cocartesianDoubleBaseChangeHomAction l k p q)).sourceMap =
    (cocartesianBaseChangeGlobalTransportCompositionIso l k p q).sourceMap := by
  exact functorIsoOfEq_sourceMap_of_eq
    (cocartesianBaseChangeOriginalGlobalCompositionIso l k p q)
    (cocartesianBaseChangeGlobalTriangle_source l k p q) rfl
    (cocartesianBaseChangeOriginalGlobalComposition_native_endpoints l k p q).1.symm

/-- 同じ結合因子の終点も、既存の局所結合比較から回収される。 -/
lemma cocartesianBaseChangeGlobalComposition_native_target :
    ((cocartesianIteratedLocalNativeCompositionIso l k p q).precomp
      (cocartesianDoubleBaseChangeHomAction l k p q)).targetMap =
    (cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap := by
  exact functorIsoOfEq_targetMap_of_eq
    (cocartesianBaseChangeOriginalGlobalCompositionIso l k p q)
    (cocartesianBaseChangeGlobalTriangle_source l k p q) rfl
    (cocartesianBaseChangeOriginalGlobalComposition_native_endpoints l k p q).2.symm

/-- 元の全 Hom 上の結合因子は、既存の局所結合比較と同じ指定値を回収する。 -/
lemma cocartesianBaseChangeGlobalComposition_native_heq :
    HEq (cocartesianBaseChangeGlobalTransportCompositionIso l k p q)
      ((cocartesianIteratedLocalNativeCompositionIso l k p q).precomp
        (cocartesianDoubleBaseChangeHomAction l k p q)) := by
  exact HEq.trans (F2.functorIsoOfEq_heq _ _ _)
    (cocartesianBaseChangeHomTransport_compositionIso_argument_heq l k p q)

end SerrePositivity.InfinityCategories
