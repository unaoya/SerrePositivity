module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeHomTransportIso
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomTransportComposition
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalHomComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalNativeFactorization

/-!
概要：元の二重局所比較は、指定結合同型で運んだ直接の局所比較と関手同型。
方針：全局所 Hom 上の結合比較と、既存の同じ Hom 輸送の合成則を結合する。
規約：元の分類作用・局所比較・正規化を保持する。
使われ方：同じ共有頂点への制限と Segal 比較の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の直接・二重局所比較は、同じ指定結合同型に沿って全局所 Hom 上で整合する。 -/
def cocartesianIteratedLocalHomComparison_nativeIso
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    FunctorIso
      (((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
        cocartesianLocalHomComparison (l ⋙ k) p q) ≫
        cocartesianBaseChangeHomCompositionNormalization l k p q)
      (cocartesianIteratedLocalHomComparison l k p q) :=
  F2.functorIsoOfEq (cocartesianIteratedLocalNativeCompositeIso l k p q)
    (cocartesianIteratedLocalNativeComposite_source l k p q)
    (cocartesianIteratedLocalNativeComposite_target l k p q)

end SerrePositivity.InfinityCategories
