module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeHomTransportIso
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomTransportComposition
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalHomComparison
public import SerrePositivity.InfinityCategories.F1.FunctorIsoSquareIdentity

/-!
概要：既存の指定局所結合比較を作る元の二因子と、その両端の正規化。
方針：同じ指定結合同型と結合輸送を保持し、端点の等式だけを分離する。
規約：既存の局所結合比較の指定値を選び直さない。
使われ方：元の全 Hom 上の三角等式を既存の局所自然性に照合する。
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

/-- 既存の局所結合比較の第一因子で使う、元の輸送結合同型。 -/
def cocartesianIteratedLocalNativeCompositionIso :=
  (cocartesianBaseChangeHomTransport_compositionIso l k p q).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q))

/-- 既存の局所結合比較の第二因子で使う、元の指定結合輸送。 -/
def cocartesianIteratedLocalNativeTransportFactorIso :=
  (cocartesianBaseChangeNativeHomTransportIso l k p q).postcomp
    (cocartesianBaseChangeHomTransport l
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
      cocartesianBaseChangeRestrictedHomTransport l k p q)

/-- 二つの指定因子の中間作用は、結合順序を除いて同じ射。 -/
lemma cocartesianIteratedLocalNativeTransportFactor_source :
    (cocartesianIteratedLocalNativeTransportFactorIso l k p q).sourceMap =
    (cocartesianIteratedLocalNativeCompositionIso l k p q).sourceMap := by
  simp only [FunctorIso.sourceMap, Category.assoc]

/-- 指定された第二因子の始点だけを、第一因子と同じ表示にそろえる。 -/
def cocartesianIteratedLocalNativeNormalizedTransportFactorIso :=
  F2.functorIsoOfEq (cocartesianIteratedLocalNativeTransportFactorIso l k p q)
    (cocartesianIteratedLocalNativeTransportFactor_source l k p q) rfl

/-- 既存の局所結合比較を作る、同じ二因子の指定合成。 -/
def cocartesianIteratedLocalNativeCompositeIso :
    FunctorIso (cocartesianIteratedLocalNativeCompositionIso l k p q).targetMap
      (cocartesianIteratedLocalNativeTransportFactorIso l k p q).targetMap :=
  (cocartesianIteratedLocalNativeCompositionIso l k p q).symm ≪≫
    cocartesianIteratedLocalNativeNormalizedTransportFactorIso l k p q

/-- 指定合成の始点は、同じ直接の局所比較に続く表示正規化。 -/
lemma cocartesianIteratedLocalNativeComposite_source :
    (cocartesianIteratedLocalNativeCompositionIso l k p q).targetMap =
    (((SSet.uliftFunctor.{u + 1, u}).map (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
      cocartesianLocalHomComparison (l ⋙ k) p q) ≫
      cocartesianBaseChangeHomCompositionNormalization l k p q) := by
  simp only [FunctorIso.targetMap, cocartesianLocalHomComparison, Category.assoc]

/-- 指定合成の終点は、同じ二回の局所比較。 -/
lemma cocartesianIteratedLocalNativeComposite_target :
    (cocartesianIteratedLocalNativeTransportFactorIso l k p q).targetMap =
    cocartesianIteratedLocalHomComparison l k p q := by
  simp only [FunctorIso.targetMap, cocartesianIteratedLocalHomComparison,
    cocartesianLocalHomComparison, Category.assoc]

end SerrePositivity.InfinityCategories
