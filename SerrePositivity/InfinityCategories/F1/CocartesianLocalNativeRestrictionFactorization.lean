module

public import SerrePositivity.InfinityCategories.F1.CocartesianIteratedLocalHomNativeIso
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeRestriction
public import SerrePositivity.InfinityCategories.F1.FunctorIsoSquareIdentity

/-!
概要：既存の局所自然性を作る結合比較・制限自然性の指定合成と、始点の回収。
方針：元の同じ二因子を保持し、指定共役と底変換の厳密な合成則だけを分離する。
規約：既存の局所自然性の指定値を選び直さない。
使われ方：元の全 Hom 上で、既存の局所自然性と三辺の等式を照合する。
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

/-- 既存の局所自然性の第一因子で使う、同じ二回目の底変換で引き戻した結合比較。 -/
def cocartesianLocalNativeRestrictionNativeFactorIso :=
  (cocartesianIteratedLocalHomComparison_nativeIso l k p q).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))

/-- 既存の局所自然性を作る、同じ結合比較と制限自然性の指定合成。 -/
def cocartesianLocalNativeRestrictionCompositeIso :
    FunctorIso (cocartesianLocalNativeRestrictionNativeFactorIso l k p q).sourceMap
      (cocartesianIteratedLocalHomComparison_restrictionIso l k p q).targetMap :=
  cocartesianLocalNativeRestrictionNativeFactorIso l k p q ≪≫
    cocartesianIteratedLocalHomComparison_restrictionIso l k p q

/-- 同じ指定共役に続く二回目の底変換は、元の直接の底上の制限に一致する。 -/
lemma cocartesianLocalNativeRestrictionNativeFactor_source :
    (cocartesianLocalNativeRestrictionNativeFactorIso l k p q).sourceMap =
    (((SSet.uliftFunctor.{u + 1, u}).map
      (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
        (cocartesianBaseChangeOverMap l k))) ≫
      cocartesianLocalHomComparison (l ⋙ k) p q) ≫
      cocartesianBaseChangeHomCompositionNormalization l k p q) := by
  have h₀ := ((SSet.uliftFunctor.{u + 1, u}).map_comp
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))
    (cocartesianBaseChangeNativeHomIso l k p q).hom).symm.trans
      (congrArg (fun m ↦ (SSet.uliftFunctor.{u + 1, u}).map m)
        (cocartesianBaseChangeNativeHomIso_restriction l k p q))
  have h := congrArg (fun m ↦
    (m ≫ cocartesianLocalHomComparison (l ⋙ k) p q) ≫
      cocartesianBaseChangeHomCompositionNormalization l k p q) h₀
  simpa only [FunctorIso.sourceMap, Category.assoc] using h

end SerrePositivity.InfinityCategories
