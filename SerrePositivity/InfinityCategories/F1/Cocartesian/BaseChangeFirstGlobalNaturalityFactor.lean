module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictionNormalizedIdentity
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNaturalityFactorCoherence

/-!
概要：元の三角形の第一辺を、元の大域自然性と同じ分類作用の端点へ正規化する。
方針：同じ大域 Hom 比較の零・一射影を制限した厳密な等式を使う。
規約：元の第一辺の指定因子と全 Hom 作用を保持する。
使われ方：指定三辺の貼り合わせを局所自然性の三角等式へ移す。
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

/-- 正規化した第一辺の始点は、底変換後の分類作用を制限して輸送したもの。 -/
lemma cocartesianBaseChangeFirstGlobalFactor_source :
    (((cocartesianBaseChangeHomComparison k p q ≫
      cocartesianBaseChangeHomSpanOne k p q) ≫
        cocartesianBaseChangeHomRestrictionOne l k p q) ≫
          cocartesianBaseChangeRestrictedHomTransport l k p q) =
    (((SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫
      cocartesianBaseChangeHomRestrictionOne l k p q) ≫
        cocartesianBaseChangeRestrictedHomTransport l k p q := by
  rw [cocartesianBaseChangeHomComparison_one]

/-- 正規化した第一辺の終点は、元の分類作用の同じ二回の制限。 -/
lemma cocartesianBaseChangeFirstGlobalFactor_target :
    ((cocartesianBaseChangeHomComparison k p q ≫
      cocartesianBaseChangeHomSpanZero k p q) ≫
        cocartesianBaseChangeHomRestrictionZero l k p q) =
    (cocartesianStraighteningHomInterval p q ≫
      intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)) ≫
      cocartesianBaseChangeHomRestrictionZero l k p q := by
  rw [cocartesianBaseChangeHomComparison_zero]

/-- 元の大域自然性と同じ分類作用の端点へ移した、指定された第一辺。 -/
def cocartesianBaseChangeFirstGlobalFactorIso :=
  F2.functorIsoOfEq (cocartesianBaseChangeRestrictedGlobalNormalizedFactorIso l k p q)
    (cocartesianBaseChangeFirstGlobalFactor_source l k p q)
    (cocartesianBaseChangeFirstGlobalFactor_target l k p q)

/-- 同じ大域自然性の表示への正規化は、元の三角形の指定された第一辺を保持する。 -/
lemma cocartesianBaseChangeFirstGlobalFactorIso_first_heq :
    HEq (cocartesianBaseChangeFirstGlobalFactorIso l k p q)
      ((cocartesianBaseChangeTriangleHomFirst_restrictedTransportIso l k p q).precomp
        (cocartesianBaseChangeTriangleHomComparison l k p q)) := by
  exact HEq.trans (F2.functorIsoOfEq_heq _ _ _)
    (cocartesianBaseChangeRestrictedGlobalNormalizedFactorIso_first_heq l k p q)

end SerrePositivity.InfinityCategories
