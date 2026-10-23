module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeOriginalGlobalTriangleIsos

/-!
概要：元の輸送三角形の四端点を、指定された大域自然性因子と同じ表示で回収する。
方針：第二辺の両端と制限正方形の零射影を使う。
規約：元の全 Hom 作用と同じ四つの指定同型を保持する。
使われ方：元の三角等式への指定局所因子の代入。
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

/-- 元の輸送三角形の始点は、同じ第二辺の指定因子の合成の始点。 -/
lemma cocartesianBaseChangeGlobalTriangle_source :
    (cocartesianBaseChangeOriginalGlobalCompositionIso l k p q).sourceMap =
    ((cocartesianBaseChangeSecondGlobalNaturalityIso l k p q).postcomp
      (cocartesianBaseChangeRestrictedHomTransport l k p q)).sourceMap := by
  have h := congrArg (fun m ↦ m ≫ cocartesianBaseChangeRestrictedHomTransport l k p q)
    (cocartesianBaseChangeTriangleSecond_originalHom_source l k p q)
  simpa only [FunctorIso.sourceMap, Category.assoc] using h

/-- 元の輸送三角形の右中間頂点は、同じ指定第一辺の始点。 -/
lemma cocartesianBaseChangeGlobalTriangle_middle :
    (cocartesianBaseChangeOriginalGlobalFirstIso l k p q).sourceMap =
    (cocartesianBaseChangeFirstGlobalFactorIso l k p q).sourceMap := by
  have h := congrArg (fun m ↦ m ≫ cocartesianBaseChangeRestrictedHomTransport l k p q)
    (cocartesianBaseChangeTriangleSecond_originalHom_target l k p q)
  simpa only [FunctorIso.sourceMap, Category.assoc] using h

/-- 元の輸送三角形の終点は、同じ指定第一辺の終点。 -/
lemma cocartesianBaseChangeGlobalTriangle_target :
    (cocartesianBaseChangeOriginalGlobalFirstIso l k p q).targetMap =
    (cocartesianBaseChangeFirstGlobalFactorIso l k p q).targetMap := by
  have h₁ := congrArg (fun m ↦ m ≫ cocartesianBaseChangeRestrictedHomSpanZero l k p q)
    (cocartesianBaseChangeTriangleHomComparison_first_restriction l k p q)
  have h₂ := congrArg (fun m ↦ cocartesianBaseChangeHomComparison k p q ≫ m)
    (cocartesianBaseChangeRestrictedHomMap_zero l k p q).symm
  have h₃ := congrArg (fun m ↦ m ≫ cocartesianBaseChangeHomRestrictionZero l k p q)
    (cocartesianBaseChangeHomComparison_zero k p q)
  have h := h₁.trans
    ((Category.assoc _ _ _).trans (h₂.trans (Category.assoc _ _ _).symm))
  simpa only [FunctorIso.targetMap, Category.assoc] using h.trans h₃

end SerrePositivity.InfinityCategories
