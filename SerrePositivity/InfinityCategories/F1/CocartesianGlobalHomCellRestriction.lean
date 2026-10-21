module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexCorrectedGlobalData
public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackRestrictionNaturality

/-!
概要：元の全 Hom の底変換は、同じ共有セルへの直接の制限に厳密に整合する。
方針：底変換の元の全 Hom 作用を native 制限として表示し、その自然性を使う。
規約：元の全相対 Hom と同じ底上の射を保持する。
使われ方：元の全 Hom から同じ二辺の source pullback への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 元の底変換と同じ共有セルへの制限は、元の直接の底変換に厳密に一致する。 -/
lemma cocartesianSingleBaseChangeHomAction_cellOver
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (v : A ⥤ C) (h : l ⋙ k = v)
    (p q : CocartesianFibrationCategory (nerve C)) :
    cocartesianSingleBaseChangeHomAction k p q ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
          (cocartesianCellOverMap l k v h))) =
    cocartesianSingleBaseChangeHomAction v p q := by
  change (SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreFunctor.map
      (cocartesianPullbackNativeRestriction p.val.hom q.val.hom (Over.mk (nerveMap k)))) ≫
    (SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreFunctor.map
      (cocartesianPullbackNativePre p.val.hom q.val.hom (cocartesianCellOverMap l k v h))) =
    (SSet.uliftFunctor.{u + 1, u}).map (quasicategoryCoreFunctor.map
      (cocartesianPullbackNativeRestriction p.val.hom q.val.hom (Over.mk (nerveMap v))))
  rw [← Functor.map_comp, ← Functor.map_comp,
    cocartesianPullbackNativeRestriction_naturality]

end SerrePositivity.InfinityCategories
