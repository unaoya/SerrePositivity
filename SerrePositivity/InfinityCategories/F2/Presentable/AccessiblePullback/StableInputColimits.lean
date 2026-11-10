module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.StableInputPostcomp
public import SerrePositivity.InfinityCategories.F2.Presentable.SliceOverColimitCreation

/-!
概要：入力と標的を固定する後合成の底への射影と順序余極限の保存。
方針：元の底の関手の filtered 保存性と固定始域内の順序余極限判定を使う。
規約：同じ全余錐を保ち、全小余極限を要求しない。
使われ方：両成分の最終余極限を共通の底の全交互余極限へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：入力固定の二重後合成は元の底への二重射影を保つ。
方針：二つの既存射影公式を合成する。
規約：元の全単体上の厳密な等式。
使われ方：両成分表示とその像の compact 性の照合。 -/
lemma stableInputPostcomp_base_projection {K C B : SSet.{u}} (q : K ⟶ C) (f : C ⟶ B)
    (r : K ⟶ B) (hq : q ≫ f = r) (z : JoinCocone q) (t : JoinCocone r)
    (hz : z.val ≫ f = t.val) :
    stableInputPostcomp q f r hq z t hz ≫
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) ≫
        sliceUnderProjection r =
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
        sliceUnderProjection q ≫ f := by
  rw [← Category.assoc, stableInputPostcomp_projection, Category.assoc,
    stableCoslicePostcomp_projection]

/-- 概要：元の底で余極限となる始点付き順序余錐は、入力固定の後合成でも余極限。
方針：底の filtered 保存性を使い、固定始域と標的上の両方の圏で余極限性を検出する。
規約：元の全余錐と入力からの全射を保つ。
使われ方：元の compact 成分余極限の共通の底への比較。 -/
lemma stableInputPostcomp_orderBot_isColimitCone
    {κ : Cardinal.{u}} {K C B : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory C] [Quasicategory B]
    (q : K ⟶ C) (f : C ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ f)
    (r : K ⟶ B) (hq : q ≫ f = r) (z : JoinCocone q) (t : JoinCocone r)
    (hz : z.val ≫ f = t.val)
    (I : Type u) [Preorder I] [OrderBot I] [IsKappaFiltered κ (nerve I)]
    (P : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶
      sliceOver ((SSet.yonedaEquiv (X := sliceUnder q)).symm z))
    (c : JoinCocone P)
    (hc : IsColimitCone (mapJoinCocone
      (sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
        sliceUnderProjection q) c)) :
    IsColimitCone (mapJoinCocone (stableInputPostcomp q f r hq z t hz) c) := by
  let T := stableInputPostcomp q f r hq z t hz
  let d := mapJoinCocone T c
  apply sliceOver_isColimitCone_of_projection
    ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) d
  apply (fixedSource_orderBot_isColimitCone_iff_projection r I
    ((P ≫ T) ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t))
    (mapJoinCocone (sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t)) d)).mpr
  have h := hf (nerve I)
    (P ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
      sliceUnderProjection q)
    (mapJoinCocone (sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
      sliceUnderProjection q) c) hc
  apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
  change ((c.val ≫ T) ≫
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t)) ≫
      sliceUnderProjection r =
    (c.val ≫ (sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
      sliceUnderProjection q)) ≫ f
  simp only [Category.assoc]
  rw [stableInputPostcomp_base_projection]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
