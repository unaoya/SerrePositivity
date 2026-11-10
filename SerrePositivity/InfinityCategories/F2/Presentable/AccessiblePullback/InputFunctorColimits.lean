module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.StableInputColimits

/-!
概要：異なる固定入力を忘れる比較でも元の基底で順序余極限性を検出する。
方針：全基底射影の可換性と固定始域内の始点付き順序余極限判定を使う。
規約：元の対象圏には filtered 余極限保存だけを要求する。
使われ方：一方に指定 compact 始点を追加した相対交互構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：全基底射影を保つ入力比較は基底余極限で与えた順序余錐を余極限へ送る。
方針：標的上の slice と固定始域の coslice で元の基底の余極限性を検出する。
規約：始点付き順序図式のみを扱い、一般形状の保存性は主張しない。
使われ方：異なる入力付き表示から得た最終成分余極限の比較。 -/
lemma inputFunctor_orderBot_isColimitCone_of_base_projection
    {κ : Cardinal.{u}} {K L C B : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory L] [Quasicategory C] [Quasicategory B]
    (q : K ⟶ C) (f : C ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ f)
    (r : L ⟶ B) (z : JoinCocone q) (t : JoinCocone r)
    (T : sliceOver ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ⟶
      sliceOver ((SSet.yonedaEquiv (X := sliceUnder r)).symm t))
    (hT : T ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) ≫
        sliceUnderProjection r =
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
        sliceUnderProjection q ≫ f)
    (I : Type u) [Preorder I] [OrderBot I] [IsKappaFiltered κ (nerve I)]
    (P : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶
      sliceOver ((SSet.yonedaEquiv (X := sliceUnder q)).symm z))
    (c : JoinCocone P)
    (hc : IsColimitCone (mapJoinCocone
      (sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder q)).symm z) ≫
        sliceUnderProjection q) c)) :
    IsColimitCone (mapJoinCocone T c) := by
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
  change ((c.val ≫ T) ≫ sliceOverProjection _) ≫ sliceUnderProjection r =
    (c.val ≫ (sliceOverProjection _ ≫ sliceUnderProjection q)) ≫ f
  simp only [Category.assoc]
  rw [hT]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
