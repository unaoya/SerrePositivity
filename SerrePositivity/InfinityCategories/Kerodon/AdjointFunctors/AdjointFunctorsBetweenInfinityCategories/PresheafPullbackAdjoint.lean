module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PresheafPullbackRestriction

/-!
概要：小圏上の前層の通常の引き戻し関手は右随伴を持つ。
方針：slice の前層表示では制限関手となり、通常の右 Kan 拡張がその右随伴。
規約：小圏と前層の値を同じ宇宙に取る。∞ 圏の Kan 拡張は使用しない。
使われ方：単体集合の引き戻しの右随伴の存在を圏同値で移送する。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：小圏上の Type u 値前層の通常の引き戻し関手は左随伴。
方針：slice の同値を合成し、制限関手の右 Kan 拡張随伴から移す。
規約：底の射 p に fibration 性は要求しない。
使われ方：left fibration に沿う right anodyne 性の保存の一般圏論的な仮定を解消する。 -/
lemma cofinalPresheafPullback_isLeftAdjoint {C : Type u} [SmallCategory C]
    {E B : Cᵒᵖ ⥤ Type u} (p : E ⟶ B) : (Over.pullback p).IsLeftAdjoint := by
  let F : (CostructuredArrow yoneda E)ᵒᵖ ⥤ (CostructuredArrow yoneda B)ᵒᵖ :=
    (CostructuredArrow.map p).op
  have : ((Functor.whiskeringLeft _ _ (Type u)).obj F).IsLeftAdjoint :=
    (F.ranAdjunction (Type u)).isLeftAdjoint
  have : ((overEquivPresheafCostructuredArrow B).functor ⋙
      (Functor.whiskeringLeft _ _ (Type u)).obj F).IsLeftAdjoint := inferInstance
  have : (Over.pullback p ⋙ (overEquivPresheafCostructuredArrow E).functor).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.cofinalPresheafPullbackRestrictionIso p).symm
  exact (Functor.isLeftAdjoint_comp_iff_left (Over.pullback p)
    (overEquivPresheafCostructuredArrow E).functor).mp inferInstance

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
