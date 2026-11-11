module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoconeSliceImageMap

/-!
概要：余錐の頂点で正規化した像を、元の任意の等しい点射上の slice へ全関手として戻す。
方針：両固定点の厳密同型と全 uncurry の単射性を使う。
規約：元の後合成と全図式の可換式を保持する。
使われ方：μ-small 全余錐の像を元の fiber の底上へ揃える。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：固定点移送は正規化した像と元の slice 後合成を全射として可換にする。
方針：全 uncurry で固定点の等号移送を除く。
規約：全関手の厳密な等式。
使われ方：元の fiber の全余錐比較。 -/
lemma coconeSliceImageMap_transport {K E B : SSet.{u}} {D : K ⟶ E}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (p : E ⟶ B) (a : (Δ[0] : SSet.{u}) ⟶ E)
    (ha : SSet.yonedaEquiv.symm c.vertex = a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceImageMap c p ≫
      eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceImagePoint_eq c p).symm.trans (congrArg (fun f ↦ f ≫ p) ha))) =
    eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ha) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a p := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective (a ≫ p)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverUncurry_eqToHom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceImagePoint_eq c p).symm.trans (congrArg (fun f ↦ f ≫ p) ha)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_postcomp]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverUncurry_eqToHom ha (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c.vertex)))
  simp only [Category.id_comp] at h
  rw [h]
  simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceImageMap_uncurry c p
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c.vertex)))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
