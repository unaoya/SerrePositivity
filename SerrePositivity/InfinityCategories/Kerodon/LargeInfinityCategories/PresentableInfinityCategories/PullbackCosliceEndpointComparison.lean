module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCosliceBaseChange

/-!
概要：底変換した全余錐の第一脚を相対 coslice の射の底変換として表す。
方針：可変頂点の第一成分と共通標的の余錐を相対 coslice の底へ合わせる。
規約：固定図式の始域は任意。元の第一関手には inner fibration 性だけを要求する。
使われ方：全共変 Hom の引き戻し cospan の一脚 left fibration 条件。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {E D B K : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B) (a : K ⟶ pullback p q)

/-- 概要：共通標的の余錐と元の可変頂点の第一成分を合わせる。
方針：元の底変換の可換条件を相対 coslice の底の可換条件として使う。
規約：可変頂点と余錐を全次数で保持する。
使われ方：相対 coslice の射を底変換する射。 -/
def pullbackCosliceEndpointBase : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceBase p q a ⟶
    pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((a ≫ pullback.fst p q) ≫ p)) :=
  pullback.lift (pullback.snd _ _ ≫ pullback.fst p q) (pullback.fst _ _) (by
    rw [Category.assoc, ← pullback.condition])

/-- 概要：底変換された第一脚と相対 coslice の射の正方形は可換。
方針：可変頂点と共通標的の余錐を両射影で比較する。
規約：元の固定図式を保持する。
使われ方：相対 coslice の底変換の引き戻し判定。 -/
lemma pullbackCosliceEndpoint_condition :
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ pullback.fst p q)) (pullback.fst p q) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap (a ≫ pullback.fst p q) p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceLeftMap p q a ≫ pullbackCosliceEndpointBase p q a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_fst, pullbackCosliceEndpointBase,
      pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceLeftMap, pullback.lift_snd_assoc]
    exact pullback.condition
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_snd, pullbackCosliceEndpointBase,
      pullback.lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceLeftMap, pullback.lift_fst]

/-- 概要：相対 coslice の底上で可換な二族は底変換された第一余錐族へ貼れる。
方針：全余錐と元の可変頂点を元の引き戻しへ持ち上げる。
規約：任意のパラメーターを許す。
使われ方：相対 coslice の底変換の普遍射。 -/
def pullbackCosliceEndpointLift {T : SSet.{u}}
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ pullback.fst p q)) (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceBase p q a)
    (h : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap (a ≫ pullback.fst p q) p =
      g ≫ pullbackCosliceEndpointBase p q a) : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceLeft p q a :=
  pullback.lift f (g ≫ pullback.snd _ _) (by
    have hh := congrArg (fun r : T ⟶ pullback p
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((a ≫ pullback.fst p q) ≫ p)) ↦ r ≫ pullback.fst _ _) h
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_fst, pullbackCosliceEndpointBase,
      pullback.lift_fst] using hh)

/-- 概要：相対 coslice の底変換の正方形は引き戻し。
方針：元の全余錐と共通標的の余錐を両射影で回収し、元の引き戻しで一意性を示す。
規約：充填性を仮定しない厳密な全単体の普遍性。
使われ方：第一脚への left fibration 性の移送。 -/
lemma pullbackCosliceEndpoint_isPullback : IsPullback
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ pullback.fst p q)) (pullback.fst p q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceLeftMap p q a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap (a ≫ pullback.fst p q) p)
    (pullbackCosliceEndpointBase p q a) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ (pullbackCosliceEndpoint_condition p q a))
  refine PullbackCone.IsLimit.mk _
    (fun s ↦ pullbackCosliceEndpointLift p q a s.fst s.snd s.condition) ?_ ?_ ?_
  · intro s
    exact pullback.lift_fst _ _ _
  · intro s
    apply pullback.hom_ext
    · have hh := congrArg (fun r : s.pt ⟶ pullback p
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((a ≫ pullback.fst p q) ≫ p)) ↦ r ≫ pullback.snd _ _) s.condition
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap_snd, pullbackCosliceEndpointBase,
        pullbackCosliceEndpointLift, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceLeftMap, pullback.lift_fst,
        pullback.lift_fst_assoc, pullback.lift_snd] using hh
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceLeftMap, pullback.lift_snd,
        pullbackCosliceEndpointLift]
  · intro s m hm₁ hm₂
    apply pullback.hom_ext
    · simpa only [pullbackCosliceEndpointLift, pullback.lift_fst] using hm₁
    · have hh := congrArg (fun r : s.pt ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceBase p q a ↦ r ≫ pullback.snd _ _) hm₂
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceLeftMap, pullback.lift_snd,
        pullbackCosliceEndpointLift, pullback.lift_snd_assoc] using hh

/-- 概要：元の第一関手が inner fibration なら、全余錐 cospan の第一脚は left fibration。
方針：相対 coslice の left fibration 性を構成した底変換へ移す。
規約：標的や固定図式への追加の充填性を要求しない。
使われ方：全共変 Hom の引き戻しの極限判定。 -/
lemma pullbackCosliceLeftMap_leftFibration [InnerFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceLeftMap p q a) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.of_isPullback (pullbackCosliceEndpoint_isPullback p q a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEndpointMap (a ≫ pullback.fst p q) p))⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
