module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PreservedCoconeGluing
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.PushoutCommonExtension

/-!
概要：部分図式と点 span の余極限保存から、元の形状 pushout の余極限保存を導く。
方針：保存された共通部分を両側に付加し、指定全余錐を貼って点 span へ制限する。
規約：元の全図式・元の関手・各指定余錐の像を同時に保持する。
使われ方：I-2 d′ の交換述語を全有限形状へ延長する帰納段階。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-- 単射側を持つ形状 pushout 上で、同じ全余極限を保存する余錐が存在する。 -/
lemma hasPreservedColimit_pushout_shape {A B C X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (f : A ⟶ B) (g : A ⟶ C) [Mono g] (F : pushout f g ⟶ X)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U (f ≫ (pushout.inl f g ≫ F)))
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U (pushout.inl f g ≫ F))
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U (pushout.inr f g ≫ F))
    (hs : ∀ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpan.{u} ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U F := by
  obtain ⟨a, ha, hUa⟩ := hA
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u})
  let GB := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram a f (pushout.inl f g ≫ F) rfl
  have hg : g ≫ (pushout.inr f g ≫ F) = f ≫ (pushout.inl f g ≫ F) :=
    (pushout.condition_assoc F).symm
  let GC := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram a g (pushout.inr f g ≫ F) hg
  obtain ⟨b, hb, hUb⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_commonDiagram_iff U a ha hUa f _ rfl).mpr hB
  obtain ⟨c, hc, hUc⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_commonDiagram_iff U a ha hUa g _ hg).mpr hC
  let i := pushout.inr f k
  let j := pushout.inr g k
  have he : i ≫ GB = j ≫ GC :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram_cone a f _ rfl).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram_cone a g _ hg).symm
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanCoconeGlue i j b c he
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanBaseMap i j ≫ H
  have hleft : pushout.inl i j ≫ G = GB := by
    dsimp only [G]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanBaseMap_left, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanCoconeGlue_left, b.property]
  have hright : pushout.inr i j ≫ G = GC := by
    dsimp only [G]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanBaseMap_right, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanCoconeGlue_right, c.property]
  have : Mono j := Adhesive.mono_of_isPushout_of_mono_left
    (IsPushout.of_hasPushout g k)
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U G :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_coneSpanBase_of_pointSpan U (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0]) i j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightConeTip_rightAnodyne A) H
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanCoconeGlue_left_isColimit i j b c he hb)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanCoconeGlue_right_isColimit i j b c he hc)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSpanCoconeGlue_left_map_isColimit U i j b c he hUb)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSpanCoconeGlue_right_map_isColimit U i j b c he hUc) (hs _)
  have hcone : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.inclusion f g k ≫ G = a.val := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.inclusion, Category.assoc]
    exact (congrArg (pushout.inr f k ≫ ·) hleft).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram_cone a f _ rfl)
  have hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.map f g k ≫ G = F := by
    apply pushout.hom_ext
    · simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.map, pushout.inl_desc_assoc, Category.assoc]
      exact (congrArg (pushout.inl f k ≫ ·) hleft).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram_base a f _ rfl)
    · simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.map, pushout.inr_desc_assoc, Category.assoc]
      exact (congrArg (pushout.inl g k ≫ ·) hright).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram_base a g _ hg)
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_iff_colimit_attachment U a ha hUa
    (f ≫ pushout.inl f g) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.inclusion f g k)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.map f g k) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.isPushout f g k) G hcone).mp hG
  rwa [hd] at h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
