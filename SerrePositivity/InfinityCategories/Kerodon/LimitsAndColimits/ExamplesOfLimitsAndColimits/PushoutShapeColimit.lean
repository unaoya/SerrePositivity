module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CommonColimitAttachment
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSpanCoconeGlue

/-!
概要：単射側のある形状 pushout の余極限を、部分余極限と span から構成する。
方針：共通の部分余極限と両部分の余極限を付加し、三頂点 span へ縮約する。
規約：任意の quasicategory に対し、元の全図式の余極限存在を結論する。
使われ方：全有限形状についての有限セル帰納の貼り合わせ段階。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-- 部分図式と三頂点 span の余極限から、pushout 形状の余極限を構成する。 -/
lemma hasColimit_pushout_shape_of_pointSpan {A B C X : SSet.{u}} [Quasicategory X]
    (f : A ⟶ B) (g : A ⟶ C) [Mono g] (F : pushout f g ⟶ X)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (f ≫ (pushout.inl f g ≫ F)))
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (pushout.inl f g ≫ F))
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (pushout.inr f g ≫ F))
    (hspan : ∀ s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpan.{u} ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit s) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F := by
  obtain ⟨a, ha⟩ := hA
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u})
  let GB := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram a f (pushout.inl f g ≫ F) rfl
  have hg : g ≫ (pushout.inr f g ≫ F) = f ≫ (pushout.inl f g ≫ F) := by
    exact (pushout.condition_assoc F).symm
  let GC := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram a g (pushout.inr f g ≫ F) hg
  obtain ⟨b, hb⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasColimit_commonColimitDiagram_iff a f _ rfl ha).mpr hB
  obtain ⟨c, hc⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasColimit_commonColimitDiagram_iff a g _ hg ha).mpr hC
  let i := pushout.inr f k
  let j := pushout.inr g k
  have he : i ≫ GB = j ≫ GC := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram_cone a f _ rfl).trans
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
  have hj : Mono j := Adhesive.mono_of_isPushout_of_mono_left
    (IsPushout.of_hasPushout g k)
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit G := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.hasColimit_coneSpanBase_of_pointSpan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0]) i j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.rightConeTip_rightAnodyne A) H
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanCoconeGlue_left_isColimit i j b c he hb)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSpanCoconeGlue_right_isColimit i j b c he hc)
    exact hspan _
  have hcone : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.inclusion f g k ≫ G = a.val := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.inclusion, Category.assoc]
    exact (congrArg (pushout.inr f k ≫ ·) hleft).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram_cone a f _ rfl)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceRestriction_trivialKanFibration_of_colimit_attachment a ha
    (f ≫ pushout.inl f g) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.inclusion f g k)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.map f g k) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.isPushout f g k) G hcone
  have hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.map f g k ≫ G = F := by
    apply pushout.hom_ext
    · simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.map, pushout.inl_desc_assoc,
        Category.assoc]
      exact (congrArg (pushout.inl f k ≫ ·) hleft).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram_base a f _ rfl)
    · simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.map, pushout.inr_desc_assoc,
        Category.assoc]
      exact (congrArg (pushout.inl g k ≫ ·) hright).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.commonColimitDiagram_base a g _ hg)
  have hf := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_trivialRestriction G
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCommonExtension.map f g k)).mp hG
  rwa [hd] at hf

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
