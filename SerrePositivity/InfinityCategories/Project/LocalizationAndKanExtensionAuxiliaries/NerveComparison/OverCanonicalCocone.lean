module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.OverLeg
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeNaturality

/-!
概要：Over の nerve の slice 比較と通常の標準余錐を同定する。
方針：両境界と構造射の脚を照合して高次の射の一致を得る。
規約：同じ宇宙の小さい圏の元の指定終点を保持する。
使われ方：B5 の指定単位の左 Kan 局所余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {C : Type u} [Category.{u} C] (c : C)

/-- 概要：Over の忘却関手上の標準余錐は元の終点を頂点に持つ。
方針：join の両境界と全ての混合辺を照合する。
規約：元の指定対象と Over の構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の古典比較。 -/
def overForgetCocone : Cocone (Over.forget c) where
  pt := c
  ι :=
    { app := fun x ↦ x.hom
      naturality := fun x y f ↦ by
        change f.left ≫ y.hom = x.hom ≫ 𝟙 c
        rw [Category.comp_id]
        exact Over.w f }

/-- 概要：Over の nerve の uncurry は通常の標準余錐の nerve と一致する。
方針：join の両境界と全ての混合辺を照合する。
規約：元の指定対象と Over の構造射を保持する。
使われ方：B5 の左 Kan の標準余錐の古典比較。 -/
lemma nerveOverIso_uncurry : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (overForgetCocone c)).val := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerve_joinTerminal_hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (overForgetCocone c)).property,
      _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso_projection]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_point]
    rfl
  · intro x
    change ((_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso c).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)).val.app
      (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOverIso_leg, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_leg]
    rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
