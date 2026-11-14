module

public import SerrePositivity.EInfinity.FrameHom.TerminalFiberBaseHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.NerveCoconePrism
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyNaturality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.OverCanonicalCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeFamilyUnderlying

/-!
# 元の Over 図式から恒等射への標準全ホモトピー

概要：元の Over 図式を恒等射へ送る唯一の自然変換と実円柱を保持する。
方針：Over の標準終対象から自然変換を作り、忘却像を元の余錐と同定する。
規約：全単体・元の構造射を保つ。
使われ方：実評価の底円柱と標準評価の全関手圏での比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory Limits Opposite SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (n : C) (T : I ⥤ Over n)

def overTerminalTransformation : T ⟶ (Functor.const I).obj (Over.mk (𝟙 n)) where
  app s := Over.mkIdTerminal.from (T.obj s)
  naturality {_ _} _ := Over.mkIdTerminal.hom_ext _ _

def overTerminalHomotopy : SSet.Homotopy (nerveMap T)
    (SSet.const (X := nerve I) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Over.mk (𝟙 n)))) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (overTerminalTransformation n T))
    rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveMap_const I (Over.mk (𝟙 n)))

lemma overTerminalTransformation_forget :
    Functor.whiskerRight (overTerminalTransformation n T) (Over.forget n) =
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.overForgetCocone n).whisker T).ι := by
  apply NatTrans.ext
  funext s
  exact Over.mkIdTerminal_from_left (T.obj s)

lemma overTerminalHomotopy_forget_h : (overTerminalHomotopy n T).h ≫
    nerveMap (Over.forget n) =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.overForgetCocone n).whisker T).ι).h := by
  change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (overTerminalTransformation n T)).h ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_whiskerRight, overTerminalTransformation_forget]

lemma overTerminalHomotopy_map_forget_h {D : Type u} [Category.{u} D] (G : C ⥤ D) :
    (overTerminalHomotopy n T).h ≫ nerveMap (Over.forget n) ≫ nerveMap G =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy
        (G.mapCocone ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.overForgetCocone n).whisker T)).ι).h := by
  rw [← Category.assoc, overTerminalHomotopy_forget_h]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveCoconePrism_eq_natTrans (T ⋙ Over.forget n)
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.overForgetCocone n).whisker T),
    ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveCoconePrism_eq_natTrans ((T ⋙ Over.forget n) ⋙ G)
      (G.mapCocone ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.overForgetCocone n).whisker T))]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCocone_mapCocone]

end SerrePositivity.EInfinity.FrameHom
