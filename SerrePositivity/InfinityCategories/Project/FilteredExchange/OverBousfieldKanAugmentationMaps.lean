module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.BousfieldKanTerminalContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.BousfieldKanTerminalStages
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedColimit

/-!
概要：各 Over 圏の終対象を用いた元の係数への augmentation。
方針：恒等射が Over 圏の終対象であることを用いる。
規約：元の図式の Kan 性は不要。
使われ方：filtered な coend 比較の各段の弱同値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]

/-- 概要：Over 圏の coend を元の終点の係数へ送る。
方針：恒等射の終対象性を terminal augmentation に渡す。
規約：標的は元の F.obj i。使われ方：元の図式への自然変換の成分。 -/
def overBousfieldKanAugmentationMap (F : I ⥤ SSet.{u}) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit (Over.forget i ⋙ F) ⟶ F.obj i :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalBousfieldKanAugmentation (Over.forget i ⋙ F) Over.mkIdTerminal

/-- 概要：各段の augmentation は元の係数の構造射を各脚で回収する。
方針：terminal augmentation の脚の式と Over の終対象への射を計算する。
規約：重みの変数は全て忘れる。使われ方：自然性の検証。 -/
lemma overBousfieldKanι_augmentationMap (F : I ⥤ SSet.{u}) (i : I) (a : Over i) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over i)ᵒᵖ) (Over.forget i ⋙ F) a ≫
      overBousfieldKanAugmentationMap F i =
        fst (F.obj a.left) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over i)ᵒᵖ).obj (Opposite.op a)) ≫ F.map a.hom := by
  rw [overBousfieldKanAugmentationMap, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalBousfieldKanAugmentation,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_augmentation]
  change _ ≫ F.map (Over.mkIdTerminal.from a).left = _ ≫ F.map a.hom
  rw [Over.mkIdTerminal_from_left]
  rfl

/-- 概要：各 Over 圏からの augmentation は弱ホモトピー同値。
方針：構成済みの terminal な添字の収縮を使う。
規約：図式の値の Kan 性は不要。使われ方：filtered 余極限へ送る各段の比較。 -/
lemma overBousfieldKanAugmentationMap_isWeakHomotopyEquivalence
    (F : I ⥤ SSet.{u}) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (overBousfieldKanAugmentationMap F i) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.terminalBousfieldKanAugmentation_isWeakHomotopyEquivalence _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
