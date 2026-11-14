module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：Bousfield–Kan coend から通常の colimit への自然な比較射。
方針：反変 Bousfield–Kan 重みを忘れる coend の augmentation を使う。
規約：比較射自体には filtered 性や Kan 性を要求しない。
使われ方：通常の filtered colimit を空間の native な余極限へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]

/-- 概要：Bousfield–Kan coend から通常の colimit への標準射。
方針：選ばれた余極限余錐の脚を重みを忘れて降下させる。
規約：filtered 性は不要。使われ方：filtered な場合の弱同値の主経路。 -/
def bousfieldKanAugmentation (F : I ⥤ SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F ⟶ colimit F :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) (colimit.cocone F)

/-- 概要：標準比較は各重み付き脚で元の colimit の脚を回収する。
方針：一般の augmentation の脚の計算則。
規約：重みの変数は忘れる。使われ方：元の図式と比較射の整合。 -/
lemma bousfieldKanι_augmentation (F : I ⥤ SSet.{u}) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F i ≫ bousfieldKanAugmentation F =
      fst (F.obj i) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ).obj (Opposite.op i)) ≫ colimit.ι F i :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_augmentation _ _ _

/-- 概要：標準比較射は図式の自然変換に自然。
方針：通常の colimit の誘導射の脚の公式を使う。
規約：成分の同値性は不要。使われ方：置換図式との比較。 -/
lemma bousfieldKanAugmentation_naturality {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    bousfieldKanAugmentation F ≫ colim.map η =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) η ≫ bousfieldKanAugmentation G :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation_naturality _ η (colimit.cocone F) (colimit.cocone G)
    (colim.map η) (fun i ↦ colimit.ι_map η i)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
