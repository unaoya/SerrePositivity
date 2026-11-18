module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscretePushoutCocones
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscreteAnodyneExtensions
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeComparisonCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanComparison

/-!
概要：集合値の任意小極限錐は、同じ離散空間値図式の極限錐を与える。
方針：定値単体集合の通常の極限保存と、一意な anodyne 延長を既存の全 Hom 判定へ渡す。
HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB）の離散係数への特殊化。
規約：形状の離散性は要求しない。元の通常の錐の全脚・全単体を保持する。
使われ方：離散前層と集合値層の元の層条件の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 元の集合値の錐を、同じ離散空間値図式の全錐として表示する。
頂点とすべての脚は元の通常の錐からそのまま送る。 -/
def discreteSpaceCone {I : Type u} [SmallCategory I] {F : I ⥤ Type u} (c : Cone F) :
    JoinCone (kanDiagramCoherentNerve (F ⋙ setsToKan)) :=
  (strictCoherentCone (setsToKan.mapCone c)).cast (strictCoherentDiagram_eq_kanDiagram _)

/-- 任意の小さい通常の形状の集合値極限は、同じ図式の離散空間値極限。
HTT 4.2.4.1 の双対。Kan 性と全 Hom 比較は既存の判定から導出する。 -/
@[cite HTT "4.2.4.1" (partial := special)
  "任意小さい通常の添字と離散空間値の通常の極限錐に特殊化した双対の比較。"]
lemma discreteSpaceCone_isLimit {I : Type u} [SmallCategory I] {F : I ⥤ Type u}
    (c : Cone F) (hc : IsLimit c) : IsLimitCone (discreteSpaceCone c) := by
  have hu : IsLimit (kanObjectForget.mapCone (setsToKan.mapCone c)) := by
    change IsLimit ((Functor.const SimplexCategoryᵒᵖ).mapCone c)
    exact isLimitOfPreserves _ hc
  have hh := bousfieldKanConeComparison_homotopyEquivalence_of_extensions
    (kanObjectForget.mapCone (setsToKan.mapCone c)) hu (by
      intro A B j hj a
      exact discreteDiagram_anodyne_extensions F j hj a)
  have hl := kanCone_isLimit_of_bousfieldKanComparison (setsToKan.mapCone c)
    hh.isWeakHomotopyEquivalence
  exact hl.cast (strictCoherentDiagram_eq_kanDiagram _)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
