module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalFilteredKanCones
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FilteredKanCocone

/-!
概要：filtered な strict Kan 図式族の同じ通常の余極限余錐を、全成分の native な余極限として保持する。
方針：元の関手圏の余極限の脚を Kan 対象に束縛し、評価による保存と既存の filtered 判定を使う。
規約：頂点と全脚は元の strict SSet 余極限。各成分で別の模型を選ばない。
使われ方：共同 strict 模型の余極限を元の点ごとの余極限へ同定する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {I J : Type u} [SmallCategory I] [SmallCategory J] [IsFiltered J]
  (F : J ⥤ I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})

/-- 元の strict な関手圏の余極限の全脚を、そのまま Kan 対象の脚に束縛する。 -/
def kanFamilyColimitCocone : Cocone F where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredKanDiagram F
  ι := {
    app j := {
      app i := (colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanConeFamilyUnderlying F) j).app i
      naturality i k f := (colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanConeFamilyUnderlying F) j).naturality f }
    naturality j k f := by
      apply NatTrans.ext
      funext i
      exact NatTrans.congr_app (colimit.w (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanConeFamilyUnderlying F) f) i }

/-- 同じ余錐を各対象で評価し忘却すると、元の評価余極限余錐の普遍性を回収する。 -/
def kanFamilyColimitCocone_evaluation_isColimit (i : I) :
    IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone
      (((evaluation I _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj i).mapCocone (kanFamilyColimitCocone F))) :=
  isColimitOfPreserves ((evaluation I SSet.{u}).obj i)
    (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanConeFamilyUnderlying F))

/-- 各評価の同じ native 余錐は、元の Kan 値図式の実際の ∞ 余極限余錐である。 -/
lemma kanFamilyColimitCocone_evaluation_native (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone
      (((evaluation I _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj i).mapCocone (kanFamilyColimitCocone F))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictNativeCocone_isColimit_of_filtered_forget _
    (kanFamilyColimitCocone_evaluation_isColimit F i)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
