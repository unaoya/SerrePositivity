module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanReindex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightLiftForget
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightSimplexLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.OverBousfieldKanCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanDegreeSection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitDegree
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitDegreeExt
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：Over 図式の余極限から元の coend への標準比較は各次数で全射。
方針：終点への持ち上げから作った次数ごとの写像との一方の逆則を示す。
規約：全射性だけでは同型性や弱同値性を主張しない。
使われ方：標準比較の全単射と表示同型の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]

/-- 概要：標準比較は余極限の脚で忘却関手の添字変更に一致する。
方針：通常の余極限の降下の式を評価する。
規約：任意の次数と単体。使われ方：生成元上での逆則。 -/
lemma overBousfieldKanColimitComparison_ι_app (F : I ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (i : I) (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit (Over.forget i ⋙ F)).obj d) :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F).app d
      ((colimit.ι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) i).app d z) =
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex F (Over.forget i)).app d z := by
  have h := colimit.ι_desc (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanCocone F) i
  exact congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F).obj i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F ↦
    t.app d z) h

/-- 概要：終点への持ち上げによる生成元は標準比較で元の生成元に戻る。
方針：添字変更の脚の式と持ち上げの忘却則を使う。
規約：係数の単体もそのまま戻る。使われ方：一方の逆則。 -/
lemma overBousfieldKanDegreeLeg_comparison (F : I ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ)
    (a : I) (s : (F.obj a ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ).obj (Opposite.op a)).obj d) :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F).app d (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeLeg F d a s) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F a).app d s := by
  obtain ⟨x, w⟩ := s
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeLeg, overBousfieldKanColimitComparison_ι_app]
  have h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanι_reindex F (Over.forget (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint w))
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightBase w)
  have he := congrArg (fun t : F.obj a ⊗
      nerve (Over (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightBase w))) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F ↦
    t.app d (x, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift w)) h
  change _ = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F a).app d
    (x, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift w ⋙
      Over.post (Over.forget (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint w)).op) at he
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift_forget] at he
  exact he

/-- 概要：次数ごとの持ち上げは標準比較の右逆。
方針：coend の全ての生成元で計算する。
規約：添字の filtered 性は不要。使われ方：比較の全射性。 -/
lemma overBousfieldKanDegreeSection_rightInverse (F : I ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) : Function.RightInverse (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeSection F d)
      ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F).app d) := by
  have h : (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F).app d
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeSection F d z)) = id := by
    apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitDegree_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F d
    intro a s
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeSection, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitDegreeDesc_ι]
    exact overBousfieldKanDegreeLeg_comparison F d a s
  exact congrFun h

/-- 概要：標準比較は各次数で全射。
方針：具体的な次数ごとの右逆を使う。
規約：単射性は別に検証する。使われ方：表示同型の証明。 -/
lemma overBousfieldKanColimitComparison_surjective (F : I ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) : Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F).app d) :=
  (overBousfieldKanDegreeSection_rightInverse F d).surjective

end SerrePositivity.InfinityCategories.Project.FilteredExchange
