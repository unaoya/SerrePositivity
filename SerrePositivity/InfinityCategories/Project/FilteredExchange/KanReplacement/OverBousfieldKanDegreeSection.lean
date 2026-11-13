module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightLiftForget
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightSimplexLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitDegree
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：Over 圏の coend の余極限との比較に対する次数ごとの逆の候補。
方針：重みの鎖をその終点に持ち上げ、余極限の脚を合成する。
規約：単体方向の自然性は各次数の全単射の証明には不要。
使われ方：標準比較の成分の全射性と単射性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]

/-- 概要：係数と重みの単体の組を終点の Over 圏の coend へ送る。
方針：持ち上げた鎖を重み付き脚に入れ、通常の余極限の脚へ送る。
規約：係数の単体は変更しない。使われ方：次数ごとの coend の降下。 -/
def overBousfieldKanDegreeLeg (F : I ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) (a : I)
    (s : (F.obj a ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ).obj (Opposite.op a)).obj d) :
    (colimit (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F)).obj d :=
  (colimit.ι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint s.2)).app d
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint s.2))ᵒᵖ)
      (Over.forget (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint s.2) ⋙ F) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightBase s.2)).app d
        (s.1, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift s.2))

/-- 概要：終点への持ち上げによる写像は係数・重みの dinaturality を保つ。
方針：終点の Over 圏の底の射に coend の関係式を適用する。
規約：終点は始点の変更で変わらない。使われ方：元の coend からの降下。 -/
lemma overBousfieldKanDegreeLeg_condition (F : I ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ)
    {a b : I} (f : a ⟶ b) (x : (F.obj a).obj d)
    (w : ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ).obj (Opposite.op b)).obj d) :
    overBousfieldKanDegreeLeg F d a (x, ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ).map f.op).app d w) =
      overBousfieldKanDegreeLeg F d b ((F.map f).app d x, w) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_condition
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint w))ᵒᵖ)
    (Over.forget (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint w) ⋙ F)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightLiftCoefficientMap f w)
  have he := congrArg (fun t ↦ t.app d (x, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift w)) h
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint w))ᵒᵖ
  let H := Over.forget (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint w) ⋙ F
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W H (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightBase (w ⋙ Over.map f.op))).app d
      (x, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift w ⋙
        Over.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightLiftCoefficientMap f w).op) =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W H (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightBase w)).app d
      ((F.map f).app d x, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift w) at he
  rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift_coefficient] at he
  exact congrArg ((colimit.ι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint w)).app d) he

/-- 概要：元の coend の各次数から Over 図式の余極限への写像。
方針：終点への持ち上げの dinaturality によって降下させる。
規約：単体集合の射とはまだ主張しない。使われ方：比較の各成分の逆。 -/
def overBousfieldKanDegreeSection (F : I ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F).obj d → (colimit (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F)).obj d :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitDegreeDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F d (overBousfieldKanDegreeLeg F d)
    (overBousfieldKanDegreeLeg_condition F d)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
