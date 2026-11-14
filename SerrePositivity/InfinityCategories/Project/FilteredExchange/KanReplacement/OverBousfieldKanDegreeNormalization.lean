module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightLiftNormalization
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightSimplexLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanDegreeSection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OverBousfieldKanDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：Over 圏の生成元の忘却と終点への持ち上げ直しは余極限で元に戻る。
方針：終点の構造射の余極限関係式と底の恒等成分の coend 関係式を使う。
規約：比較には filtered 性も Kan 性も不要。
使われ方：標準比較の各次数の単射性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]

/-- 概要：Over 圏の元の生成元と終点へ持ち上げ直した生成元は余極限で一致する。
方針：Over の構造射を余極限で消し、底の恒等成分の射を coend で消す。
規約：係数の単体は元のものを保つ。使われ方：次数ごとの他方の逆則。 -/
lemma overBousfieldKanDegreeLeg_normalization (F : I ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (i : I) (a : Over i) (x : (F.obj a.left).obj d)
    (σ : (nerve (Over (Opposite.op a))).obj d) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeLeg F d a.left (x, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightForgetSimplex σ) =
      (colimit.ι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) i).app d
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over i)ᵒᵖ) (Over.forget i ⋙ F) a).app d
          (x, σ)) := by
  let w := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightForgetSimplex σ
  let j := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightEndpoint w
  let b := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightBase w
  let f : j ⟶ i := (σ.obj 0).left.unop.hom
  let p := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift w ⋙ Over.post (Over.map f).op
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over i)ᵒᵖ
  let H := Over.forget i ⋙ F
  let z := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over j)ᵒᵖ)
    (Over.forget j ⋙ F) b).app d (x, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift w)
  have hc := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit (Over.forget j ⋙ F) ⟶
      colimit (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) ↦ t.app d z)
    (colimit.w (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) f)
  have hm := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanι_map F f b
  have hem := congrArg (fun t ↦ t.app d (x, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift w)) hm
  change (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanMap F f).app d z =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W H ((Over.map f).obj b)).app d (x, p) at hem
  have hn := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_condition W H (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightNormalizationBaseMap σ)
  have hen := congrArg (fun t ↦ t.app d (x, p)) hn
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W H a).app d
      (x, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift w ⋙ Over.post (Over.map f).op ⋙
        Over.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightNormalizationBaseMap σ).op) =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W H ((Over.map f).obj b)).app d
      ((F.map (𝟙 a.left)).app d x, p) at hen
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightSimplexLift_normalization, F.map_id] at hen
  calc
    _ = (colimit.ι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) i).app d
        ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanMap F f).app d z) := hc.symm
    _ = (colimit.ι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) i).app d
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W H ((Over.map f).obj b)).app d (x, p)) :=
      congrArg ((colimit.ι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) i).app d) hem
    _ = _ := congrArg ((colimit.ι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) i).app d) hen.symm

end SerrePositivity.InfinityCategories.Project.FilteredExchange
