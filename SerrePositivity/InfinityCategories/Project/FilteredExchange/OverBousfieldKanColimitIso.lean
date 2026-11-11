module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.BousfieldKanReindex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.BousfieldKanWeightLiftNormalization
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.OverBousfieldKanCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.OverBousfieldKanComparisonSurjective
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.OverBousfieldKanDegreeNormalization
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.OverBousfieldKanDegreeSection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.OverBousfieldKanDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitDegree
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitDegreeExt
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanColimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedColimit

/-!
概要：Over 圏の Bousfield–Kan coend の余極限は元の coend に同型。
方針：鎖の終点への持ち上げで標準比較の各次数の両逆を検証する。
規約：全ての通常の小圏の図式に適用し、filtered 性は不要。
使われ方：通常の filtered augmentation の弱同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]

/-- 概要：各段の忘却比較の後の次数ごとの持ち上げは元の余極限の脚。
方針：各段の coend の全生成元に正規化の等式を使う。
規約：係数の全ての単体を含む。使われ方：他方の逆則。 -/
lemma overBousfieldKanDegreeSection_reindex (F : I ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (i : I) (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit (Over.forget i ⋙ F)).obj d) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeSection F d ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex F (Over.forget i)).app d z) =
      (colimit.ι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) i).app d z := by
  have he : (fun z ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeSection F d
      ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex F (Over.forget i)).app d z)) =
        fun z ↦ (colimit.ι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) i).app d z := by
    apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitDegree_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over i)ᵒᵖ)
      (Over.forget i ⋙ F) d
    intro a s
    obtain ⟨x, σ⟩ := s
    have h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanι_reindex F (Over.forget i) a
    have hσ := congrArg (fun t ↦ t.app d (x, σ)) h
    change (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanReindex F (Over.forget i)).app d
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (Over i)ᵒᵖ) (Over.forget i ⋙ F) a).app d
        (x, σ)) =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight Iᵒᵖ) F a.left).app d
        (x, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.bousfieldKanWeightForgetSimplex σ) at hσ
    rw [hσ, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeSection, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitDegreeDesc_ι]
    exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeLeg_normalization F d i a x σ
  exact congrFun he z

/-- 概要：次数ごとの持ち上げは標準比較の左逆。
方針：余極限の各脚で忘却比較の正規化を使う。
規約：全ての通常の小圏の図式。使われ方：比較の単射性。 -/
lemma overBousfieldKanDegreeSection_leftInverse (F : I ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) : Function.LeftInverse (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeSection F d)
      ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F).app d) := by
  have h : (fun z ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDegreeSection F d
      ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F).app d z)) = id := by
    apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.colimitDegree_hom_ext (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) d
    intro i z
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison_ι_app]
    exact overBousfieldKanDegreeSection_reindex F d i z
  exact congrFun h

/-- 概要：Over 圏の coend の余極限との標準比較は同型。
方針：各次数の具体的な両逆から成分の同型性を得る。
規約：filtered 性も Kan 性も不要。使われ方：標準 augmentation の因子分解。 -/
instance overBousfieldKanColimitComparison_isIso (F : I ⥤ SSet.{u}) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F) := by
  have (d : SimplexCategoryᵒᵖ) : IsIso ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F).app d) :=
    (isIso_iff_bijective _).2
      ⟨(overBousfieldKanDegreeSection_leftInverse F d).injective,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison_surjective F d⟩
  exact NatIso.isIso_of_isIso_app _

/-- 概要：元の coend を各 Over 圏の coend の通常の余極限として表示する同型。
方針：全単射を証明した標準比較を同型として束ねる。
規約：同型の順方向は元の忘却比較。使われ方：filtered 表示の公開界面。 -/
def overBousfieldKanColimitIso (F : I ⥤ SSet.{u}) :
    colimit (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanDiagram F) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanColimit F :=
  asIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.overBousfieldKanColimitComparison F)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
