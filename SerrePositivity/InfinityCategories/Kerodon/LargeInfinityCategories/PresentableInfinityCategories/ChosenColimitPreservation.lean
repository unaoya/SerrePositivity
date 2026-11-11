module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ChosenColimitComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ChosenColimitEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomUniversal

/-!
概要：元の指定余極限の保存は選んだ全余極限比較の可逆性に同値。
方針：全余錐比較を各図式で評価し、元の余極限余錐の一意性を使う。
規約：選んだ全比較自身について判定する。
使われ方：有限余積保存を Yoneda 生成対象で検査する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の形状の余極限を保てば指定した全余極限比較は可逆。
方針：全図式の点ごとの普遍余錐の像を使い、比較の成分を可逆とする。
規約：同じ全比較を使う。
使われ方：保存判定の必要条件。 -/
lemma chosenColimitComparison_isIso_of_preservation
    {K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (hY : ∀ p : K ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (q : X ⟶ Y)
    (h : ∀ (p : K ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q c)) : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitComparison hX hY q) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHom_isIso_of_components
  intro a
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitComparison_evaluate_isIso hX hY q a
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitImageCocone_evaluate_val hX (𝟙 ((ihom K).obj X)) q a)).mpr
  exact h _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_isPointwiseColimit hX (𝟙 ((ihom K).obj X)) a)

/-- 概要：指定した全比較が可逆なら元の形状の全余極限を保存する。
方針：全比較を指定図式で評価し、選んだ余錐から元の余錐へ同型で戻す。
規約：元の指定余錐の像を結論に保持する。
使われ方：生成対象での比較から有限余積保存へ戻す。 -/
lemma chosenColimit_preservation_of_comparison_isIso
    {K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (hY : ∀ p : K ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (q : X ⟶ Y)
    (h : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitComparison hX hY q))
    (p : K ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q c) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitImageCocone_evaluate_isColimit hX hY q (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitComparison hX hY q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))
  have hv : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitImageCocone hX (𝟙 ((ihom K).obj X)) q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCocone K X hX p)).val := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitImageCocone_evaluate_val]
    change (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hX (𝟙 ((ihom K).obj X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)).val ≫ q = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCocone K X hX p).val ≫ q
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_id_evaluate_val]
  have hj := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ hv).mp hi
  exact hj.of_vertexIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p q)).toFunctor.mapIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCocone K X hX p) c
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitCocone_isColimit K X hX p) hc))

/-- 概要：元の形状の全余極限保存は指定した全比較の可逆性に同値。
方針：二つの構成済みの方向を組み合わせる。
規約：選んだ全比較を固定する。
使われ方：有限余積の全比較による公開判定。 -/
lemma chosenColimitComparison_isIso_iff_preservation
    {K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (hY : ∀ p : K ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (q : X ⟶ Y) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitComparison hX hY q) ↔
      ∀ (p : K ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c →
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q c) :=
  ⟨chosenColimit_preservation_of_comparison_isIso hX hY q,
    chosenColimitComparison_isIso_of_preservation hX hY q⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
