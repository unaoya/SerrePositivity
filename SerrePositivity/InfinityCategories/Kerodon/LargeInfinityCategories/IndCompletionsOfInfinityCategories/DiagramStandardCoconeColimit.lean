module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowStandardCoconeColimit

/-!
概要：各頂点評価の共終性から、元の全図式の標準余錐の余極限性を回収する。
方針：同じ scalar 密度余錐を制限し、関手圏の点ごとの判定を使う。
規約：任意の形状で共終性を仮定として明示し、有限性だけからは結論しない。
使われ方：有限半順序形状の帰納を単一表示の普遍性へ接続する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)

/-- 概要：元の指定点評価が共終なら、同じ評価余錐は余極限。
方針：scalar 密度の制限。規約：全射を保持。使われ方：全図式の普遍性。 -/
lemma smallDiagramCommaCocone_evaluate_isColimit_of_cofinal (k : K _⦋0⦌)
    (hk : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaEvaluation κ D k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up k)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaCocone κ D)) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C))
    (D.app (Opposite.op ⦋0⦌) (ULift.up k))
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaEvaluation κ D k)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaEvaluation κ D k) hk c).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYonedaCanonicalCocone_isColimit κ _)
  have hval : (c.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaEvaluation κ D k)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up k))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaCocone κ D)).val := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaEvaluation_coconeMap κ D k
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ hval).mp hc

/-- 概要：全頂点評価が共終なら、元の標準全余錐は余極限。
方針：各点の普遍性。規約：元の余錐と頂点を保持。使われ方：有限形状の帰納。 -/
lemma smallDiagramCommaCocone_isColimit_of_evaluation_cofinal
    (h : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaEvaluation κ D k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.smallDiagramCommaCocone κ D) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.isColimitCone_functor_of_pointwise
  rintro ⟨k⟩
  exact smallDiagramCommaCocone_evaluate_isColimit_of_cofinal κ D k (h k)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
