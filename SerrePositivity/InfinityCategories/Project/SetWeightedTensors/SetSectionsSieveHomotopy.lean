module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsSieveNaturality
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsLimitNaturality

/-!
概要：評価錐の三角形を、全写像空間のホモトピー圏の等式として取り出す。
規約：G8 の切断比較との照合は別の課題であり、この等式だけでは②を主張しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors


/-- 評価から指定極限への二経路は、全写像空間を対象とするホモトピー圏で等しい。 -/
lemma sieveEvaluation_postcompose_homMk_eq
    {C : Type u} [SmallCategory C] {U : C} {E : SSet.{u + 1}} [Quasicategory E]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Cᵒᵖ) ⟶ E)
    (S : Sieve U) (M : E _⦋0⦌)
    (cS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram S.functor F)) (hcS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cS)
    (cU : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram (yoneda.obj U) F)) (hcU : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cU) :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1})
        (X := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom M
          (F.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U)))), inferInstance⟩)
        (Y := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom M cS.vertex, inferInstance⟩)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose M (Truncated.HomotopyCategory.homMk
            (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.representableEvaluationMap F cU hcU).toTruncated) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose M (Truncated.HomotopyCategory.homMk
            (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sieveSectionsMap S F cS hcS cU hcU).toTruncated) :
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom M (F.app (Opposite.op ⦋0⦌)
            (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U)))) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom M cS.vertex)).toTruncated =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1})
        (X := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom M
          (F.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U)))), inferInstance⟩)
        (Y := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom M cS.vertex, inferInstance⟩)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.postcompose M (Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sieveEvaluationMap F S cS hcS).toTruncated))).toTruncated :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_homMk_eq_of_functorIso
    (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.sieveEvaluation_postcomposeIso F S M cS hcS cU hcU)

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
