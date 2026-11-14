module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UniverseRightKanCanonical
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanOppositeCanonicalLimits
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.CoYonedaConeLimits

/-!
概要：元の左 Kan 標準余錐の普遍性から、任意の全係数制限の Hom 族の右 Kan 条件を得る。
方針：元の反転標準錐を共同 Hom で写し、元の係数の全評価で極限性を判定する。
規約：全係数を持つ元の関手圏値の族と、持ち上げた元の反対射を保持する。
使われ方：大きい係数前層への全自然変換空間族の右 Kan 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の全標準余錐の普遍性は、任意の全係数制限を持つ元の Hom 族の右 Kan 条件を与える。 -/
lemma homCanonical_isRightKanExtension {K C D : SSet.{u}} [Quasicategory D]
    {A : SSet.{u + 1}} (δ : K ⟶ C) (F : C ⟶ D)
    (f : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj D)
    (h : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map δ))
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map δ) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap D ≫ (pre f).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})))
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap D ≫ (pre f).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map δ) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap D ≫ (pre f).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanExtension_refl_post_ulift_of_canonicalLimits
  intro c
  have hc := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanCanonicalCone_op_isLimit δ F (SSet.opObjEquiv c) (h (SSet.opObjEquiv c))
  have he : SSet.opObjEquiv.symm (SSet.opObjEquiv c) = c := Equiv.symm_apply_apply _ c
  rw [he] at hc
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_pointwise
  intro a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap D ≫ (pre f).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map F) c)))
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up ((f.app (Opposite.op ⦋0⦌) a).down)))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map F) c)))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coyonedaInfinityMap_evaluation]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity_isLimit _ hc _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
