module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowInterpolationCoherentCocone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EquivalenceDescent

/-!
概要：補間した全 C 図式を、元の小さい区間と小さい C の関手族へ降ろす。
方針：区間と全内部 Hom の宇宙同型で表示を揃え、全射を降下する。
規約：元の全次数の図式を厳密に回収。使われ方：元の図式 comma への帰還。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D}
  (V : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowInterpolationData κ D q)

/-- 元の区間の宇宙持ち上げで表示した、同じ全 C 図式。 -/
def indArrowInterpolationLiftedDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}))).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationCoherentDiagram V ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1).hom).app _

/-- 小さい元の区間と C に値を取る、実際の全 coherent 関手族。 -/
def indArrowInterpolationSmallDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶
    (ihom (Δ[1] : SSet.{u})).obj C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (indArrowInterpolationLiftedDiagram V ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).inv)

/-- 降ろした同じ全図式の持ち上げは、元の大きい全 C 図式を厳密に回収。 -/
lemma indArrowInterpolationSmallDiagram_lift :
    (SSet.uliftFunctor.{u + 1, u}).map (indArrowInterpolationSmallDiagram V) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).hom =
        indArrowInterpolationLiftedDiagram V := by
  rw [indArrowInterpolationSmallDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 元の図式 Yoneda の作用も、同じ補間 C 図式の像そのものになる。 -/
lemma indArrowInterpolationSmallDiagram_yoneda :
    (SSet.uliftFunctor.{u + 1, u}).map (indArrowInterpolationSmallDiagram V) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda κ (Δ[1] : SSet.{u}) C =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationCoherentDiagram V ≫
          (ihom (Δ[1] : SSet.{u + 1})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) ≫
            (pre (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1).hom).app
              (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda, ← Category.assoc, indArrowInterpolationSmallDiagram_lift,
    indArrowInterpolationLiftedDiagram, Category.assoc,
    (pre (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1).hom).naturality]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
