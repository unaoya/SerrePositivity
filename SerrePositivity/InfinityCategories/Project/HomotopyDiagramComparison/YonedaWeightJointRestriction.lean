module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomWeightEvaluationFamily
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomotopyLimitsPresentableSigmaHomWeightRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafUniverseFamilyEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaEvaluationJoint

/-!
概要：全 Yoneda 評価の共同図式を、元の Hom 係数へ制限し、比較すべき両族へ同定する。
方針：同じ両変数の底写像と元の共同評価の展開公式を使う。
規約：両族の全写像が元の全共同図式の制限そのものであることを示す。
使われ方：大域 Yoneda 評価の比較から両右 Kan 族の制限比較への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の C と全標的係数から、同じ全 Yoneda 評価の共同底への指定写像。 -/
def yonedaWeightJointRestriction (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj ((SSet.uliftFunctor.{u + 1, u}).obj C)).op ⊗
      (SSet.uliftFunctor.{u + 3, u + 2}).obj ((SSet.uliftFunctor.{u + 2, u + 1}).obj D) ⟶
      (SSet.uliftFunctor.{u + 3, u + 2}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.YonedaEvaluationJointBase ((SSet.uliftFunctor.{u + 1, u}).obj C)) :=
  ((SSet.uliftFunctor.{u + 3, u + 2}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u + 1, u + 2} ((SSet.uliftFunctor.{u + 1, u}).obj C)).inv ▷ _) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).inv ≫
      (SSet.uliftFunctor.{u + 3, u + 2}).map
        (𝟙 _ ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F₀)

/-- 元の Yoneda 自然変換空間族の全評価は、共同 Hom 図式の同じ元の係数への制限。 -/
lemma yonedaHomWeightFamily_joint (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightFamily F₀) =
      (β_ ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D)) _).hom ≫
      yonedaWeightJointRestriction F₀ ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaHomJointDiagram ((SSet.uliftFunctor.{u + 1, u}).obj C) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightFamily, ← Category.assoc, uncurry_pre_app, uncurry_natural_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_uncurry]
  apply SSet.hom_ext
  intro n
  rfl

omit [Quasicategory C] in
/-- 元の係数評価族の全評価は、共同評価図式の同じ元の係数への制限。 -/
lemma homWeightEvaluationFamily_joint (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    uncurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homWeightEvaluationFamily F₀) =
      (β_ ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D)) _).hom ≫
      yonedaWeightJointRestriction F₀ ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointDiagram ((SSet.uliftFunctor.{u + 1, u}).obj C) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homWeightEvaluationFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily, uncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram_family_uncurry]
  dsimp only [yonedaWeightJointRestriction, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointDiagram,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaEvaluationJointNative]
  rw [uncurry_eq]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
