module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafUniverseDiagram

/-!
概要：任意の元の全前層族の宇宙変更を、その元の共同評価の宇宙変更へ厳密に照合する。
方針：元の内部 Hom 比較と元の前合成作用を展開する。
規約：任意の全パラメータと元の全写像を保持する。
使われ方：全 Yoneda 評価図式を元の Hom 係数の族へ制限する際の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 指定前層宇宙変更をした元の任意の全族の評価は、元の共同評価の同じ宇宙変更。 -/
lemma presheafUniverseDiagram_family_uncurry {C : SSet.{u}} {K : SSet.{u + 1}}
    (F : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) :
    uncurry ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C) =
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u, u + 1} C).inv ▷
        (SSet.uliftFunctor.{u + 2, u + 1}).obj K) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u + 1, u + 2} ((SSet.uliftFunctor.{u + 1, u}).obj C.op) K).inv ≫
      (SSet.uliftFunctor.{u + 2, u + 1}).map (uncurry F) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram.{u} := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram]
  rw [← Category.assoc, ← Category.assoc, uncurry_pre_app, uncurry_natural_right,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftInternalHomComparison_map_uncurry]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
