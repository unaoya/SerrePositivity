module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardErasureIso

/-!
# 元の中央 backward 列の eraseInclusion の graph 比較

概要：元の削除語から元の語への同じ graphDiagram.map が弱ホモトピー同値。
方針：列の像から構成した始域の同型と、元の insertBetween の反転性を合成する。
規約：追加の弱同値から anodyne 局所化の同型性を無証明に仮定しない。
使われ方：元の語の backward 列挿入の一般化への基礎。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra
open _root_.SerrePositivity.SimplicialModel _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

lemma erasedGraphMap_localized_isIso
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m)))) := by
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have h : IsIso (Q.map (G.map (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.wordMap n m))) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertionComparison.originalFunctor_localized_isIso cof
  have he : G.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m)) =
      G.map (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion.eraseIso n m).inv ≫ G.map (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.wordMap n m) := by
    rw [← G.map_comp, ← _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion.eraseIso_hom_fac]
    simp only [Iso.inv_hom_id_assoc]
  rw [he, Q.map_comp]
  infer_instance

lemma erasedGraphMap_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.middleColumn n m))) :=
  _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (erasedGraphMap_localized_isIso cof)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
