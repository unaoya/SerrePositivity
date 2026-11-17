module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardRightEssentialImage
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 元の中央 backward 恒等列の挿入の nerve 比較

概要：右置換の元の unit を全忠実な挿入に戻し、第二の包含の nerve を反転する。
方針：構成済みの前像による本質像の持ち上げを使い、第一の包含と合成する。
規約：元の WordAction と元の graphDiagram の同じ射を結論にする。
使われ方：forward ブロックの間の backward 一列挿入の弱同値性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertionComparison
open CategoryTheory CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.SimplicialModel _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def underlyingUnit : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion
    (C := C) (n := n) (m := m) (X := X) (Y := Y) ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRightEssentialImage.rightReplacement ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.originalFunctor :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialRightReplacement.rightUnit ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRightEssentialImage.rightReplacementCompIso.inv

def unit : 𝟭 (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.Objects (C := C) (n := n) (m := m) (X := X) (Y := Y)) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRightEssentialImage.rightReplacement ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.functor where
  app S := ObjectProperty.homMk (underlyingUnit.app S)
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact underlyingUnit.naturality f

lemma functor_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.functor (C := C) (n := n) (m := m) (X := X) (Y := Y)))) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FullyFaithfulNerveRetraction.of_unit _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.functor _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRightEssentialImage.rightReplacement unit

lemma functor_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.functor (C := C) (n := n) (m := m) (X := X) (Y := Y))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ functor_localized_isIso

lemma originalFunctor_localized_isIso
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.originalFunctor (C := C) (n := n) (m := m) (X := X) (Y := Y)))) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have hI := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion_localized_isIso (n := n) (m := m) (X := X) (Y := Y) cof
  have hJ := functor_localized_isIso (C := C) (n := n) (m := m) (X := X) (Y := Y)
  have h : IsIso (Q.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.functor (C := C) (n := n) (m := m) (X := X) (Y := Y))) ≫
      Q.map (nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion)) := by infer_instance
  have he : Q.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.functor (C := C) (n := n) (m := m) (X := X) (Y := Y))) ≫
      Q.map (nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardTrivialCofibration.inclusion) = Q.map (nerveMap _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.originalFunctor) := by
    rw [← Q.map_comp]
    rfl
  exact he ▸ h

lemma originalFunctor_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.originalFunctor (C := C) (n := n) (m := m) (X := X) (Y := Y))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (originalFunctor_localized_isIso cof)

lemma graphMap_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertion.wordMap n m)) :=
  originalFunctor_isWeakHomotopyEquivalence cof

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardIdentityInsertionComparison
