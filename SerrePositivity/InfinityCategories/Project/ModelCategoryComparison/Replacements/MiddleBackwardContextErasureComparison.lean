module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardContextEssentialImage
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 任意の前後の語を保つ元の中央 backward 挿入の弱同値性

概要：元の eraseInclusion の graph 写像自体が弱ホモトピー同値となる。
方針：右置換の unit を全忠実な第二の包含へ持ち上げ、第一の包含と合成する。
規約：元の全体の語・中央列・削除語・挿入写像を保持する。
使われ方：padding された任意の語の backward 一列挿入の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasureComparison
open CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.SimplicialModel _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n m : ℕ) (X Y : C)

def underlyingUnit : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.inclusion a b n m X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextEssentialImage.rightReplacement a b n m X Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.originalFunctor a b n m X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextRightReplacement.rightUnit a b n m X Y ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextEssentialImage.rightReplacementCompIso a b n m X Y).inv

def unit : 𝟭 (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.Objects a b n m X Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextEssentialImage.rightReplacement a b n m X Y ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.functor a b n m X Y where
  app S := ObjectProperty.homMk ((underlyingUnit a b n m X Y).app S)
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact (underlyingUnit a b n m X Y).naturality f

lemma functor_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.functor a b n m X Y))) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FullyFaithfulNerveRetraction.of_unit (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.functor a b n m X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextEssentialImage.rightReplacement a b n m X Y) (unit a b n m X Y)

lemma functor_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.functor a b n m X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (functor_localized_isIso a b n m X Y)

variable (cof : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

include cof in
lemma originalFunctor_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.originalFunctor a b n m X Y))) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have hI := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.inclusion_localized_isIso a b n m X Y cof
  have hJ := functor_localized_isIso a b n m X Y
  have h : IsIso (Q.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.functor a b n m X Y)) ≫
      Q.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.inclusion a b n m X Y))) := by infer_instance
  have he : Q.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.functor a b n m X Y)) ≫
      Q.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextTrivialCofibration.inclusion a b n m X Y)) =
        Q.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.originalFunctor a b n m X Y)) := by
    rw [← Q.map_comp]
    rfl
  exact he ▸ h

include cof in
lemma originalFunctor_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasure.originalFunctor a b n m X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (originalFunctor_localized_isIso a b n m X Y cof)

include cof in
lemma graphMap_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.wholeWord a b n m) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleColumn a b n m))) :=
  originalFunctor_isWeakHomotopyEquivalence a b n m X Y cof

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasureComparison
