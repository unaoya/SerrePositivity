module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ThreeArrowGraphWeakComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ReducedColimit

/-!
# 元の三列から reduced hammock への正規化の弱同値性

概要：元の三列の正規化自身は弱ホモトピー同値となる。
方針：元の三列の標準射と、既存の余極限の縮約同型を合成する。
規約：元の正規化の全単体作用素を保持する。
使われ方：元の Map^h の共通始域から reduced hammock への比較。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory _root_.HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma threeArrowNormalization_isWeakHomotopyEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso (weakEquivalences C) X Y).hom :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)
  have h := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.threeArrowGraphInclusion_isWeakHomotopyEquivalence X Y cof).comp hi
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_hom_fac] at h
  exact h

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
