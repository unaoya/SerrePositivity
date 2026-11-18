module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedFactorPaste
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedFactorTargetValue
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedCompositionValue
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AllMarkedImage
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedNonemptySpace

/-!
# 任意の元の三因子の貼り戻しの文字列と非空性

概要：元の任意の指定 prefix・非指定生成矢・残りの貼り戻しの値を回収する。
方針：元の包含の空性・同じ一文字と元の合成の連結則を使う。
規約：既に抽出された点に限定せず、任意の三因子を扱う。
使われ方：貼り戻しの後の抽出による元の三因子の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)
  {n : SimplexCategoryᵒᵖ}

lemma pastePoint_value (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n) (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.right W Y g.val).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Y).app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pastePoint W X Y g p r) =
      g.val :: (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W g.val.right Y).app n r := by
  classical
  have hp := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion_range W X g.val.left n _).1 ⟨p, rfl⟩
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W g.val.hom.toPath = [g.val] := by
    change (if W g.val.hom then [] else [] ++ [g.val]) = _
    rw [ite_eq_right g.property]
    rfl
  have hi := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue_composePoint W X g.val.left g.val.right
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X g.val.left).app n p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W.paths g.val.hom.toPath n)
  have hgen := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue_arrowPoint W (n := n) g.val.hom.toPath).trans hg
  have hv := (hi.trans (congrArg₂ List.append hp hgen)).trans (List.nil_append [g.val])
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue_composePoint W X g.val.right Y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X g.val.left g.val.right ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X g.val.left).app n p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W.paths g.val.hom.toPath n)) r).trans
        (congrArg (fun z => List.append z ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W g.val.right Y).app n r)) hv)

lemma paste_value : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.paste W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.wordValue W X Y := by
  ext n s
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pastePoint_value W X Y s.1 s.2.1 s.2.2

lemma pastePoint_nonempty (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n)
    (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.right W Y g.val).obj n) : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Y).app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pastePoint W X Y g p r) ≠ [] :=
  fun h => List.cons_ne_nil _ _ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pastePoint_value W X Y g p r).symm.trans h)

def pasteNonempty : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.NonemptyValue.space W X Y where
  app _ := ↾fun s => ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pastePoint W X Y s.1 s.2.1 s.2.2, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pastePoint_nonempty W X Y s.1 s.2.1 s.2.2⟩
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pastePoint_simplex W X Y θ s.1 s.2.1 s.2.2

lemma pasteNonempty_inclusion :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pasteNonempty W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.NonemptyValue.inclusion W X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.paste W X Y := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget
