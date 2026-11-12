module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph

/-!
# 非空の非指定文字を持つ hammock の全語の図式

概要：元の圧縮と恒等列の挿入を非空部分へ制限する。
方針：元の graph 図式の恒等・合成則と非空性の保持を使う。
規約：全語と元の単体を保持する。
使われ方：一段の切断の自然な余錐と余極限への降下。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)

def wordMap {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph.simplicialSet W a X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph.simplicialSet W b X Y where
  app _ := ↾fun τ => ⟨((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).app _ τ.val,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nonemptyColumns_wordAction W f (τ.val.obj 0) τ.property⟩
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro τ
    apply Subtype.ext
    exact congrArg (fun k => k τ.val) (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f).naturality θ)

lemma wordMap_id (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : wordMap W X Y (𝟙 a) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph.simplicialSet W a X Y) := by
  ext n τ
  apply Subtype.ext
  exact congrArg (fun k => k.app n τ.val) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map_id a)

lemma wordMap_comp {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (g : b ⟶ c) :
    wordMap W X Y (f ≫ g) = wordMap W X Y f ≫ wordMap W X Y g := by
  ext n τ
  apply Subtype.ext
  exact congrArg (fun k => k.app n τ.val) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map_comp f g)

def wordDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{max u v} where
  obj w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph.simplicialSet W w X Y
  map f := wordMap W X Y f
  map_id := wordMap_id W X Y
  map_comp := wordMap_comp W X Y

def inclusionNatTrans : wordDiagram W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y where
  app w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph.inclusion W w X Y
  naturality _ _ _ := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram
