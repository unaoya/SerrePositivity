module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GraphCompositionNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph

/-!
# 全語の対の図式から元の余極限への合成余錐

概要：二つの全語の graph の積の図式に整合する、元の合成射の族を構成する。
方針：固定語の合成の自然性と、連結語の標準射の自然性を合成する。
規約：対の図式の余極限を二つの余極限の積と同定する工程は後続。
使われ方：積の各変数の余極限保存による hammock の合成の降下。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative] (X Y Z : C)

def pairDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word × _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{max u v} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).prod (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W Y Z) ⋙ tensor SSet

/-- 元の固定語の合成を、同じ連結語の標準射で余極限へ入れる。 -/
def graphPairing (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b Y Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W a b X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Z (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b)

lemma graphPairing_naturality {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ a') (g : b ⟶ b') :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W Y Z).map g) ≫ graphPairing W X Y Z a' b' =
      graphPairing W X Y Z a b := by
  dsimp only [graphPairing]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition_naturality, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality]

/-- 全語の対の元の積図式に整合する、実際の合成余錐。 -/
def compositionPairingCocone : Cocone (pairDiagram W X Y Z) :=
  { pt := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Z
    ι :=
      { app p := graphPairing W X Y Z p.1 p.2
        naturality _ _ f := (graphPairing_naturality W X Y Z f.1 f.2).trans
          (Category.comp_id _).symm } }

/-- 対の図式の実際の余極限から元の余極限への合成比較。 -/
def colimitCompositionPairing : colimit (pairDiagram W X Y Z) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Z :=
  colimit.desc _ (compositionPairingCocone W X Y Z)

/-- 元の全ての固定語の対で、同じ合成射を厳密に回収する。 -/
lemma colimitCompositionPairing_fac (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    colimit.ι (pairDiagram W X Y Z) (a, b) ≫ colimitCompositionPairing W X Y Z =
      graphPairing W X Y Z a b := colimit.ι_desc _ _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
