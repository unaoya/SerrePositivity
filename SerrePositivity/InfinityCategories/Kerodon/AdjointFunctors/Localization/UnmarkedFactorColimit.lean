module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPointSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPointWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram

/-!
# 一段の切断の全語の余極限への降下

概要：元の全語の非空部分の余極限から、実際の切断因子の依存和への射を構成する。
方針：全単体作用素と全語への整合を同じ余極限の普遍性に代入する。
規約：非空部分の余極限と元の全 hammock の包含射を明示する。
使われ方：元の非空部分との同定・切断の反復・自由積分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)

lemma cutMap_word {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram.wordMap W X Y f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cutMap W b X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cutMap W a X Y := by
  ext n τ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.point_wordAction W f τ.val τ.property _).symm

def cutCocone : Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram.wordDiagram W X Y) where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y
  ι :=
    { app := fun w => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cutMap W w X Y
      naturality := fun _ _ f => (cutMap_word W X Y f).trans (Category.comp_id _).symm }

def nonemptyColimit : SSet.{max u v} := colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram.wordDiagram W X Y)

def inclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph.simplicialSet W w X Y ⟶ nonemptyColimit W X Y :=
  colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram.wordDiagram W X Y) w

def colimitCut : nonemptyColimit W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y :=
  colimit.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram.wordDiagram W X Y) (cutCocone W X Y)

lemma inclusion_colimitCut (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : inclusion W X Y w ≫ colimitCut W X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cutMap W w X Y :=
  colimit.ι_desc _ _

lemma colimitCut_unique (f : nonemptyColimit W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y)
    (hf : ∀ w, inclusion W X Y w ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cutMap W w X Y) : f = colimitCut W X Y := by
  apply colimit.hom_ext
  intro w
  exact (hf w).trans (inclusion_colimitCut W X Y w).symm

def ambientMap : nonemptyColimit W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y :=
  colim.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram.inclusionNatTrans W X Y)

lemma inclusion_ambientMap (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    inclusion W X Y w ≫ ambientMap W X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph.inclusion W w X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y w :=
  colimit.ι_map _ _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit
