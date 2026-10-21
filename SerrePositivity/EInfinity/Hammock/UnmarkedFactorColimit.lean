module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorPointSimplex
public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorPointWordAction
public import SerrePositivity.EInfinity.Hammock.UnmarkedNonemptyWordDiagram

/-!
# 一段の切断の全語の余極限への降下

概要：元の全語の非空部分の余極限から、実際の切断因子の依存和への射を構成する。
方針：全単体作用素と全語への整合を同じ余極限の普遍性に代入する。
規約：非空部分の余極限と元の全 hammock の包含射を明示する。
使われ方：元の非空部分との同定・切断の反復・自由積分解。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)

lemma cutMap_word {a b : Word} (f : a ⟶ b) :
    NonemptyGraph.wordMap W X Y f ≫ cutMap W b X Y = cutMap W a X Y := by
  ext n τ
  exact (point_wordAction W f τ.val τ.property _).symm

def cutCocone : Cocone (NonemptyGraph.wordDiagram W X Y) where
  pt := FactorTarget.space W X Y
  ι :=
    { app := fun w => cutMap W w X Y
      naturality := fun _ _ f => (cutMap_word W X Y f).trans (Category.comp_id _).symm }

def nonemptyColimit : SSet.{max u v} := colimit (NonemptyGraph.wordDiagram W X Y)

def inclusion (w : Word) : NonemptyGraph.simplicialSet W w X Y ⟶ nonemptyColimit W X Y :=
  colimit.ι (NonemptyGraph.wordDiagram W X Y) w

def colimitCut : nonemptyColimit W X Y ⟶ FactorTarget.space W X Y :=
  colimit.desc (NonemptyGraph.wordDiagram W X Y) (cutCocone W X Y)

lemma inclusion_colimitCut (w : Word) : inclusion W X Y w ≫ colimitCut W X Y = cutMap W w X Y :=
  colimit.ι_desc _ _

lemma colimitCut_unique (f : nonemptyColimit W X Y ⟶ FactorTarget.space W X Y)
    (hf : ∀ w, inclusion W X Y w ≫ f = cutMap W w X Y) : f = colimitCut W X Y := by
  apply colimit.hom_ext
  intro w
  exact (hf w).trans (inclusion_colimitCut W X Y w).symm

def ambientMap : nonemptyColimit W X Y ⟶ colimitGraph W.paths X Y :=
  colim.map (NonemptyGraph.inclusionNatTrans W X Y)

lemma inclusion_ambientMap (w : Word) :
    inclusion W X Y w ≫ ambientMap W X Y =
      NonemptyGraph.inclusion W w X Y ≫ graphInclusion W.paths X Y w :=
  colimit.ι_map _ _

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
