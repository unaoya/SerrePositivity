module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineExtractionGluing

/-!
# 元の指定 hammock の包含の後の反復抽出による終端の回収

概要：元の指定 hammock を包含して抽出すると、同じ元の点を終端とする切断列に戻る。
方針：空文字列部分との元の同型の両逆と既存の空の場合の抽出式を使う。
規約：実際の指定部分圏の同じ元の点を保持する。
使われ方：貼り戻し後の因子回収の帰納の nil の場合。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (Y X : Paths C)
  {n : SimplexCategoryᵒᵖ}

lemma markedSpine_native (p : (AllMarked.nativeSpace W X Y).obj n) :
    markedSpine W Y n X ((AllMarked.inclusion W X Y).app n p) = MarkedSpine.nil X p := by
  have hx := (AllMarked.inclusion_range W X Y n _).1 ⟨p, rfl⟩
  rw [markedSpine_empty W Y n X _ hx]
  exact congrArg (MarkedSpine.nil X) (congrArg (fun k => k.app n p)
    (AllMarked.emptyValueMap_emptyLift W X Y))

def MarkedSpine.nilMap : AllMarked.nativeSpace W X Y ⟶ MarkedSpine.space W Y X where
  app _ := ↾fun p => MarkedSpine.nil X p
  naturality _ _ _ := rfl

lemma nativeInclusion_extraction :
    AllMarked.inclusion W X Y ≫ extraction W Y X = MarkedSpine.nilMap W Y X := by
  ext n p
  exact markedSpine_native W Y X p

lemma nilMap_gluing : MarkedSpine.nilMap W Y X ≫ MarkedSpine.gluing W Y X =
    AllMarked.inclusion W X Y := rfl

lemma extraction_gluing_nil (p : (AllMarked.nativeSpace W X Y).obj n) :
    (extraction W Y X).app n ((MarkedSpine.gluing W Y X).app n (MarkedSpine.nil X p)) =
      MarkedSpine.nil X p := markedSpine_native W Y X p

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
