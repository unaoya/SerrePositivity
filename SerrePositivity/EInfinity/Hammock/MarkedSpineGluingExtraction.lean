module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPasteCutRecovery
public import SerrePositivity.EInfinity.Hammock.MarkedSpineNativeRecovery

/-!
# 元の全因子列の貼り戻し後の反復抽出による回収

概要：任意の元の有限因子列を貼って抽出すると同じ全因子列へ戻る。
方針：一段の三因子の回収を元の列の長さで反復する。
規約：全 prefix・終端は元の指定部分圏の hammock の点である。
使われ方：元の hammock と全因子列の実際の単体的同型。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (Y : Paths C)
  {n : SimplexCategoryᵒᵖ}

lemma markedSpine_paste (X : Paths C) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
    (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n) (r : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.right W Y g.val).obj n) :
    markedSpine W Y n X (FactorTarget.pastePoint W X Y g p r) =
      MarkedSpine.cons X g p (markedSpine W Y n g.val.right r) := by
  have he := markedSpine_nonempty W Y n X
    ((FactorTarget.pasteNonempty W X Y).app n ⟨g, p, r⟩)
  have hc := FactorTarget.pasteNonempty_cut_point W X Y
    (⟨g, p, r⟩ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).obj n)
  exact he.trans (congrArg (fun s : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).obj n =>
    MarkedSpine.cons X s.1 s.2.1 (markedSpine W Y n s.1.val.right s.2.2)) hc)

lemma markedSpine_glue {X : Paths C} (t : MarkedSpine W Y n X) :
    markedSpine W Y n X (MarkedSpine.glue t) = t := by
  induction t with
  | nil X p => exact markedSpine_native W Y X p
  | cons X g p t ih =>
    exact (markedSpine_paste W Y X g p (MarkedSpine.glue t)).trans
      (congrArg (MarkedSpine.cons X g p) ih)

lemma gluing_extraction (X : Paths C) :
    MarkedSpine.gluing W Y X ≫ extraction W Y X = 𝟙 (MarkedSpine.space W Y X) := by
  ext n t
  exact markedSpine_glue W Y t

def markedSpineIso (X : Paths C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y ≅ MarkedSpine.space W Y X where
  hom := extraction W Y X
  inv := MarkedSpine.gluing W Y X
  hom_inv_id := extraction_gluing W Y X
  inv_hom_id := gluing_extraction W Y X

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
