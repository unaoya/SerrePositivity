module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagColumnSplitDiagram
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramOfFunctor

/-!
# 任意列の前後の全図式から元の固定端点の関手を回収する

概要：元の固定端点の関手を切り、貼り戻すと同じ全対象・全射の関手に戻る。
方針：MovingDiagram の厳密な貼り戻しと元の ofFunctor の回収を使う。
規約：添字圏は任意で、全行と全縦射を保持する。
使われ方：元の hammock graph の任意列での分割・貼り戻し。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : Word} {X Y : C}

lemma ofFunctor_fixedFunctor (F : D ⥤ Zigzag W w X Y) : (ofFunctor F).fixedFunctor = F := by
  apply CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro d e f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

namespace ColumnSplit

def recombinedFunctor (p : Fin w.length) (F : D ⥤ Zigzag W w X Y) : D ⥤ Zigzag W w X Y :=
  (recombine p (ofFunctor F)).fixedFunctor

lemma recombinedFunctor_eq (p : Fin w.length) (F : D ⥤ Zigzag W w X Y) :
    recombinedFunctor p F = F := by
  rw [recombinedFunctor, recombine_eq, ofFunctor_fixedFunctor]

end ColumnSplit
end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
