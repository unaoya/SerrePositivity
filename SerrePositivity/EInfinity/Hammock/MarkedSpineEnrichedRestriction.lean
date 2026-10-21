module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineEnrichedFoldUnique
public import SerrePositivity.EInfinity.Hammock.MarkedSpineMarkedComposition

/-!
# 元の全因子列からの豊穣関手の二つの生成部分への制限

概要：任意の豊穣関手から元の指定因子と非指定生成矢の像を回収する。
方針：元の包含の合成・単位保存と元の豊穣関手の公理を使う。
規約：対象写像を同じ元の写像に保持する。
使われ方：自由積の普遍的な拡張と制限の両逆。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {D : Type uD} [EnrichedCategory SSet.{u} D]

def restrictEnrichedFunctor :
    letI := enrichedCategory W
    EnrichedFunctor SSet.{u} (Paths C) D → EnrichedFoldData W D := by
  letI := enrichedCategory W
  intro G
  exact
    { obj := G.obj
      marked := fun X Y => nilMap W Y X ≫ G.map X Y
      generator := fun g => generatorMap W g ≫ G.map g.val.left g.val.right
      marked_unit := fun X => by
        rw [← Category.assoc, marked_unitMap]
        exact G.map_id X
      marked_comp := fun X Y Z => by
        have hc : composition W X Y Z ≫ G.map X Z =
            (G.map X Y ⊗ₘ G.map Y Z) ≫ eComp SSet.{u} (G.obj X) (G.obj Y) (G.obj Z) :=
          G.map_comp X Y Z
        rw [← Category.assoc, marked_composition, Category.assoc]
        change (nilMap W Y X ⊗ₘ nilMap W Z Y) ≫
          (composition W X Y Z ≫ G.map X Z) = _
        rw [hc]
        rw [← Category.assoc, tensorHom_comp_tensorHom] }

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
