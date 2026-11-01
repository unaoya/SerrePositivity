module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitRowHomotopy
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitArrowMap
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.BackwardZigzag

/-!
# 元の一定行の連結と余極限の合成の回収

概要：行の連結の一定写像が元の二写像の豊穣合成に一致することを示す。
方針：各次数の元の標準射と連結関手を回収する。
規約：既存の合成と単位、元の forward 射を使う。
使われ方：指定射の往復のホモトピーを元の前後合成へ移す。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {X Y Z : C}

lemma colimitRowMap_append (S : Zigzag W a X Y) (T : Zigzag W b Y Z) :
    colimitRowMap (ZigzagAppend.obj S T) =
      (λ_ (𝟙_ SSet.{max u v})).inv ≫ (colimitRowMap S ⊗ₘ colimitRowMap T) ≫
        colimitComposition W X Y Z := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change (graphInclusion W X Z (Word.append a b)).app n
    ((Functor.const (Fin (n.unop.len + 1))).obj (ZigzagAppend.obj S T)) =
    composePoint W X Y Z
      ((graphInclusion W X Y a).app n ((Functor.const (Fin (n.unop.len + 1))).obj S))
      ((graphInclusion W Y Z b).app n ((Functor.const (Fin (n.unop.len + 1))).obj T))
  rw [composePoint_inclusions]
  apply congrArg ((graphInclusion W X Z (Word.append a b)).app n)
  refine CategoryTheory.Functor.ext (F := _) (G := _) (fun _ => rfl) ?_
  intro i j h
  change 𝟙 _ = eqToHom rfl ≫ ZigzagAppend.functor.map (𝟙 (S, T)) ≫ eqToHom rfl
  rw [CategoryTheory.Functor.map_id]
  simp

lemma colimitRowMap_forward (g : X ⟶ Y) :
    colimitRowMap (ForwardZigzag.obj (W := W) g) = arrowMap W g := rfl

def backwardMap (g : X ⟶ Y) (hg : W g) :
    𝟙_ SSet.{max u v} ⟶ colimitGraph W Y X :=
  colimitRowMap (BackwardZigzag.obj g hg)

end SerrePositivity.EInfinity.Hammock
