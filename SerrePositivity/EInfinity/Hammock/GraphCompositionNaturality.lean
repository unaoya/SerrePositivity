module

public import SerrePositivity.EInfinity.Hammock.GraphComposition
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendNaturality
public import SerrePositivity.EInfinity.Hammock.Diagram

/-!
# 全語の graph の図式に自然な単体的合成

概要：元の固定語の graph の合成は、左右の全語の遷移に自然。
方針：連結関手の厳密な自然性を、元の全単体の二つの射列へ前合成する。
規約：元の単体的積と全作用素を使い、余極限上の合成はまだ入力しない。
使われ方：全語の余極限の普遍性による合成の降下。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

/-- 元の graph の合成は、左右の全語の元の遷移射に自然。 -/
lemma graphComposition_naturality {a b a' b' : Word} (f : a ⟶ a') (g : b ⟶ b') (X Y Z : C) :
    ((graphDiagram W X Y).map f ⊗ₘ (graphDiagram W Y Z).map g) ≫
        graphComposition W a' b' X Y Z =
      graphComposition W a b X Y Z ≫ (graphDiagram W X Z).map (Word.appendMap f g) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  exact (congrArg (fun H : Zigzag W a X Y × Zigzag W b Y Z ⥤
      Zigzag W (Word.append a' b') X Z => p.1.prod' p.2 ⋙ H)
    (ZigzagAppend.functor_naturality (W := W) (X := X) (Y := Y) (Z := Z) f g)).symm

end SerrePositivity.EInfinity.Hammock
