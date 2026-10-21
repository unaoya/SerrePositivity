module

public import SerrePositivity.EInfinity.Hammock.HammockValue

/-!
# 元の通常の局所化 Hom への hammock の評価

概要：実際の通常の局所化関手に一般の評価を代入し、元の右比較の各次数を得る。
方針：元の Q_inverts と元の wIso を使い、標準射・縮約との回収式を保持する。
規約：局所化を未知の入力にせず、Mathlib の元の構成を使う。
使われ方：自由相対解像の実際の DK Hom への右射。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C)

def localizationValue : colimitGraph W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (W.Q.obj X ⟶ W.Q.obj Y) :=
  Zigzag.Value.colimitValue W.Q W.Q_inverts X Y

def reducedLocalizationValue : reducedSimplicialSet W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (W.Q.obj X ⟶ W.Q.obj Y) :=
  Zigzag.Value.reducedValue W.Q W.Q_inverts X Y

lemma graphInclusion_localizationValue (w : Word) :
    graphInclusion W X Y w ≫ localizationValue W X Y = Zigzag.Value.graphMap W.Q W.Q_inverts :=
  Zigzag.Value.graphInclusion_colimitValue W.Q W.Q_inverts X Y w

lemma graphNormalization_reducedLocalizationValue (w : Word) :
    graphNormalization W X Y w ≫ reducedLocalizationValue W X Y =
      Zigzag.Value.graphMap W.Q W.Q_inverts :=
  Zigzag.Value.graphNormalization_reducedValue W.Q W.Q_inverts X Y w

omit [W.IsMultiplicative] in
lemma localized_edge_backward {w : Word} (S : Zigzag W w X Y) (i : Fin w.length)
    (hi : w.direction i = .backward) : Zigzag.Value.edge W.Q W.Q_inverts S i =
      (Localization.Construction.wIso (W := W) (Direction.arrow .backward S i hi).unop
        (Direction.arrow_allowed .backward S i hi)).inv := by
  rw [Zigzag.Value.edge_backward W.Q W.Q_inverts S i hi]
  have h : Zigzag.Value.backwardIso W.Q W.Q_inverts S i hi =
      Localization.Construction.wIso (W := W) (Direction.arrow .backward S i hi).unop
        (Direction.arrow_allowed .backward S i hi) := by
    apply Iso.ext
    rfl
  exact congrArg Iso.inv h

end SerrePositivity.EInfinity.Hammock
