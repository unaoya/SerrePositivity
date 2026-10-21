module

public import SerrePositivity.EInfinity.Hammock.RelativeFixedZigzagFunctor
public import SerrePositivity.EInfinity.Hammock.RelativeWordAction

/-!
# 元の端点表示を固定した全語の作用の自然性

概要：端点の等式移送を含む元の相対関手も、元の全語の作用と厳密に可換。
方針：全頂点・全列・全縦射を既存の同じ相対関手の回収式で照合する。
規約：端点の等式の証明は元の全列のデータを変更しない。
使われ方：固定対象の全語の hammock 図式を自由解像に沿って動かす。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Relative
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {a b : Word} {X Y : C} {X' Y' : D}
  (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')

lemma wordAction_fixedObj_eq (f : a ⟶ b) (S : Zigzag W a X Y) :
    WordAction.obj f ((fixedFunctor F hX hY).obj S) =
      (fixedFunctor F hX hY).obj (WordAction.obj f S) :=
  Zigzag.object_ext _ _ (fun _ => rfl) (column_heq F f S)

lemma wordAction_fixedFunctor_eq (f : a ⟶ b) :
    fixedFunctor (w := a) F hX hY ⋙ WordAction.functor f =
      WordAction.functor f ⋙ fixedFunctor (w := b) F hX hY := by
  apply CategoryTheory.Functor.ext
    (F := fixedFunctor (w := a) F hX hY ⋙ WordAction.functor f)
    (G := WordAction.functor f ⋙ fixedFunctor (w := b) F hX hY)
    (fun S : Zigzag W a X Y => wordAction_fixedObj_eq F hX hY f S) ?_
  intro S T g
  apply (conj_eqToHom_iff_heq _ _
    (wordAction_fixedObj_eq F hX hY f S) (wordAction_fixedObj_eq F hX hY f T)).2
  exact Zigzag.hom_hext (wordAction_fixedObj_eq F hX hY f S)
    (wordAction_fixedObj_eq F hX hY f T) _ _ (fun _ => HEq.rfl)

end SerrePositivity.EInfinity.Hammock.Zigzag.Relative
