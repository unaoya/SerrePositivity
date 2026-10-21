module

public import SerrePositivity.EInfinity.Hammock.RelativeZigzagFunctor
public import SerrePositivity.EInfinity.Hammock.FaithfulObjectEmbedding

/-!
# 対象単射で忠実な相対関手による行と全単体の単射性

概要：元の頂点と射を区別する関手は元の行・縦射・全図式を区別する。
方針：全頂点と各生成列の異種等式を元の関手へ反映する。
規約：元の指定矢の類の充満性やモデル構造は要求しない。
使われ方：有限部分木への持ち上げと射影の整合の検査。
-/

@[expose] public section
universe u v u' v' w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Relative
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) [F.functor.Faithful] (hobj : Function.Injective F.functor.obj)
  {a : Word} {X Y : C}

omit [W.IsMultiplicative] [V.IsMultiplicative] [F.functor.Faithful] in
lemma arrow_heq_of_eq {S T : Zigzag V a (F.functor.obj X) (F.functor.obj Y)}
    (h : S = T) (k : Fin a.length) : HEq (S.arrow k) (T.arrow k) := by
  cases h
  rfl

include hobj in
omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma obj_injective : Function.Injective (obj (w := a) (X := X) (Y := Y) F) := by
  intro S T h
  have hv : ∀ j, S.vertex j = T.vertex j := fun j =>
    hobj (congrArg (fun U => U.vertex j) h)
  apply Zigzag.object_ext S T hv
  intro k
  exact FaithfulObjectEmbedding.map_heq_reflect F.functor hobj (S.arrow k) (T.arrow k)
    (congrArg F.functor.obj (hv (a.source k))) (congrArg F.functor.obj (hv (a.target k)))
    (arrow_heq_of_eq F h k)

lemma functor_faithful : (functor (w := a) (X := X) (Y := Y) F).Faithful := by
  constructor
  intro S T f g h
  apply Zigzag.hom_ext
  intro j
  apply F.functor.map_injective
  exact congrArg (fun k => k.app j) h

include hobj in
lemma postcompose_injective {I : Type w} [Category.{w'} I] :
    Function.Injective (fun G : I ⥤ Zigzag W a X Y => G ⋙ functor F) := by
  let := functor_faithful (a := a) (X := X) (Y := Y) F
  exact FaithfulObjectEmbedding.postcompose_injective _ (obj_injective F hobj)

end SerrePositivity.EInfinity.Hammock.Zigzag.Relative
