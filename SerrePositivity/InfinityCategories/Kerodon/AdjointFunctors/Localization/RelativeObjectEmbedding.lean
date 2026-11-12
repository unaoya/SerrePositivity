module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FaithfulObjectEmbedding

/-!
# 対象単射で忠実な相対関手による行と全単体の単射性

概要：元の頂点と射を区別する関手は元の行・縦射・全図式を区別する。
方針：全頂点と各生成列の異種等式を元の関手へ反映する。
規約：元の指定矢の類の充満性やモデル構造は要求しない。
使われ方：有限部分木への持ち上げと射影の整合の検査。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v' w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeObjectEmbedding
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) [F.functor.Faithful] (hobj : Function.Injective F.functor.obj)
  {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

omit [W.IsMultiplicative] [V.IsMultiplicative] [F.functor.Faithful] in
lemma arrow_heq_of_eq {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag V a (F.functor.obj X) (F.functor.obj Y)}
    (h : S = T) (k : Fin a.length) : HEq (S.arrow k) (T.arrow k) := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.arrow_heq_of_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeObjectEmbedding (arrow_heq_of_eq)


include hobj in
omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma obj_injective : Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj (w := a) (X := X) (Y := Y) F) := by
  intro S T h
  have hv : ∀ j, S.vertex j = T.vertex j := fun j =>
    hobj (congrArg (fun U => U.vertex j) h)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext S T hv
  intro k
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FaithfulObjectEmbedding.map_heq_reflect F.functor hobj (S.arrow k) (T.arrow k)
    (congrArg F.functor.obj (hv (a.source k))) (congrArg F.functor.obj (hv (a.target k)))
    (arrow_heq_of_eq F h k)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.obj_injective export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeObjectEmbedding (obj_injective)


lemma functor_faithful : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := a) (X := X) (Y := Y) F).Faithful := by
  constructor
  intro S T f g h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
  intro j
  apply F.functor.map_injective
  exact congrArg (fun k => k.app j) h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.functor_faithful export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeObjectEmbedding (functor_faithful)


include hobj in
lemma postcompose_injective {I : Type w} [Category.{w'} I] :
    Function.Injective (fun G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y => G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F) := by
  let := functor_faithful (a := a) (X := X) (Y := Y) F
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FaithfulObjectEmbedding.postcompose_injective _ (obj_injective F hobj)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.postcompose_injective export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeObjectEmbedding (postcompose_injective)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeObjectEmbedding
