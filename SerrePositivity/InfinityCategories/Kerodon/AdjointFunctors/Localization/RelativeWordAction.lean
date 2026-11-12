module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeSegmentFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction

/-!
# 相対関手と元の全語の作用の両立

概要：全語の列の圧縮・恒等列の挿入と、元の相対関手の適用を照合する。
方針：元の各 fiber の同方向合成へ関手を適用し、全頂点と全列を回収する。
規約：同型による比較だけでなく、元の対象の厳密な等式を証明する。
使われ方：元の hammock 図式の相対関手に関する自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma columnAux_functor_heq {I : Type*} (U : I → C) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : I)
    (m : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (U p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (U q))
    (m' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (F.functor.obj (U p)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (F.functor.obj (U q)))
    (hm : HEq m' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction.mapFunctor d F.functor).map m)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.columnAux (fun i => F.functor.obj (U i)) d p q m')
      (F.functor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.columnAux U d p q m)) := by
  cases d with
  | forward => exact hm
  | backward => exact heq_of_eq (congrArg Quiver.Hom.unop (eq_of_heq hm))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.columnAux_functor_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction (columnAux_functor_heq)


omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma column_heq (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (j : Fin b.length) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) j) (F.functor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f S j)) :=
  columnAux_functor_heq F (fun k => S.vertex (f.cut k)) _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.segment_map_heq F _ S _ _ _ _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.column_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction (column_heq)


lemma wordAction_obj_eq (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ (fun _ => rfl) (column_heq F f S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.wordAction_obj_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction (wordAction_obj_eq)


lemma wordAction_functor_eq (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := a) (X := X) (Y := Y) F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := b) (X := X) (Y := Y) F := by
  apply CategoryTheory.Functor.ext
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := a) (X := X) (Y := Y) F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := b) (X := X) (Y := Y) F)
    (fun S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y => wordAction_obj_eq F f S) ?_
  intro S T g
  apply (conj_eqToHom_iff_heq _ _ (wordAction_obj_eq F f S) (wordAction_obj_eq F f T)).2
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (wordAction_obj_eq F f S) (wordAction_obj_eq F f T) _ _
    (fun _ => HEq.rfl)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Relative.wordAction_functor_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction (wordAction_functor_eq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction
