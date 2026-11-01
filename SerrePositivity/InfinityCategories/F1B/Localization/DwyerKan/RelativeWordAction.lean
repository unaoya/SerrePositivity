module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeSegmentFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordAction

/-!
# 相対関手と元の全語の作用の両立

概要：全語の列の圧縮・恒等列の挿入と、元の相対関手の適用を照合する。
方針：元の各 fiber の同方向合成へ関手を適用し、全頂点と全列を回収する。
規約：同型による比較だけでなく、元の対象の厳密な等式を証明する。
使われ方：元の hammock 図式の相対関手に関する自然性。
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
  (F : LocalizerMorphism W V) {a b : Word} {X Y : C}

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma columnAux_functor_heq {I : Type*} (U : I → C) (d : Direction) (p q : I)
    (m : Direction.vertex d (U p) ⟶ Direction.vertex d (U q))
    (m' : Direction.vertex d (F.functor.obj (U p)) ⟶
      Direction.vertex d (F.functor.obj (U q)))
    (hm : HEq m' ((Direction.mapFunctor d F.functor).map m)) :
    HEq (WordAction.columnAux (fun i => F.functor.obj (U i)) d p q m')
      (F.functor.map (WordAction.columnAux U d p q m)) := by
  cases d with
  | forward => exact hm
  | backward => exact heq_of_eq (congrArg Quiver.Hom.unop (eq_of_heq hm))

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma column_heq (f : a ⟶ b) (S : Zigzag W a X Y) (j : Fin b.length) :
    HEq (WordAction.column f (obj F S) j) (F.functor.map (WordAction.column f S j)) :=
  columnAux_functor_heq F (fun k => S.vertex (f.cut k)) _ _ _ _ _
    (segment_map_heq F _ S _ _ _ _)

lemma wordAction_obj_eq (f : a ⟶ b) (S : Zigzag W a X Y) :
    WordAction.obj f (obj F S) = obj F (WordAction.obj f S) :=
  Zigzag.object_ext _ _ (fun _ => rfl) (column_heq F f S)

lemma wordAction_functor_eq (f : a ⟶ b) :
    functor (w := a) (X := X) (Y := Y) F ⋙ WordAction.functor f =
      WordAction.functor f ⋙ functor (w := b) (X := X) (Y := Y) F := by
  apply CategoryTheory.Functor.ext
    (F := functor (w := a) (X := X) (Y := Y) F ⋙ WordAction.functor f)
    (G := WordAction.functor f ⋙ functor (w := b) (X := X) (Y := Y) F)
    (fun S : Zigzag W a X Y => wordAction_obj_eq F f S) ?_
  intro S T g
  apply (conj_eqToHom_iff_heq _ _ (wordAction_obj_eq F f S) (wordAction_obj_eq F f T)).2
  exact Zigzag.hom_hext (wordAction_obj_eq F f S) (wordAction_obj_eq F f T) _ _
    (fun _ => HEq.rfl)

end SerrePositivity.EInfinity.Hammock.Zigzag.Relative
