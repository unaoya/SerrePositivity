module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendUnit
public import SerrePositivity.EInfinity.Hammock.GraphComposition

/-!
# 固定語の graph の左右単位則

概要：元の空語の単位との合成は、語の単位遷移の後で単位同型に一致する。
方針：全単体の元の射列を、zigzag の厳密な関手の単位則で照合する。
規約：全次数・全縦射の一致を使い、零単体での一致だけでは代用しない。
使われ方：元の全語の余極限上の合成の左右単位則。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (a : Word) (X Y : C)

lemma graphComposition_left_unit :
    (graphUnit W X ⊗ₘ 𝟙 (graph W a X Y)) ≫ graphComposition W Word.empty a X X Y ≫
        (graphDiagram W X Y).map (eqToHom (Word.empty_append a)) =
      (λ_ (graph W a X Y)).hom := by
  rw [graphDiagram_map]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change ((Functor.const (Fin (n.unop.len + 1))).obj (emptyObj W X)).prod' p.2 ⋙
    ZigzagAppend.functor ⋙ WordAction.functor (eqToHom (Word.empty_append a)) = p.2
  apply Functor.hext (fun j => eq_of_heq
    ((WordAction.obj_eqToHom_heq _ _).trans (ZigzagAppend.empty_left_obj_heq (p.2.obj j))))
  intro i j f
  exact (WordAction.map_eqToHom_heq _ _).trans (ZigzagAppend.empty_left_map_heq (p.2.map f))

lemma graphComposition_right_unit :
    (𝟙 (graph W a X Y) ⊗ₘ graphUnit W Y) ≫ graphComposition W a Word.empty X Y Y ≫
        (graphDiagram W X Y).map (eqToHom (Word.append_empty a)) =
      (ρ_ (graph W a X Y)).hom := by
  rw [graphDiagram_map]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change p.1.prod' ((Functor.const (Fin (n.unop.len + 1))).obj (emptyObj W Y)) ⋙
    ZigzagAppend.functor ⋙ WordAction.functor (eqToHom (Word.append_empty a)) = p.1
  apply Functor.hext (fun j => eq_of_heq
    ((WordAction.obj_eqToHom_heq _ _).trans (ZigzagAppend.empty_right_obj_heq (p.1.obj j))))
  intro i j f
  exact (WordAction.map_eqToHom_heq _ _).trans (ZigzagAppend.empty_right_map_heq (p.1.map f))

end SerrePositivity.EInfinity.Hammock
