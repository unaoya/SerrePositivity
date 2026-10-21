module

public import SerrePositivity.EInfinity.Hammock.LeftRoofPrecomposeObjects

/-!
# 始域比較の下行の元の語の作用による回収

概要：元の始域射と roof の連結へ恒等列を挿入すると同じ下行になる。
方針：元の cut と一列・空区間の合成を使う。
規約：元の全頂点・射・端点を保持する。
使われ方：下行を元の hammock の前合成へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X' X U Y : C}

lemma lowerInsert_obj (p : U ⟶ X) (hp : W p) (f : X' ⟶ X) (σ : U ⟶ Y) :
    WordAction.obj lowerInsert
        (ZigzagAppend.obj (ForwardZigzag.obj f) (LeftRoof.obj W p hp σ)) =
      lower W p hp f σ := by
  let S := ZigzagAppend.obj (ForwardZigzag.obj (W := W) f) (LeftRoof.obj W p hp σ)
  have ha0 : S.arrow (0 : Fin 3) = f :=
    eq_of_heq (ZigzagAppend.arrow_left_heq (ForwardZigzag.obj f)
      (LeftRoof.obj W p hp σ) (0 : Fin 1))
  have ha1 : S.arrow (1 : Fin 3) = p :=
    eq_of_heq (ZigzagAppend.arrow_right_heq (ForwardZigzag.obj f)
      (LeftRoof.obj W p hp σ) (0 : Fin 2))
  have ha2 : S.arrow (2 : Fin 3) = σ :=
    eq_of_heq (ZigzagAppend.arrow_right_heq (ForwardZigzag.obj f)
      (LeftRoof.obj W p hp σ) (1 : Fin 2))
  apply Zigzag.object_ext
  · intro j
    change S.vertex (lowerInsert.cut j) = _
    rw [lowerInsert_cut]
    fin_cases j <;> rfl
  · intro i
    fin_cases i
    · apply heq_of_eq
      change (Segment.map .backward S 0 0 _ _).unop = 𝟙 X'
      exact congrArg (fun a : Opposite.op X' ⟶ Opposite.op X' => a.unop)
        (Segment.map_refl .backward S 0 _)
    · apply heq_of_eq
      change Segment.map .forward S 0 1 _ _ = f
      exact (Segment.map_adjacent .forward S (0 : Fin 3) rfl).trans
        ((eq_of_heq (Direction.forward_arrow_heq S (0 : Fin 3) rfl)).trans ha0)
    · apply heq_of_eq
      change (Segment.map .backward S 1 2 _ _).unop = p
      exact congrArg (fun a : Opposite.op X ⟶ Opposite.op U => a.unop)
        ((Segment.map_adjacent .backward S (1 : Fin 3) rfl).trans
          ((eq_of_heq (Direction.backward_arrow_heq S (1 : Fin 3) rfl)).trans
            (congrArg (fun a : U ⟶ X => a.op) ha1)))
    · apply heq_of_eq
      change Segment.map .forward S 2 3 _ _ = σ
      exact (Segment.map_adjacent .forward S (2 : Fin 3) rfl).trans
        ((eq_of_heq (Direction.forward_arrow_heq S (2 : Fin 3) rfl)).trans ha2)

end SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
