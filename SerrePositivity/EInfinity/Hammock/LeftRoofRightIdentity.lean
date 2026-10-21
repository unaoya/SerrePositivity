module

public import SerrePositivity.EInfinity.Hammock.LeftRoof
public import SerrePositivity.EInfinity.Hammock.DirectionArrowComparison

/-!
# 元の二列 roof と恒等右脚の三列の一致

概要：元の語の単射が恒等右脚だけを挿入することを全頂点・全列で照合する。
方針：同じ cut と一列・空区間の合成を使う。
規約：元の射と全端点を保持する。
使われ方：source frame の元の三本矢比較を二列へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.LeftRoof
open CategoryTheory

def insertRightIdentity : word ⟶ Word.threeArrow where
  orderHom := ⟨Fin.castSucc, fun _ _ h => h⟩
  direction_eq i := by fin_cases i <;> rfl

lemma insertRightIdentity_cut (j : Fin 4) :
    insertRightIdentity.cut j = (![0, 1, 2, 2] : Fin 4 → Fin 3) j := by
  fin_cases j <;> decide

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y U : C}

def rightIdentityObj (p : U ⟶ X) (hp : W p) (f : U ⟶ Y) :
    Zigzag W Word.threeArrow X Y where
  vertex := ![X, U, Y, Y]
  first := rfl
  last := rfl
  arrow := Fin.cases p (Fin.cases f (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i)))
  backward_mem i hi := by
    fin_cases i
    · exact hp
    · cases hi
    · exact W.id_mem Y

lemma insertRightIdentity_obj (p : U ⟶ X) (hp : W p) (f : U ⟶ Y) :
    WordAction.obj insertRightIdentity (obj W p hp f) = rightIdentityObj W p hp f := by
  apply Zigzag.object_ext
  · intro j
    change (obj W p hp f).vertex (insertRightIdentity.cut j) = _
    rw [insertRightIdentity_cut]
    fin_cases j <;> rfl
  · intro i
    fin_cases i
    · apply heq_of_eq
      change (Segment.map .backward (obj W p hp f) 0 1 _ _).unop = p
      exact congrArg (fun m : Opposite.op X ⟶ Opposite.op U => m.unop)
        ((Segment.map_adjacent .backward (obj W p hp f) (0 : Fin 2) rfl).trans
          (eq_of_heq (Direction.backward_arrow_heq (obj W p hp f) (0 : Fin 2) rfl)))
    · apply heq_of_eq
      change Segment.map .forward (obj W p hp f) 1 2 _ _ = f
      exact (Segment.map_adjacent .forward (obj W p hp f) (1 : Fin 2) rfl).trans
        (eq_of_heq (Direction.forward_arrow_heq (obj W p hp f) (1 : Fin 2) rfl))
    · apply heq_of_eq
      change (Segment.map .backward (obj W p hp f) 2 2 _ _).unop = 𝟙 Y
      exact congrArg (fun m : Opposite.op Y ⟶ Opposite.op Y => m.unop)
        (Segment.map_refl .backward (obj W p hp f) 2 _)

end SerrePositivity.EInfinity.Hammock.LeftRoof
