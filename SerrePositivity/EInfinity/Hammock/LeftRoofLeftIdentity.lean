module

public import SerrePositivity.EInfinity.Hammock.LeftRoofRightIdentity
public import SerrePositivity.EInfinity.Hammock.ColimitRowComposition

/-!
# 元の恒等左脚 roof と同じ forward 射の厳密な余極限表示

概要：前向き一列に恒等後向き列を挿入すると、元の恒等左脚 roof になる。
方針：同じ cut・元の空区間と一列区間を計算し、元の語の標準射を適用する。
規約：元の射・元の余極限の点を保持する。
使われ方：Under 全円柱の定数端を元の右脚へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.LeftRoof
open CategoryTheory MonoidalCategory

def insertLeftIdentity : Word.single .forward ⟶ word where
  orderHom := ⟨Fin.succ, fun _ _ h => Nat.succ_le_succ h⟩
  direction_eq i := by fin_cases i; rfl

lemma insertLeftIdentity_cut (j : Fin 3) :
    insertLeftIdentity.cut j = (![0, 0, 1] : Fin 3 → Fin 2) j := by
  fin_cases j <;> decide

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y : C} (f : X ⟶ Y)

lemma insertLeftIdentity_obj :
    WordAction.obj insertLeftIdentity (ForwardZigzag.obj (W := W) f) =
      obj W (𝟙 X) (W.id_mem X) f := by
  apply Zigzag.object_ext
  · intro j
    change (ForwardZigzag.obj (W := W) f).vertex (insertLeftIdentity.cut j) = _
    rw [insertLeftIdentity_cut]
    fin_cases j <;> rfl
  · intro i
    fin_cases i
    · apply heq_of_eq
      change (Segment.map .backward (ForwardZigzag.obj (W := W) f) 0 0 _ _).unop = 𝟙 X
      exact congrArg (fun m : Opposite.op X ⟶ Opposite.op X => m.unop)
        (Segment.map_refl .backward (ForwardZigzag.obj (W := W) f) 0 _)
    · apply heq_of_eq
      change Segment.map .forward (ForwardZigzag.obj (W := W) f) 0 1 _ _ = f
      exact (Segment.map_adjacent .forward (ForwardZigzag.obj (W := W) f) (0 : Fin 1) rfl).trans
        (eq_of_heq (Direction.forward_arrow_heq (ForwardZigzag.obj (W := W) f) (0 : Fin 1) rfl))

lemma colimitRowMap_leftIdentity : colimitRowMap (obj W (𝟙 X) (W.id_mem X) f) =
    arrowMap W f := by
  rw [← insertLeftIdentity_obj, colimitRowMap_wordAction, colimitRowMap_forward]

end SerrePositivity.EInfinity.Hammock.LeftRoof
