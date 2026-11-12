module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionArrowComparison

/-!
# 元の二列 roof と恒等右脚の三列の一致

概要：元の語の単射が恒等右脚だけを挿入することを全頂点・全列で照合する。
方針：同じ cut と一列・空区間の合成を使う。
規約：元の射と全端点を保持する。
使われ方：source frame の元の三本矢比較を二列へ移す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

def insertRightIdentity : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow where
  orderHom := ⟨Fin.castSucc, fun _ _ h => h⟩
  direction_eq i := by fin_cases i <;> rfl

lemma insertRightIdentity_cut (j : Fin 4) :
    insertRightIdentity.cut j = (![0, 1, 2, 2] : Fin 4 → Fin 3) j := by
  fin_cases j <;> decide

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y U : C}

def rightIdentityObj (p : U ⟶ X) (hp : W p) (f : U ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y where
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
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj insertRightIdentity (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) = rightIdentityObj W p hp f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f).vertex (insertRightIdentity.cut j) = _
    rw [insertRightIdentity_cut]
    fin_cases j <;> rfl
  · intro i
    fin_cases i
    · apply heq_of_eq
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) 0 1 _ _).unop = p
      exact congrArg (fun m : Opposite.op X ⟶ Opposite.op U => m.unop)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) (0 : Fin 2) rfl).trans
          (eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backward_arrow_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) (0 : Fin 2) rfl)))
    · apply heq_of_eq
      change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) 1 2 _ _ = f
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) (1 : Fin 2) rfl).trans
        (eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) (1 : Fin 2) rfl))
    · apply heq_of_eq
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) 2 2 _ _).unop = 𝟙 Y
      exact congrArg (fun m : Opposite.op Y ⟶ Opposite.op Y => m.unop)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_refl .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) 2 _)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
