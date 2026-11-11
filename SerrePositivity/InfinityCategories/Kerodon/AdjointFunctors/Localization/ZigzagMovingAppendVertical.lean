module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHom

/-!
# 動く共有端点を持つ二つの zigzag の全縦射の貼り合わせ

概要：端点が動く左右の部分区間の縦射を、同じ接合点で貼り合わせる。
方針：左右の元の成分を使い、接合点の二つの成分の異種等式を明示入力とする。
規約：局所端点の射を恒等射とは仮定しない。全頂点の弱同値を保持する。
使われ方：元の長い zigzag のブロック置換の関手性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z X' Y' Z' : C}
  {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} {S' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X' Y'}
  {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z} {T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y' Z'}

/-- 各連結頂点で元の同じ縦射を使う。 -/
def app (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S S') (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T T')
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T k ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S' T' k :=
  if hk : k.val ≤ a.length then
    eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_le S T k hk) ≫ f.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.leftIndex k hk) ≫
      eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_le S' T' k hk).symm
  else
    eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_gt S T k hk) ≫ g.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.rightIndex k hk) ≫
      eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_gt S' T' k hk).symm

lemma app_mem (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S S') (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T T')
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)) : W (app f g k) := by
  unfold app
  split_ifs with hk
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2 (f.app_mem _)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2 (g.app_mem _)

lemma app_index_heq (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S S') (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T T')
    {k k' : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)} (h : k = k') :
    HEq (app f g k) (app f g k') := by
  cases h
  rfl

/-- 左部分の全縦射は、元の同じ左の縦射と異種等しい。 -/
lemma app_left_heq (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S S') (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T T')
    (i : Fin (a.length + 1)) :
    HEq (app f g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b i)) (f.app i) := by
  rw [app, dite_eq_left (show (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b i).val ≤ a.length from
    Nat.le_of_lt_succ i.isLt)]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- 右部分の全縦射も、接合点を含めて元の同じ右の縦射と異種等しい。 -/
lemma app_right_heq (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S S') (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T T')
    (hj : HEq (f.app (Fin.last a.length)) (g.app 0))
    (i : Fin (b.length + 1)) :
    HEq (app f g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b i)) (g.app i) := by
  by_cases hi : i.val = 0
  · have h : i = 0 := Fin.ext hi
    subst i
    exact (app_index_heq f g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.jointVertex a b).symm).trans
      ((app_left_heq f g (Fin.last a.length)).trans hj)
  · have hk : ¬ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b i).val ≤ a.length := by
      change ¬ a.length + i.val ≤ a.length
      omega
    rw [app, dite_eq_right hk]
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq g
    apply Fin.ext
    dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.rightIndex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex]
    omega

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical
