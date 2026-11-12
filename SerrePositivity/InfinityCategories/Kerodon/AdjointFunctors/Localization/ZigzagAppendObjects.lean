module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory

/-!
# 元の二つの固定端点 zigzag の連結

概要：共有端点を持つ二つの zigzag の元の全列を連結する。
方針：各列の両端を元の頂点の等式で移し、元の射をそのまま使う。
規約：後ろ向きの射の類の条件を保持し、余分な cofibrancy やモデル構造は不要。
使われ方：固定語の hammock graph の合成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z : C}

lemma source_left_eq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin a.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).source (i.castAdd b.length)) = S.vertex (a.source i) :=
  (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.source_left a b i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T _)

lemma target_left_eq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin a.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).target (i.castAdd b.length)) = S.vertex (a.target i) :=
  (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.target_left a b i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T _)

lemma source_right_eq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin b.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).source (i.natAdd a.length)) = T.vertex (b.source i) :=
  (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.source_right a b i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T _)

lemma target_right_eq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin b.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).target (i.natAdd a.length)) = T.vertex (b.target i) :=
  (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.target_right a b i)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T _)

/-- 左側の元の一列を、同じ二つの頂点の移送だけで連結語へ入れる。 -/
def leftArrow (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin a.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).source (i.castAdd b.length)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).target (i.castAdd b.length)) :=
  eqToHom (source_left_eq S T i) ≫ S.arrow i ≫ eqToHom (target_left_eq S T i).symm

/-- 右側の元の一列を、接合点の等式を含む移送だけで連結語へ入れる。 -/
def rightArrow (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin b.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).source (i.natAdd a.length)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).target (i.natAdd a.length)) :=
  eqToHom (source_right_eq S T i) ≫ T.arrow i ≫ eqToHom (target_right_eq S T i).symm

lemma leftArrow_mem (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin a.length)
    (hi : a.direction i = .backward) : W (leftArrow S T i) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2 (S.backward_mem i hi)

lemma rightArrow_mem (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin b.length)
    (hi : b.direction i = .backward) : W (rightArrow S T i) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2 (T.backward_mem i hi)

/-- 元の全頂点・全列を連結した固定端点 zigzag。 -/
def obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Z where
  vertex := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T
  first := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T 0).trans S.first
  last := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T (Fin.last b.length)).trans T.last
  arrow := Fin.addCases (leftArrow S T) (rightArrow S T)
  backward_mem i hi := by
    cases i using Fin.addCases with
    | left i =>
      rw [Fin.addCases_left]
      exact leftArrow_mem S T i ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a b i).symm.trans hi)
    | right i =>
      rw [Fin.addCases_right]
      exact rightArrow_mem S T i ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a b i).symm.trans hi)

/-- 左側の全列は、元の同じ射と異種等しい。 -/
lemma arrow_left_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin a.length) :
    HEq ((obj S T).arrow (i.castAdd b.length)) (S.arrow i) := by
  dsimp only [obj]
  rw [Fin.addCases_left]
  simp only [leftArrow, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- 右側の全列も、元の同じ射と異種等しい。 -/
lemma arrow_right_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin b.length) :
    HEq ((obj S T).arrow (i.natAdd a.length)) (T.arrow i) := by
  dsimp only [obj]
  rw [Fin.addCases_right]
  simp only [rightArrow, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects
