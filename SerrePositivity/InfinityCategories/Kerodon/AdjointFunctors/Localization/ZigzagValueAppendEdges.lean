module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendDirections
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath

/-!
# 元の連結 zigzag の左右の評価された列

概要：連結後の各列の値は、元の同じ列の値と異種等しい。
方針：元の向き付き列の回収と、関手像・逆同型の端点移送の回収を使う。
規約：元の各生成列と元の端点だけを使う。
使われ方：元の値の射列の左右への制限。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppendEdges
open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} (L : C ⥤ D) (hL : W.IsInvertedBy L)

lemma map_heq {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) : HEq (L.map f) (L.map g) := by
  cases hA
  cases hB
  cases eq_of_heq h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.map_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppendEdges (map_heq)


lemma map_unop_heq {A B A' B' : C} (hA : A = A') (hB : B = B')
    {f : op A ⟶ op B} {g : op A' ⟶ op B'} (h : HEq f g) :
    HEq (L.map f.unop) (L.map g.unop) := by
  cases hA
  cases hB
  cases eq_of_heq h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.map_unop_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppendEdges (map_unop_heq)


lemma iso_inv_heq {A B A' B' : D} (hA : A = A') (hB : B = B')
    (e : A ≅ B) (e' : A' ≅ B') (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  cases hA
  cases hB
  have he : e = e' := Iso.ext (eq_of_heq h)
  cases he
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.iso_inv_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppendEdges (iso_inv_heq)


variable {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z : C}

lemma edge_append_left_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin a.length) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) (i.castAdd b.length)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge L hL S i) := by
  cases hi : a.direction i with
  | forward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward L hL _ _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a b i).trans hi),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward L hL S i hi]
    exact map_heq L (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T i.castSucc)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T i.succ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.direction_left_heq S T .forward i hi)
  | backward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward L hL _ _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a b i).trans hi),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward L hL S i hi]
    exact iso_inv_heq (congrArg L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T i.succ))
      (congrArg L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T i.castSucc)) _ _
      (map_unop_heq L (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T i.castSucc)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T i.succ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.direction_left_heq S T .backward i hi))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.edge_append_left_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppendEdges (edge_append_left_heq)


lemma edge_append_right_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin b.length) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) (i.natAdd a.length)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge L hL T i) := by
  cases hi : b.direction i with
  | forward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward L hL _ _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a b i).trans hi),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward L hL T i hi]
    exact map_heq L (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T i.castSucc)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T i.succ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.direction_right_heq S T .forward i hi)
  | backward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward L hL _ _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a b i).trans hi),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward L hL T i hi]
    exact iso_inv_heq (congrArg L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T i.succ))
      (congrArg L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T i.castSucc)) _ _
      (map_unop_heq L (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T i.castSucc)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T i.succ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.direction_right_heq S T .backward i hi))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.edge_append_right_heq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppendEdges (edge_append_right_heq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppendEdges
