module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppendEdges
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagPathIntervalValue

/-!
# 元の連結の値の射列の左右への制限

概要：連結の値の射列を左右の頂点へ制限すると元の同じ値の射列を得る。
方針：元の全頂点と隣接列の回収を ComposableArrows.ext に渡す。
規約：接合点を含む元の端点移送を保持する。
使われ方：元の値の合成則。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z : C}

def appendLeftFunctor (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : Fin (a.length + 1) ⥤ Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1) :=
  (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b, fun _ _ h => h⟩ :
    Fin (a.length + 1) →o Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)).toFunctor

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.appendLeftFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (appendLeftFunctor)


def appendRightFunctor (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : Fin (b.length + 1) ⥤ Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1) :=
  (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b, fun _ _ h => Nat.add_le_add_left h a.length⟩ :
    Fin (b.length + 1) →o Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)).toFunctor

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.appendRightFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (appendRightFunctor)


lemma path_append_left (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) :
    appendLeftFunctor a b ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S := by
  apply ComposableArrows.ext (fun i => congrArg L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T i))
  intro i hi
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  change HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).map
    (homOfLE (Fin.castSucc_le_succ ((⟨i, hi⟩ : Fin a.length).castAdd b.length))))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S).map (homOfLE (Fin.castSucc_le_succ ⟨i, hi⟩)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_map_adjacent, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_map_adjacent]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppendEdges.edge_append_left_heq L hL S T ⟨i, hi⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.path_append_left export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (path_append_left)


lemma path_append_right (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) :
    appendRightFunctor a b ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL T := by
  apply ComposableArrows.ext (fun i => congrArg L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T i))
  intro i hi
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  change HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).map
    (homOfLE (Fin.castSucc_le_succ ((⟨i, hi⟩ : Fin b.length).natAdd a.length))))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL T).map (homOfLE (Fin.castSucc_le_succ ⟨i, hi⟩)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_map_adjacent, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_map_adjacent]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueAppendEdges.edge_append_right_heq L hL S T ⟨i, hi⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.path_append_right export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (path_append_right)


lemma path_append_left_hom (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).map
      (homOfLE (Fin.zero_le (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b (Fin.last a.length)))) =
    eqToHom (congrArg L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T 0)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S).hom ≫
      eqToHom (congrArg L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T (Fin.last a.length))).symm :=
  CategoryTheory.Functor.congr_hom (path_append_left L hL S T)
    (homOfLE (Fin.zero_le (Fin.last a.length)))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.path_append_left_hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (path_append_left_hom)


lemma path_append_right_hom (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).map
      (homOfLE (Fin.le_last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b 0))) =
    eqToHom (congrArg L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T 0)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL T).hom ≫
      eqToHom (congrArg L.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T (Fin.last b.length))).symm :=
  CategoryTheory.Functor.congr_hom (path_append_right L hL S T)
    (homOfLE (Fin.zero_le (Fin.last b.length)))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.path_append_right_hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (path_append_right_hom)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
