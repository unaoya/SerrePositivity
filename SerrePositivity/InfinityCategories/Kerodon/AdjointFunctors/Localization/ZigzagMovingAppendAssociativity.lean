module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendAssociativityObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramWordChange
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramAppend
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramExt

/-!
# 動く全図式の連結の結合則

概要：局所端点も動く三図式の連結を、元の語の結合等式で照合する。
方針：元の全対象の結合則と三部分の全縦成分の回収を使う。
規約：空の語と両接合点を含み、元の全図式を保持する。
使われ方：元の refinedDiagram の括弧を保った三列圧縮。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendAssociativity
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}
  {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z V X' Y' Z' V' : C}
  {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} {S' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X' Y'}
  {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z} {T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y' Z'}
  {U : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W c Z V} {U' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W c Z' V'}

lemma app_assoc_heq (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S S') (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T T')
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom U U')
    (hfg : HEq (f.app (Fin.last a.length)) (g.app 0))
    (hgh : HEq (g.app (Fin.last b.length)) (h.app 0))
    (i : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) c).length + 1))
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append b c)).length + 1)) (hij : i.val = j.val) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map f g hfg) h i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map g h hgh) j) := by
  let fg := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map f g hfg
  let gh := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map g h hgh
  have hfg_h : HEq (fg.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length)) (h.app 0) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq f g hfg (Fin.last b.length)).trans hgh
  have hf_gh : HEq (f.app (Fin.last a.length)) (gh.app 0) :=
    hfg.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq g h 0).symm
  by_cases ha : i.val ≤ a.length
  · let k : Fin (a.length + 1) := ⟨i.val, by omega⟩
    have hi : i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) c (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b k) := Fin.ext rfl
    have hj : j = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append b c) k := Fin.ext hij.symm
    exact (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_index_heq fg h hi).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq fg h _)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq f g k)).trans
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_index_heq f gh hj).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq f gh k)).symm
  · by_cases hb : i.val ≤ a.length + b.length
    · let k : Fin (b.length + 1) := ⟨i.val - a.length, by omega⟩
      have hi : i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) c (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b k) :=
        Fin.ext (by dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, k]; omega)
      have hj : j = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append b c) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex b c k) :=
        Fin.ext (by dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, k]; omega)
      exact (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_index_heq fg h hi).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq fg h _)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq f g hfg k)).trans
          (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_index_heq f gh hj).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq f gh hf_gh _)).trans
            (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq g h k)).symm
    · let k : Fin (c.length + 1) := ⟨i.val - (a.length + b.length), by
        have := i.isLt
        change i.val < a.length + b.length + c.length + 1 at this
        omega⟩
      have hi : i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) c k :=
        Fin.ext (by dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, k]; omega)
      have hj : j = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append b c) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex b c k) :=
        Fin.ext (by dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, k]; omega)
      exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_index_heq fg h hi).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq fg h hfg_h k)).trans
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_index_heq f gh hj).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq f gh hf_gh _)).trans
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq g h hgh k)).symm


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendAssociativity
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendAssociativity
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B E L : D ⥤ C}

lemma changeWord_append_assoc (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b B E) (H : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W c E L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_assoc a b c) ((F.append G).append H) = F.append (G.append H) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ext
  · intro d
    exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_obj_heq _ _ d).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_assoc_heq (F.obj d) (G.obj d) (H.obj d)))
  · intro d e f j
    let i : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) c).length + 1) := ⟨j.val, by
      have hj := j.isLt
      change j.val < a.length + (b.length + c.length) + 1 at hj
      change j.val < a.length + b.length + c.length + 1
      omega⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_map_app_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_assoc a b c) _ f i j rfl).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendAssociativity.app_assoc_heq (F.map f) (G.map f) (H.map f)
        ((F.last f).trans (G.first f).symm) ((G.last f).trans (H.first f).symm) i j rfl)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendAssociativity (changeWord_append_assoc)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendAssociativity
