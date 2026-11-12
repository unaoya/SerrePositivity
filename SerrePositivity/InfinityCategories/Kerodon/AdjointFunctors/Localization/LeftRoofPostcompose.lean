module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofRightIdentity
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision

/-!
# 元の二列 roof の後合成の回収

概要：元の射を末尾へ連結し、同方向の二列を合成すると元の後合成の roof になる。
方針：同じ語の射と元の区間合成を使う。
規約：元の全頂点・列・端点を保持する。
使われ方：source frame 比較の終域変数の自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

abbrev postWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)

def postCollapse : postWord ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word where
  orderHom := ⟨(![0, 1, 1] : Fin 3 → Fin 2), by decide⟩
  direction_eq i := by fin_cases i <;> rfl

lemma postCollapse_cut (j : Fin 3) : postCollapse.cut j = (![0, 1, 3] : Fin 3 → Fin 4) j := by
  fin_cases j <;> decide

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y Z U : C}

lemma postCollapse_obj (p : U ⟶ X) (hp : W p) (f : U ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj postCollapse (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj g)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp (f ≫ g) := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) g)
  have ha0 : S.arrow (0 : Fin 3) = p :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj g) (0 : Fin 2))
  have ha1 : S.arrow (1 : Fin 3) = f :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj g) (1 : Fin 2))
  have ha2 : S.arrow (2 : Fin 3) = g :=
    eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p hp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj g) (0 : Fin 1))
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S 0 1 (by decide)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction (w := postWord) .backward (0 : Fin 3) rfl) = p.op :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .backward S (0 : Fin 3) rfl).trans
      ((eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backward_arrow_heq S (0 : Fin 3) rfl)).trans
        (congrArg (fun a : U ⟶ X => a.op) ha0))
  have h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S 1 2 (by decide)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction (w := postWord) .forward (1 : Fin 3) rfl) = f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S (1 : Fin 3) rfl).trans
      ((eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq S (1 : Fin 3) rfl)).trans ha1)
  have h2 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S 2 3 (by decide)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction (w := postWord) .forward (2 : Fin 3) rfl) = g :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S (2 : Fin 3) rfl).trans
      ((eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_arrow_heq S (2 : Fin 3) rfl)).trans ha2)
  have hd : ∀ i : Fin 3, 1 ≤ i.val → i.val < 3 → postWord.direction i = .forward := by
    intro i hi _
    fin_cases i
    · change 1 ≤ (0 : ℕ) at hi
      omega
    · rfl
    · rfl
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S 1 3 (by decide) hd = f ≫ g :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp .forward S 1 2 3 (by decide) (by decide) hd).trans
      (congrArg₂ (fun a b => a ≫ b) h1 h2)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    change S.vertex (postCollapse.cut j) = _
    rw [postCollapse_cut]
    fin_cases j <;> rfl
  · intro i
    fin_cases i
    · apply heq_of_eq
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S 0 1 _ _).unop = p
      exact congrArg (fun a : Opposite.op X ⟶ Opposite.op U => a.unop) hb
    · exact heq_of_eq hc

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
