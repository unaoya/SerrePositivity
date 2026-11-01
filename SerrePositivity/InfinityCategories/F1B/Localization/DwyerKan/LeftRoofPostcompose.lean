module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.LeftRoofRightIdentity
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardZigzag
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SegmentSubdivision

/-!
# 元の二列 roof の後合成の回収

概要：元の射を末尾へ連結し、同方向の二列を合成すると元の後合成の roof になる。
方針：同じ語の射と元の区間合成を使う。
規約：元の全頂点・列・端点を保持する。
使われ方：source frame 比較の終域変数の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.LeftRoof
open CategoryTheory

abbrev postWord : Word := Word.append word (Word.single .forward)

def postCollapse : postWord ⟶ word where
  orderHom := ⟨(![0, 1, 1] : Fin 3 → Fin 2), by decide⟩
  direction_eq i := by fin_cases i <;> rfl

lemma postCollapse_cut (j : Fin 3) : postCollapse.cut j = (![0, 1, 3] : Fin 3 → Fin 4) j := by
  fin_cases j <;> decide

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y Z U : C}

lemma postCollapse_obj (p : U ⟶ X) (hp : W p) (f : U ⟶ Y) (g : Y ⟶ Z) :
    WordAction.obj postCollapse (ZigzagAppend.obj (obj W p hp f) (ForwardZigzag.obj g)) =
      obj W p hp (f ≫ g) := by
  let S := ZigzagAppend.obj (obj W p hp f) (ForwardZigzag.obj (W := W) g)
  have ha0 : S.arrow (0 : Fin 3) = p :=
    eq_of_heq (ZigzagAppend.arrow_left_heq (obj W p hp f) (ForwardZigzag.obj g) (0 : Fin 2))
  have ha1 : S.arrow (1 : Fin 3) = f :=
    eq_of_heq (ZigzagAppend.arrow_left_heq (obj W p hp f) (ForwardZigzag.obj g) (1 : Fin 2))
  have ha2 : S.arrow (2 : Fin 3) = g :=
    eq_of_heq (ZigzagAppend.arrow_right_heq (obj W p hp f) (ForwardZigzag.obj g) (0 : Fin 1))
  have hb : Segment.map .backward S 0 1 (by decide)
      (Segment.adjacent_direction (w := postWord) .backward (0 : Fin 3) rfl) = p.op :=
    (Segment.map_adjacent .backward S (0 : Fin 3) rfl).trans
      ((eq_of_heq (Direction.backward_arrow_heq S (0 : Fin 3) rfl)).trans
        (congrArg (fun a : U ⟶ X => a.op) ha0))
  have h1 : Segment.map .forward S 1 2 (by decide)
      (Segment.adjacent_direction (w := postWord) .forward (1 : Fin 3) rfl) = f :=
    (Segment.map_adjacent .forward S (1 : Fin 3) rfl).trans
      ((eq_of_heq (Direction.forward_arrow_heq S (1 : Fin 3) rfl)).trans ha1)
  have h2 : Segment.map .forward S 2 3 (by decide)
      (Segment.adjacent_direction (w := postWord) .forward (2 : Fin 3) rfl) = g :=
    (Segment.map_adjacent .forward S (2 : Fin 3) rfl).trans
      ((eq_of_heq (Direction.forward_arrow_heq S (2 : Fin 3) rfl)).trans ha2)
  have hd : ∀ i : Fin 3, 1 ≤ i.val → i.val < 3 → postWord.direction i = .forward := by
    intro i hi _
    fin_cases i
    · change 1 ≤ (0 : ℕ) at hi
      omega
    · rfl
    · rfl
  have hc : Segment.map .forward S 1 3 (by decide) hd = f ≫ g :=
    (Segment.map_comp .forward S 1 2 3 (by decide) (by decide) hd).trans
      (congrArg₂ (fun a b => a ≫ b) h1 h2)
  apply Zigzag.object_ext
  · intro j
    change S.vertex (postCollapse.cut j) = _
    rw [postCollapse_cut]
    fin_cases j <;> rfl
  · intro i
    fin_cases i
    · apply heq_of_eq
      change (Segment.map .backward S 0 1 _ _).unop = p
      exact congrArg (fun a : Opposite.op X ⟶ Opposite.op U => a.unop) hb
    · exact heq_of_eq hc

end SerrePositivity.EInfinity.Hammock.LeftRoof
