module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WeakArrowCancellationRows
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitIdentityPoint
public import Mathlib.Tactic.FinCases

/-!
# 往復列の恒等行と元の空語からの挿入

概要：二列の恒等行が元の空語の作用で得られることを示す。
方針：三頂点と二つの空区間の恒等射を照合する。
規約：余極限の単位との一致に元の語の標準射を使う。
使われ方：往復のホモトピーの単位端点の回収。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.WeakArrow
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

omit [W.IsMultiplicative] in
lemma empty_segment_identity (d : Direction) (X : C) (p q : Fin (Word.empty.length + 1))
    (hpq : p ≤ q) (hd : ∀ i : Fin Word.empty.length,
      p.val ≤ i.val → i.val < q.val → Word.empty.direction i = d) :
    HEq (Segment.map d (emptyObj W X) p q hpq hd) (𝟙 (Direction.vertex d X)) := by
  have he : p = q := @Subsingleton.elim (Fin 1) inferInstance _ _
  subst q
  exact heq_of_eq (Segment.map_refl d (emptyObj W X) p hd)

omit [W.IsMultiplicative] in
lemma empty_column_identity (d : Direction) (X : C) {I : Type*} (p q : I)
    (a b : Fin (Word.empty.length + 1)) (hab : a ≤ b)
    (hd : ∀ i : Fin Word.empty.length,
      a.val ≤ i.val → i.val < b.val → Word.empty.direction i = d) :
    HEq (WordAction.columnAux (fun _ : I => X) d p q
      (Segment.map d (emptyObj W X) a b hab hd)) (𝟙 X) := by
  cases d with
  | forward => exact empty_segment_identity W .forward X a b hab hd
  | backward =>
    exact heq_of_eq (congrArg Quiver.Hom.unop
      (eq_of_heq (empty_segment_identity W .backward X a b hab hd)))

lemma empty_arrow_identity (w : Word) (X : C) (i : Fin w.length) :
    HEq ((WordAction.obj (Word.fromEmpty w) (emptyObj W X)).arrow i) (𝟙 X) :=
  empty_column_identity W (w.direction i) X i.castSucc i.succ _ _ _ _

lemma sourceUnit_arrow (X : C)
    (i : Fin (Word.append (Word.single .forward) (Word.single .backward)).length) :
    HEq ((sourceUnit (W := W) X).arrow i) (𝟙 X) := by
  cases i using Fin.addCases with
  | left i =>
    exact (ZigzagAppend.arrow_left_heq (ForwardZigzag.obj (W := W) (𝟙 X))
      (BackwardZigzag.obj (𝟙 X) (W.id_mem X)) i).trans (by
        change Fin 1 at i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl)
  | right i =>
    exact (ZigzagAppend.arrow_right_heq (ForwardZigzag.obj (W := W) (𝟙 X))
      (BackwardZigzag.obj (𝟙 X) (W.id_mem X)) i).trans (by
        change Fin 1 at i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl)

lemma targetUnit_arrow (Y : C)
    (i : Fin (Word.append (Word.single .backward) (Word.single .forward)).length) :
    HEq ((targetUnit (W := W) Y).arrow i) (𝟙 Y) := by
  cases i using Fin.addCases with
  | left i =>
    exact (ZigzagAppend.arrow_left_heq (BackwardZigzag.obj (𝟙 Y) (W.id_mem Y))
      (ForwardZigzag.obj (W := W) (𝟙 Y)) i).trans (by
        change Fin 1 at i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl)
  | right i =>
    exact (ZigzagAppend.arrow_right_heq (BackwardZigzag.obj (𝟙 Y) (W.id_mem Y))
      (ForwardZigzag.obj (W := W) (𝟙 Y)) i).trans (by
        change Fin 1 at i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl)

lemma empty_sourceUnit (X : C) :
    WordAction.obj (Word.fromEmpty
      (Word.append (Word.single .forward) (Word.single .backward))) (emptyObj W X) =
      sourceUnit (W := W) X := by
  apply Zigzag.object_ext
  · intro j
    change Fin 3 at j
    fin_cases j <;> rfl
  · intro i
    exact (empty_arrow_identity W _ X i).trans (sourceUnit_arrow W X i).symm

lemma empty_targetUnit (Y : C) :
    WordAction.obj (Word.fromEmpty
      (Word.append (Word.single .backward) (Word.single .forward))) (emptyObj W Y) =
      targetUnit (W := W) Y := by
  apply Zigzag.object_ext
  · intro j
    change Fin 3 at j
    fin_cases j <;> rfl
  · intro i
    exact (empty_arrow_identity W _ Y i).trans (targetUnit_arrow W Y i).symm

end SerrePositivity.EInfinity.Hammock.WeakArrow
