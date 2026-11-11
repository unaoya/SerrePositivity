module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WeakArrowCancellationRows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitIdentityPoint
public import Mathlib.Tactic.FinCases

/-!
# 往復列の恒等行と元の空語からの挿入

概要：二列の恒等行が元の空語の作用で得られることを示す。
方針：三頂点と二つの空区間の恒等射を照合する。
規約：余極限の単位との一致に元の語の標準射を使う。
使われ方：往復のホモトピーの単位端点の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

omit [W.IsMultiplicative] in
lemma empty_segment_identity (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (X : C) (p q : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty.length + 1))
    (hpq : p ≤ q) (hd : ∀ i : Fin _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty.length,
      p.val ≤ i.val → i.val < q.val → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty.direction i = d) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) p q hpq hd) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d X)) := by
  have he : p = q := @Subsingleton.elim (Fin 1) inferInstance _ _
  subst q
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_refl d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) p hd)

omit [W.IsMultiplicative] in
lemma empty_column_identity (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (X : C) {I : Type*} (p q : I)
    (a b : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty.length + 1)) (hab : a ≤ b)
    (hd : ∀ i : Fin _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty.length,
      a.val ≤ i.val → i.val < b.val → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty.direction i = d) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.columnAux (fun _ : I => X) d p q
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) a b hab hd)) (𝟙 X) := by
  cases d with
  | forward => exact empty_segment_identity W .forward X a b hab hd
  | backward =>
    exact heq_of_eq (congrArg Quiver.Hom.unop
      (eq_of_heq (empty_segment_identity W .backward X a b hab hd)))

lemma empty_arrow_identity (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X : C) (i : Fin w.length) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.fromEmpty w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X)).arrow i) (𝟙 X) :=
  empty_column_identity W (w.direction i) X i.castSucc i.succ _ _ _ _

lemma sourceUnit_arrow (X : C)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)).length) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceUnit (W := W) X).arrow i) (𝟙 X) := by
  cases i using Fin.addCases with
  | left i =>
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (𝟙 X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (𝟙 X) (W.id_mem X)) i).trans (by
        change Fin 1 at i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl)
  | right i =>
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (𝟙 X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (𝟙 X) (W.id_mem X)) i).trans (by
        change Fin 1 at i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl)

lemma targetUnit_arrow (Y : C)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).length) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetUnit (W := W) Y).arrow i) (𝟙 Y) := by
  cases i using Fin.addCases with
  | left i =>
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (𝟙 Y) (W.id_mem Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (𝟙 Y)) i).trans (by
        change Fin 1 at i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl)
  | right i =>
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (𝟙 Y) (W.id_mem Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (𝟙 Y)) i).trans (by
        change Fin 1 at i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl)

lemma empty_sourceUnit (X : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.fromEmpty
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceUnit (W := W) X := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    change Fin 3 at j
    fin_cases j <;> rfl
  · intro i
    exact (empty_arrow_identity W _ X i).trans (sourceUnit_arrow W X i).symm

lemma empty_targetUnit (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.fromEmpty
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W Y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetUnit (W := W) Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    change Fin 3 at j
    fin_cases j <;> rfl
  · intro i
    exact (empty_arrow_identity W _ Y i).trans (targetUnit_arrow W Y i).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
