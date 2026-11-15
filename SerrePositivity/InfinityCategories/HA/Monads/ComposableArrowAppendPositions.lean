module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowAppendFaces

/-!
概要：終端へ挿入した実射と、それ以前の全実対象・辺を元の実鎖から回収する。
方針：終端辺は実再帰、他は最後の面の全関手の等式を使う。
規約：実射の対象の輸送を異種等式で保持する。
使われ方：Riehl–Verity Lemma 4.1.4の最後の深さの親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の非退化性の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：終端へ挿入した全実鎖の最後の辺は指定した実射。
方針：実precompの尾部を再帰する。規約：全ての実長さ。
使われ方：Riehl–Verity Lemma 4.1.4の最後の辺の非退化性。 -/
lemma composableArrowAppend_last_edge :
    ∀ (n : ℕ) (F : ComposableArrows C n) (B : C) (f : F.obj (Fin.last n) ⟶ B),
      HEq ((composableArrowAppend F B f).map
        (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) f := by
  intro n
  induction n with
  | zero =>
    intro F B f
    rw [composableArrowAppend_zero]
    rfl
  | succ n ih =>
    intro F B f
    erw [composableArrowAppend_succ]
    change HEq ((composableArrowAppend F.δ₀ B f).map
      (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) f
    exact ih F.δ₀ B f

/-- 概要：終端挿入より前の全対象は元の対象。
方針：最後の面の全関手の等式を各実頂点で評価する。規約：元の対象の等式。
使われ方：Riehl–Verity Lemma 4.1.4の実親の原子性の検収。 -/
lemma composableArrowAppend_before_obj {n : ℕ} (F : ComposableArrows C n) (B : C)
    (f : F.obj (Fin.last n) ⟶ B) (i : Fin (n + 1)) :
    (composableArrowAppend F B f).obj i.castSucc = F.obj i := by
  have ho := CategoryTheory.Functor.congr_obj (composableArrowAppend_face_last n F B f) i
  change (composableArrowAppend F B f).obj ((Fin.last (n + 1)).succAbove i) = F.obj i at ho
  rw [Fin.succAbove_last] at ho
  exact ho

/-- 概要：終端挿入より前の全隣接実辺は元の実辺。
方針：最後の面の全関手の等式を実射で評価する。規約：元の全実射の異種等式。
使われ方：Riehl–Verity Lemma 4.1.4の実親の非退化性の検収。 -/
lemma composableArrowAppend_before_edge {n : ℕ} (F : ComposableArrows C (n + 1)) (B : C)
    (f : F.obj (Fin.last (n + 1)) ⟶ B) (j : Fin (n + 1)) :
    HEq ((composableArrowAppend F B f).map
      (homOfLE (Fin.castSucc_le_succ j.castSucc)))
      (F.map (homOfLE (Fin.castSucc_le_succ j))) := by
  have hm := CategoryTheory.Functor.hcongr_hom (composableArrowAppend_face_last (n + 1) F B f)
    (homOfLE (Fin.castSucc_le_succ j))
  change HEq ((composableArrowAppend F B f).map
    ((finiteChainFaceIndex (Fin.last (n + 2))).map
      (homOfLE (Fin.castSucc_le_succ j)))) _ at hm
  have hi : finiteChainFaceIndex (Fin.last (n + 2)) = Fin.castSuccFunctor (n + 2) := by
    refine CategoryTheory.Functor.ext (fun i => Fin.succAbove_last_apply i) ?_
    intro a b g
    exact Subsingleton.elim _ _
  rw [hi] at hm
  exact hm

end SerrePositivity.InfinityCategories.HA.Monads
