module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
概要：実有限鎖の終点へ一つの実射を挿入し、一つ高次の全実関手を構成する。
方針：尾部に再帰し、元の先頭辺を対象の輸送を含めて戻す。
規約：新しい実全鎖と両端の等式を同時に作る。
使われ方：Riehl–Verity Lemma 4.1.4の始点plusの実親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の終端の実射の挿入。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：終点へ実射を挿入した全実鎖と両端の等式。
方針：長さ0は一辺、正の長さは尾部の構成に元の先頭を戻す。
規約：実関手の存在を引数にしない。使われ方：Riehl–Verity Lemma 4.1.4の実親。 -/
def composableArrowAppendData :
    ∀ (n : ℕ) (F : ComposableArrows C n) (B : C) (_f : F.obj (Fin.last n) ⟶ B),
      {G : ComposableArrows C (n + 1) // G.obj 0 = F.obj 0 ∧
        G.obj (Fin.last (n + 1)) = B} := by
  intro n
  induction n with
  | zero =>
    intro F B f
    exact ⟨ComposableArrows.mk₁ f, rfl, rfl⟩
  | succ n ih =>
    intro F B f
    let r := ih F.δ₀ B f
    exact ⟨r.val.precomp (F.map' 0 1 ≫ eqToHom r.property.1.symm), rfl, r.property.2⟩

/-- 概要：指定した終端実射を挿入した一つ高次の全実鎖。
方針：実再帰の出力を取る。規約：元の全射を保持する。
使われ方：Riehl–Verity Lemma 4.1.4の最後の深さでの実親。 -/
def composableArrowAppend {n : ℕ} (F : ComposableArrows C n) (B : C)
    (f : F.obj (Fin.last n) ⟶ B) : ComposableArrows C (n + 1) :=
  (composableArrowAppendData n F B f).val

/-- 概要：終端への挿入は実始点を保つ。
方針：構成と同時に得た等式を取る。規約：対象の実等式。
使われ方：Riehl–Verity Lemma 4.1.4の実原子の始端。 -/
lemma composableArrowAppend_first {n : ℕ} (F : ComposableArrows C n) (B : C)
    (f : F.obj (Fin.last n) ⟶ B) : (composableArrowAppend F B f).obj 0 = F.obj 0 :=
  (composableArrowAppendData n F B f).property.1

/-- 概要：終端への挿入の実終点は指定した対象。
方針：構成と同時に得た等式を取る。規約：対象の実等式。
使われ方：Riehl–Verity Lemma 4.1.4の実原子の終端。 -/
lemma composableArrowAppend_last {n : ℕ} (F : ComposableArrows C n) (B : C)
    (f : F.obj (Fin.last n) ⟶ B) :
    (composableArrowAppend F B f).obj (Fin.last (n + 1)) = B :=
  (composableArrowAppendData n F B f).property.2

/-- 概要：一点の実鎖への終端挿入は指定した一辺。
方針：実再帰の基底を展開する。規約：全関手の等式。
使われ方：Riehl–Verity Lemma 4.1.4の実面の基底。 -/
lemma composableArrowAppend_zero (F : ComposableArrows C 0) (B : C)
    (f : F.obj (Fin.last 0) ⟶ B) :
    composableArrowAppend F B f = ComposableArrows.mk₁ f := by
  rfl

/-- 概要：終端挿入の尾部は尾部への終端挿入。
方針：実再帰の一段を展開する。規約：先頭辺の対象の輸送を保持する。
使われ方：Riehl–Verity Lemma 4.1.4の実面の再帰。 -/
lemma composableArrowAppend_succ {n : ℕ} (F : ComposableArrows C (n + 1)) (B : C)
    (f : F.obj (Fin.last (n + 1)) ⟶ B) :
    composableArrowAppend F B f = (composableArrowAppend F.δ₀ B f).precomp
      (F.map' 0 1 ≫ eqToHom (composableArrowAppend_first F.δ₀ B f).symm) := by
  rfl

end SerrePositivity.InfinityCategories.HA.Monads
