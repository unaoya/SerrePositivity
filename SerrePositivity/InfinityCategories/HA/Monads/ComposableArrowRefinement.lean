module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
概要：実有限鎖の指定した一辺へ二つの実射と中間対象を挿入する。
方針：指定位置まで再帰し、元の先頭の射を保ちながら実precompで組み立てる。
規約：出力は全ての射を持つ実関手で、両端の対象の等式も構成する。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の実全単体、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実射の細分の挿入。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：指定辺に実中間対象を挿入した実鎖と両端の対象の等式。
方針：先頭の辺なら二回precompし、それ以外は尾部を再帰して元の先頭を戻す。
規約：新しい実関手の存在を引数にしない。使われ方：Riehl–Verity §4.1の実親の鎖。 -/
def composableArrowRefinementData :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (_q : F.obj k.castSucc ⟶ B) (_g : B ⟶ F.obj k.succ),
      {G : ComposableArrows C (n + 2) //
        G.obj 0 = F.obj 0 ∧ G.obj (Fin.last (n + 2)) = F.obj (Fin.last (n + 1))} := by
  intro n
  induction n with
  | zero =>
    intro F k B q g
    have hk : k = 0 := by
      apply Fin.ext
      have hi := k.isLt
      change k.val = 0
      omega
    subst k
    exact ⟨(F.δ₀.precomp g).precomp q, rfl, rfl⟩
  | succ n ih =>
    intro F k
    refine Fin.cases ?_ (fun k => ?_) k
    · intro B q g
      exact ⟨(F.δ₀.precomp g).precomp q, rfl, rfl⟩
    · intro B q g
      let r := ih F.δ₀ k B q g
      exact ⟨r.val.precomp (F.map' 0 1 ≫ eqToHom r.property.1.symm), rfl, r.property.2⟩

/-- 概要：指定辺へ実射を挿入した実全鎖。
方針：構成した全関手を取り出す。規約：両端は元の実鎖の対象。
使われ方：Riehl–Verity §4.1の親の全単体。 -/
def composableArrowRefinement {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
    (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ) :
    ComposableArrows C (n + 2) := (composableArrowRefinementData n F k B q g).val

/-- 概要：細分した実鎖の始点は元の始点。
方針：実再帰と同時に構成した等式を使う。規約：対象の実等式。
使われ方：Riehl–Verity §4.1の原子の始端の保存。 -/
lemma composableArrowRefinement_first {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
    (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ) :
    (composableArrowRefinement F k B q g).obj 0 = F.obj 0 :=
  (composableArrowRefinementData n F k B q g).property.1

/-- 概要：細分した実鎖の終点は元の終点。
方針：実再帰と同時に構成した等式を使う。規約：対象の実等式。
使われ方：Riehl–Verity §4.1の原子の終端の保存。 -/
lemma composableArrowRefinement_last {n : ℕ} (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
    (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ) :
    (composableArrowRefinement F k B q g).obj (Fin.last (n + 2)) = F.obj (Fin.last (n + 1)) :=
  (composableArrowRefinementData n F k B q g).property.2

end SerrePositivity.InfinityCategories.HA.Monads
