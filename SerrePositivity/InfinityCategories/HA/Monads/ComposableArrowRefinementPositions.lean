module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementFaces

/-!
概要：実細分で挿入した対象と、その右の実射を全実鎖から取り出す。
方針：元の実再帰を先頭と尾部で照合する。
規約：全鎖の指定位置の実対象と実射を保持する。
使われ方：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の退化の排除。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：細分で挿入した頂点の実対象は指定した中間対象。
方針：位置で再帰して実precompの対象を計算する。規約：対象の実等式。
使われ方：Riehl–Verity §4.1の左の退化の排除。 -/
lemma composableArrowRefinement_middle :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      (composableArrowRefinement F k B q g).obj k.succ.castSucc = B := by
  intro n
  induction n with
  | zero =>
    intro F k B q g
    have hk : k = 0 := by apply Fin.ext; have hi := k.isLt; change k.val = 0; omega
    subst k
    rw [composableArrowRefinement_zero]
    rfl
  | succ n ih =>
    intro F k
    refine Fin.cases ?_ (fun k => ?_) k
    · intro B q g
      rw [composableArrowRefinement_zero]
      rfl
    · intro B q g
      erw [composableArrowRefinement_succ]
      change (composableArrowRefinement F.δ₀ k B q g).obj k.succ.castSucc = B
      exact ih F.δ₀ k B q g

/-- 概要：細分で挿入した頂点の右の実射は指定した右因子。
方針：実precompの尾部の射を再帰して照合する。規約：対象の等式の前は異種等式で保持する。
使われ方：Riehl–Verity §4.1の右の退化の排除。 -/
lemma composableArrowRefinement_right_edge :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      HEq ((composableArrowRefinement F k B q g).map
        (homOfLE (Fin.castSucc_le_succ k.succ))) g := by
  intro n
  induction n with
  | zero =>
    intro F k B q g
    have hk : k = 0 := by apply Fin.ext; have hi := k.isLt; change k.val = 0; omega
    subst k
    rw [composableArrowRefinement_zero]
    rfl
  | succ n ih =>
    intro F k
    refine Fin.cases ?_ (fun k => ?_) k
    · intro B q g
      rw [composableArrowRefinement_zero]
      rfl
    · intro B q g
      erw [composableArrowRefinement_succ]
      change HEq ((composableArrowRefinement F.δ₀ k B q g).map
        (homOfLE (Fin.castSucc_le_succ k.succ))) g
      exact ih F.δ₀ k B q g

end SerrePositivity.InfinityCategories.HA.Monads
