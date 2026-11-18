module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurAction

/-!
模型。文献の定義との比較は後で
# Schur 作用の arity の等式による移送

概要：Berger–Moerdijk §1 の代数公理で係数と入力の長さの表示を同時に変える。
方針：arity の等式を消去し、係数と入力の恒等射を相殺する。
規約：係数と入力テンソル冪の両方を同じ等式で移送する。
使われ方：先頭ブロックでの結合則を既存の部分合成の arity の表記へ戻す。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：Schur 作用は係数と入力の同時の arity の移送を相殺する（Berger–Moerdijk §1）。
方針：arity の等式を消去して恒等射を簡約する。
規約：底の Schur 対象は変えない。
使われ方：二通りの arity の和の表示の間で作用の式を移す。 -/
@[reassoc]
lemma schurAction_index_eq (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) {m n : ℕ} (h : m = n) :
    (eqToHom (congrArg P.arity h) ⊗ₘ
      eqToHom (congrArg (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)) h)) ≫
      P.schurAction K n = P.schurAction K m := by
  subst n
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight, Category.id_comp]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
