module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerHeads

/-!
模型。文献の定義との比較は後で
# 先頭交換後の連結射の移送

概要：Berger–Moerdijk §1 の先頭交換の連結射を、先頭二ブロックの展開へ移す。
方針：有限族の対象と総和の比較を使い、連結の添字の等式による移送を計算する。
規約：局所的な可約性の設定により有限添字を先に計算し、複体の構成の展開を抑える。
使われ方：有限テンソル族の連結と先頭の隣接交換を両立させる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily
attribute [local irreducible] _root_.SerrePositivity.TensorPowers.power _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso

set_option maxHeartbeats 500000 in
-- 具体的な添字族と有限テンソルの定義の比較に限って上限を増やす。
/-- 概要：具体的な交換族の連結を先頭二つで展開する（Berger–Moerdijk §1）。
方針：連結の二ブロックの展開を始域の等式の射に合成する。
規約：始域と終域の移送は独立した補題の等式を使う。
使われ方：先頭交換後の連結の比較で複体の大きな定義を展開し直すことを避ける。 -/
lemma tensorPowerFirstSwapFamily_expand (K : Complex A) (n : ℕ) (s : Fin (n + 2) → ℕ) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily_obj K n s).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 2) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily n s)).hom ≫
        eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily_sum n s)) =
      (power K (s 1) ◁ (power K (s 0) ◁
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun i => s i.succ.succ)).hom)) ≫
        (power K (s 1) ◁ (appendIso K (s 0) (∑ i : Fin n, s i.succ.succ)).hom) ≫
        (appendIso K (s 1) (s 0 + ∑ i : Fin n, s i.succ.succ)).hom := by
  have h := congrArg (fun f => eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily_obj K n s).symm ≫ f)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_two K n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily n s))
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily, Fin.cases_zero, Fin.cases_succ] at h
  conv at h =>
    rhs
    erw [eqToHom_refl, Category.id_comp]
  exact h

/-- 概要：先頭交換後の連結を交換した二つの先頭の式で表す（Berger–Moerdijk §1）。
方針：隣接互換を具体的な交換族と比較し、その連結の展開を使う。
規約：総和の終域は交換した二つと残りの右括弧の和とする。
使われ方：有限テンソル族の先頭交換を三ブロックの交換に接続する。 -/
lemma tensorPowerFamilyIso_firstSwap_transport (K : Complex A)
    (n : ℕ) (s : Fin (n + 2) → ℕ) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n (fun i => power K (s i))).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 2)
          (fun i => s (adjacentTransposition (0 : Fin (n + 1)) i))).hom ≫
        eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_firstSwap n s)) =
      (power K (s 1) ◁ (power K (s 0) ◁
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun i => s i.succ.succ)).hom)) ≫
        (power K (s 1) ◁ (appendIso K (s 0) (∑ i : Fin n, s i.succ.succ)).hom) ≫
        (appendIso K (s 1) (s 0 + ∑ i : Fin n, s i.succ.succ)).hom := by
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_compare K (n + 2) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily_eq n s)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily_obj K n s)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n (fun i => power K (s i)))
    (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily_sum n s))
    (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_firstSwap n s))).trans
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily_expand K n s)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
