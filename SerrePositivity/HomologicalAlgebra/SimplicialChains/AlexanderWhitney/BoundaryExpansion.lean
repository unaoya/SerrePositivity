module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.BoundaryCuts
public import Mathlib.Algebra.BigOperators.Fin

/-!
# AW 境界の前半・後半への分割

概要：Berger–Fresse §1.1.4 の AW 対角に入力の微分を適用した式を展開する。
方針：交代面和を切断点の前後で分け、各因子の面写像へ移す。
規約：切断点は前半の最後の頂点と後半の最初の頂点に共通する。
使われ方：テンソル積の微分との比較で現れる二つの有限和を同定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory
open scoped _root_.Simplicial _root_.TensorProduct

private lemma sum_split {M : Type*} [AddCommMonoid M] (p q : ℕ)
    (f : Fin (p + q + 2) → M) :
    (∑ i, f i) =
      (∑ i : Fin (p + 1), f ⟨i.val, by omega⟩) +
        ∑ j : Fin (q + 1), f ⟨p + 1 + j.val, by omega⟩ := by
  calc
    (∑ i, f i) = ∑ i : Fin ((p + 1) + (q + 1)), f ⟨i.val, by omega⟩ :=
      Fintype.sum_equiv (finCongr (by omega)) _ _ (by intro i; rfl)
    _ = _ := by rw [Fin.sum_univ_add]; rfl

variable (A : Type u) [CommRing A]

/-- 概要：AW 成分に入力の微分を適用した生成元公式（Berger–Fresse §1.1.4）。
方針：全ての面を前半の面と後半の面に分割し、切断公式を適用する。
規約：前半では最後の面を、後半では最初の面を除いた和が現れる。
使われ方：二つの欠けた面の相殺により AW の鎖写像の条件を証明する。 -/
lemma component_generator_boundary (X : SSet.{0}) (p q : ℕ)
    (x : X _⦋p + q + 1⦌) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X (p + q) p q rfl
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).d (p + q + 1) (p + q) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X (p + q + 1) x)) =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val •
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p (X.δ i.castSucc (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 (p + 1) (by omega))) ⊗ₜ[A]
          _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x (p + 1) q (by omega)))) +
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) •
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X p (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 p (by omega)) ⊗ₜ[A]
          _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X q (X.δ j.succ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x p (q + 1) (by omega)))) := by
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_d]
  simp only [map_sum, map_zsmul, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator]
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.sum_split p q]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_δ_inside X x (⟨i.val, by omega⟩ : Fin (p + q + 2))
      0 p (by omega) (by omega) (by simp only; have := i.isLt; omega),
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_δ_before X x (⟨i.val, by omega⟩ : Fin (p + q + 2))
        p q (by omega) (by simp only; have := i.isLt; omega)]
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_δ_after X x (⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2))
      0 p (by omega) (by simp only; omega),
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_δ_inside X x (⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2))
        p q (by omega) (by simp only; omega) (by simp only; have := j.isLt; omega)]
    have he : (⟨p + 1 + j.val - p, by omega⟩ : Fin (q + 2)) = j.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [he]

end SerrePositivity.SimplicialChains.AlexanderWhitney
