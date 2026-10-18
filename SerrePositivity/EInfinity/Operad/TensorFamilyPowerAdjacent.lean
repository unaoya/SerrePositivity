module

public import SerrePositivity.EInfinity.Operad.TensorFamilyPowerFirstSwap
public import SerrePositivity.EInfinity.Operad.TensorFamilyPowerTail

/-!
# 隣接する入力ブロックの交換と連結

概要：Berger–Moerdijk §1 の任意の隣接ブロック交換を、全入力の全単射の作用と比較する。
方針：先頭二ブロックの交換を基底とし、先頭を保って尾へ帰納する。
規約：各ブロックの長さは零でもよい。
使われ方：自由代数の外側等変性で、入力のブロック交換を連結したテンソル冪へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers SerrePositivity.Coxeter
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] TensorPowers.power tensorPowerFamilyIso

/-- 概要：任意の隣接ブロック交換が全入力に誘導する全単射（Berger–Moerdijk §1）。
方針：先頭の交換と、先頭を保った尾の交換で再帰する。
規約：n+1 ブロックに n 個の隣接交換を添字付ける。
使われ方：有限テンソル族の隣接交換の連結後の作用を記述する。 -/
def tensorFamilyAdjacentBlockEquiv : ∀ (n : ℕ) (s : Fin (n + 1) → ℕ) (i : Fin n),
    Fin (∑ j, s j) ≃ Fin (∑ j, s (adjacentTransposition i j))
  | 0, _, i => Fin.elim0 i
  | n + 1, s, i =>
    Fin.cases (tensorFamilyFirstBlockEquiv n s) (fun j =>
      (finCongr (Fin.sum_univ_succ s)).trans
        ((FiniteBijection.blockEquiv (Equiv.refl (Fin (s 0)))
          (tensorFamilyAdjacentBlockEquiv n (fun k => s k.succ) j)).trans
            (finCongr (tensorFamily_sum_adjacentSucc n s j).symm))) i

/-- 概要：先頭の隣接ブロック交換は三ブロックの先頭交換である（Berger–Moerdijk §1）。
方針：全単射の再帰の先頭の場合を評価する。
規約：残りのブロックを一つの総和として扱う。
使われ方：連結の隣接交換の帰納法の基底で使う。 -/
lemma tensorFamilyAdjacentBlockEquiv_zero (n : ℕ) (s : Fin (n + 2) → ℕ) :
    tensorFamilyAdjacentBlockEquiv (n + 1) s 0 = tensorFamilyFirstBlockEquiv n s := rfl

/-- 概要：尾の隣接ブロック交換は先頭の恒等全単射とのブロック和である（Berger–Moerdijk §1）。
方針：全単射の再帰の尾の場合を評価する。
規約：前後の総和の移送を明示する。
使われ方：連結の隣接交換の帰納段階で全入力の全単射を展開する。 -/
lemma tensorFamilyAdjacentBlockEquiv_succ (n : ℕ) (s : Fin (n + 2) → ℕ) (i : Fin n) :
    tensorFamilyAdjacentBlockEquiv (n + 1) s i.succ =
      (finCongr (Fin.sum_univ_succ s)).trans
        ((FiniteBijection.blockEquiv (Equiv.refl (Fin (s 0)))
          (tensorFamilyAdjacentBlockEquiv n (fun k => s k.succ) i)).trans
            (finCongr (tensorFamily_sum_adjacentSucc n s i).symm)) := rfl

/-- 概要：任意の隣接ブロック交換は有限テンソル族の連結と両立する（Berger–Moerdijk §1）。
方針：先頭の交換の比較を使い、尾の移送と連結の全単射に関する等変性で帰納する。
規約：連結後の全単射はブロック内の順序を保つ。
使われ方：Schur 演算の外側等変性で入力側の全ての隣接交換を計算する。 -/
@[reassoc]
lemma tensorPowerFamilyIso_adjacent (K : Complex A) (n : ℕ) (s : Fin (n + 1) → ℕ)
    (i : Fin n) :
    (tensorFamilyAdjacentIso n (fun j => power K (s j)) i).hom ≫
        (tensorPowerFamilyIso K (n + 1) (fun j => s (adjacentTransposition i j))).hom =
      (tensorPowerFamilyIso K (n + 1) s).hom ≫
        tensorPowerEquivMap K (tensorFamilyAdjacentBlockEquiv n s i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [tensorFamilyAdjacentIso_zero, tensorFamilyAdjacentBlockEquiv_zero]
      exact tensorPowerFamilyIso_firstSwap K n s
    · apply (cancel_mono
        (eqToHom (congrArg (power K) (tensorFamily_sum_adjacentSucc n s j)))).1
      simp only [tensorFamilyAdjacentIso_succ, tensorFamilyAdjacentBlockEquiv_succ,
        tensorPowerEquivMap_trans, tensorPowerEquivMap_finCongr, Category.assoc]
      rw [eqToHom_trans]
      simp only [eqToHom_refl, Category.comp_id]
      rw [tensorPowerFamilyIso_head_assoc, ← appendIso_equivariance]
      simp only [tensorPowerEquivMap_refl, id_tensorHom]
      rw [tensorPowerFamilyIso_adjacentSucc_transport, ← whiskerLeft_comp_assoc,
        ih (fun k => s k.succ) j]
      simp only [whiskerLeft_comp, Category.assoc]

end SerrePositivity.EInfinity
