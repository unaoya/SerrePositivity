module

public import SerrePositivity.EInfinity.Operad.OneSlotSubstitutionTransport
public import SerrePositivity.EInfinity.Operad.CompositionLastSwapEquivariance

/-!
# 隣接交換が反復合成の出力へ誘導する全単射

概要：Berger–Moerdijk §1 の反復合成の隣接交換の出力を帰納的に記述する。
方針：末尾二入力の交換を基底とし、末尾固定の交換では前半の出力の全単射を arity の移送で挟む。
規約：元の未代入の尾の長さ k は各再帰で更新する。
使われ方：隣接交換に関する反復合成の外側等変性の終域を指定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.Coxeter
open scoped BigOperators

/-- 概要：末尾二入力の交換を指定入力全体の交換と未代入入力の恒等置換のブロック和で表す（Berger–Moerdijk §1）。
方針：ブロック和の左側の二点の交換の式を使う。
規約：未代入入力 k 個を右側に保つ。
使われ方：隣接交換の帰納法の末尾の場合を既存の末尾交換の等変性へ帰着する。 -/
lemma operadLastTwoInputSwap_block (n k : ℕ) :
    FiniteBijection.blockEquiv (adjacentTransposition (Fin.last n)) (Equiv.refl (Fin k)) =
      operadLastTwoInputSwap n k := by
  rw [adjacentTransposition, FiniteBijection.blockEquiv_swap_left]
  rfl

/-- 概要：前半の交換の出力の全単射を末尾固定の交換の全入力の和へ持ち上げる（Berger–Moerdijk §1）。
方針：交換前後の最後の入力の分離で得る arity の等式を前後に合成する。
規約：前半の未代入の尾は k と最後の arity の和。
使われ方：隣接交換の出力の全単射の帰納段階を定義する。 -/
def operadAdjacentCastOutput (n k : ℕ) (s : Fin (n + 2) → ℕ) (i : Fin n)
    (e : Fin ((∑ j : Fin (n + 1), s j.castSucc) + (k + s (Fin.last (n + 1)))) ≃
      Fin ((∑ j : Fin (n + 1), s (adjacentTransposition i j).castSucc) +
        (k + s (Fin.last (n + 1))))) :
    Fin ((∑ j, s j) + k) ≃ Fin ((∑ j, s (adjacentTransposition i.castSucc j)) + k) :=
  (finCongr (oneSlotComposeOutput_eq (n + 1) k s).symm).trans
    (e.trans (finCongr (oneSlotSwapOutput_eq n k s i)))

/-- 概要：任意の隣接交換が反復合成の出力へ誘導する全単射（Berger–Moerdijk §1）。
方針：交換位置が末尾なら二ブロックを交換し、それ以外は最後の入力を代入して前半へ再帰する。
規約：n+1 個の指定入力と未代入入力 k 個を持つ。
使われ方：任意の隣接位置に関する外側等変性を述べる。 -/
def operadCompositionAdjacentOutput : ∀ (n k : ℕ) (s : Fin (n + 1) → ℕ) (i : Fin n),
    Fin ((∑ j, s j) + k) ≃ Fin ((∑ j, s (adjacentTransposition i j)) + k)
  | 0, _, _, i => Fin.elim0 i
  | n + 1, k, s, i =>
    Fin.lastCases (operadLastTwoOutputEquiv n k s)
      (fun j => operadAdjacentCastOutput n k s j
        (operadCompositionAdjacentOutput n (k + s (Fin.last (n + 1)))
          (fun j => s j.castSucc) j)) i

/-- 概要：隣接交換の出力の再帰は末尾位置で既存の二ブロック交換となる（Berger–Moerdijk §1）。
方針：再帰定義の最後の位置の場合を計算する。
規約：指定入力は n+2 個。
使われ方：等変性の帰納法の末尾の場合に用いる。 -/
lemma operadCompositionAdjacentOutput_last (n k : ℕ) (s : Fin (n + 2) → ℕ) :
    operadCompositionAdjacentOutput (n + 1) k s (Fin.last n) =
      operadLastTwoOutputEquiv n k s := by
  simp only [operadCompositionAdjacentOutput, Fin.lastCases_last]

/-- 概要：末尾以外の隣接交換の出力は最後の入力を代入した前半の出力を移したものになる（Berger–Moerdijk §1）。
方針：再帰定義の castSucc の場合を計算する。
規約：最後の指定入力の arity を未代入の尾へ加える。
使われ方：等変性の帰納段階で出力の全単射を展開する。 -/
lemma operadCompositionAdjacentOutput_castSucc (n k : ℕ)
    (s : Fin (n + 2) → ℕ) (i : Fin n) :
    operadCompositionAdjacentOutput (n + 1) k s i.castSucc =
      operadAdjacentCastOutput n k s i
        (operadCompositionAdjacentOutput n (k + s (Fin.last (n + 1)))
          (fun j => s j.castSucc) i) := by
  simp only [operadCompositionAdjacentOutput, Fin.lastCases_castSucc]

namespace Operad

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 概要：前半の出力の全単射を持ち上げた作用は arity の移送を前後に合成して計算する（Berger–Moerdijk §1）。
方針：全単射の合成則と長さの標準全単射の作用の式を使う。
規約：前半の出力の全単射 e は任意でよい。
使われ方：反復合成後の arity の移送を相殺して帰納仮定を適用する。 -/
lemma arity_adjacentCastOutput (P : Operad A) (n k : ℕ) (s : Fin (n + 2) → ℕ) (i : Fin n)
    (e : Fin ((∑ j : Fin (n + 1), s j.castSucc) + (k + s (Fin.last (n + 1)))) ≃
      Fin ((∑ j : Fin (n + 1), s (adjacentTransposition i j).castSucc) +
        (k + s (Fin.last (n + 1))))) :
    P.arityBijectionMap (operadAdjacentCastOutput n k s i e) =
      eqToHom (congrArg P.arity (oneSlotComposeOutput_eq (n + 1) k s).symm) ≫
        P.arityBijectionMap e ≫ eqToHom (congrArg P.arity (oneSlotSwapOutput_eq n k s i)) := by
  simp only [operadAdjacentCastOutput, arityBijectionMap_trans, arityBijectionMap_finCongr]

end Operad

end SerrePositivity.EInfinity
