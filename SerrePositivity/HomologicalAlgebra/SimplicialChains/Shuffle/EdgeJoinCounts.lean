module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.EdgeJoin

/-!
# 連結した辺集合の接頭部分の濃度

概要：Berger–Fresse §1.1.4 の経路連結における水平辺・垂直辺の個数を計算する。
方針：前半・後半への区間制限を回収し、接頭部分を切断点で二つに分ける。
規約：切断点そのものを接頭部分の終点として許す。
使われ方：経路の連結の逆転数と Koszul 符号の計算。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.Shuffle

/-- 概要：区間制限は辺集合の補集合と可換（BF §1.1.4）。
方針：所属条件の否定を比較する。
規約：補集合はそれぞれの有限辺全体に関するもの。
使われ方：水平辺の区間計算から垂直辺の区間計算を得る。 -/
@[simp] lemma edgeInterval_compl {N : ℕ} (S : Finset (Fin N)) (a m : ℕ)
    (h : a + m ≤ N) : _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval Sᶜ a m h = (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval S a m h)ᶜ := by
  ext i
  simp

/-- 概要：連結と補集合は可換（BF §1.1.4）。
方針：切断点の前後の所属の否定を比較する。
規約：連結後の補集合は全 N 辺に関するもの。
使われ方：垂直辺数を連結の接頭部分の公式で求める。 -/
@[simp] lemma edgeJoin_compl {a b N : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b))
    (h : a + b = N) : (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h)ᶜ = _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin Sᶜ Tᶜ h := by
  ext i
  simp only [Finset.mem_compl, _root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeJoin]
  split_ifs <;> simp

/-- 概要：連結の前半での接頭辺数は最初の集合の接頭辺数（BF §1.1.4）。
方針：前半への区間制限とその接頭部分の濃度を使う。
規約：k=a の場合を含む。
使われ方：連結の前半にある水平辺の前の垂直辺数。 -/
lemma edgeJoin_prefix_card_front {a b N : ℕ}
    (S : Finset (Fin a)) (T : Finset (Fin b)) (h : a + b = N) (k : ℕ) (hk : k ≤ a) :
    ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h).filter (fun i => i.val < k)).card =
      (S.filter (fun i => i.val < k)).card := by
  have he := _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_prefix_card (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h) 0 a (by omega) k hk
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_edgeJoin_front] at he
  simpa only [zero_le, zero_add, true_and] using he.symm

/-- 概要：連結の後半では前半全体の辺数を加える（BF §1.1.4）。
方針：長い接頭部分を前半全体と後半の接頭部分に分割する。
規約：k は後半の長さ以下。
使われ方：連結の後半にある水平辺の前の垂直辺数。 -/
lemma edgeJoin_prefix_card_back {a b N : ℕ}
    (S : Finset (Fin a)) (T : Finset (Fin b)) (h : a + b = N) (k : ℕ) (hk : k ≤ b) :
    ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h).filter (fun i => i.val < a + k)).card =
      S.card + (T.filter (fun i => i.val < k)).card := by
  have he := _root_.SerrePositivity.SimplicialChains.Shuffle.prefix_card_add_interval_card (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h) a k
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_prefix_card_front S T h a le_rfl] at he
  have hi := _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_prefix_card (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h) a b (by omega) k hk
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_edgeJoin_back] at hi
  rw [← hi] at he
  simpa only [Fin.isLt, Finset.filter_true] using he.symm

end SerrePositivity.SimplicialChains.Shuffle
