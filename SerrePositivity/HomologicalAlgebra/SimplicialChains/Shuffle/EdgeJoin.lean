module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.EdgeIntervals

/-!
# 辺集合の連結と区間制限の逆性

概要：Berger–Fresse §1.1.4 の shuffle 分割に逆な辺集合の連結を構成する。
方針：切断点の前では最初の集合、後では番号をずらした第二の集合を使う。
規約：全辺数の等式を明示し、長さ零の部分も許す。
使われ方：shuffle 経路の前半・後半による分割の全単射。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.Shuffle

/-- 概要：二つの有限辺集合の連結（Berger–Fresse §1.1.4）。
方針：切断位置 a で場合分けし後半の辺番号から a を引く。
規約：出力の辺数 N は a+b に等しい。
使われ方：前半・後半の shuffle 経路を復元する。 -/
def edgeJoin {a b N : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b)) (h : a + b = N) :
    Finset (Fin N) :=
  Finset.univ.filter (fun i =>
    if hi : i.val < a then (⟨i.val, hi⟩ : Fin a) ∈ S
    else (⟨i.val - a, by omega⟩ : Fin b) ∈ T)

/-- 概要：連結辺集合の所属条件（Berger–Fresse §1.1.4）。
方針：有限集合の filter を展開する。
規約：切断点以後の辺は後半に属する。
使われ方：連結と区間制限の逆性。 -/
@[simp] lemma mem_edgeJoin {a b N : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b))
    (h : a + b = N) (i : Fin N) :
    i ∈ _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h ↔
      if hi : i.val < a then (⟨i.val, hi⟩ : Fin a) ∈ S
      else (⟨i.val - a, by omega⟩ : Fin b) ∈ T := by
  simp [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin]

/-- 概要：連結を前半の区間へ制限すると最初の辺集合（Berger–Fresse §1.1.4）。
方針：各辺の所属を切断点より前の場合で計算する。
規約：区間の開始位置は零。
使われ方：shuffle の連結後の前半経路を回収する。 -/
@[simp] lemma edgeInterval_edgeJoin_front {a b N : ℕ}
    (S : Finset (Fin a)) (T : Finset (Fin b)) (h : a + b = N) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h) 0 a (by omega) = S := by
  ext i
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeInterval, _root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeJoin]
  rw [dite_eq_left (show 0 + i.val < a by omega)]
  have hi : (⟨0 + i.val, by omega⟩ : Fin a) = i := by
    apply Fin.ext
    dsimp
    omega
  rw [hi]

/-- 概要：連結を後半の区間へ制限すると第二の辺集合（Berger–Fresse §1.1.4）。
方針：各辺の所属で開始位置の加算と減算を消す。
規約：後半の辺番号は零から振り直す。
使われ方：shuffle の連結後の後半経路を回収する。 -/
@[simp] lemma edgeInterval_edgeJoin_back {a b N : ℕ}
    (S : Finset (Fin a)) (T : Finset (Fin b)) (h : a + b = N) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h) a b (by omega) = T := by
  ext i
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeInterval, _root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeJoin]
  rw [dite_eq_right (show ¬a + i.val < a by omega)]
  have hi : (⟨a + i.val - a, by omega⟩ : Fin b) = i := by
    apply Fin.ext
    dsimp
    omega
  rw [hi]

/-- 概要：区間制限の開始位置の等式による比較（Berger–Fresse §1.1.4）。
方針：開始位置の等式を消去する。
規約：区間長と全辺数は変えない。
使われ方：経路の二座標の和と切断頂点の番号を同定する。 -/
lemma edgeInterval_start_eq {N : ℕ} (S : Finset (Fin N)) {a a' : ℕ} (ha : a = a')
    (m : ℕ) (h : a + m ≤ N) (h' : a' + m ≤ N) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval S a m h = _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval S a' m h' := by
  subst a'
  rfl

/-- 概要：辺集合を前半・後半へ制限して連結すると元の集合（Berger–Fresse §1.1.4）。
方針：各辺を切断点より前か後かに分け、元の番号を復元する。
規約：全辺数は a+b。
使われ方：shuffle の分割からの連結が元の経路を回収することを示す。 -/
@[simp] lemma edgeJoin_edgeIntervals {N : ℕ} (S : Finset (Fin N)) (a b : ℕ)
    (h : a + b = N) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval S 0 a (by omega)) (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval S a b (by omega)) h = S := by
  ext i
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeJoin]
  split_ifs with hi
  · rw [_root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeInterval]
    have he : (⟨0 + i.val, by omega⟩ : Fin N) = i := by
      apply Fin.ext
      dsimp
      omega
    rw [he]
  · rw [_root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeInterval]
    have he : (⟨a + (i.val - a), by omega⟩ : Fin N) = i := by
      apply Fin.ext
      dsimp
      omega
    rw [he]

/-- 概要：連結辺集合の濃度は二つの濃度の和（Berger–Fresse §1.1.4）。
方針：区間分割の濃度公式と連結の二つの区間制限を使う。
規約：前半・後半のどちらが空でも成立する。
使われ方：連結を指定した二次数の shuffle 経路として構成する。 -/
@[simp] lemma edgeJoin_card {a b N : ℕ} (S : Finset (Fin a)) (T : Finset (Fin b))
    (h : a + b = N) : (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h).card = S.card + T.card := by
  let J := _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h
  have hp : (J.filter (fun i => i.val < a)).card =
      (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval J 0 a (by omega)).card := by
    simpa only [zero_le, zero_add, true_and] using
      (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_card J 0 a (by omega)).symm
  have hf : J.filter (fun i => i.val < a + b) = J :=
    Finset.filter_true_of_mem (fun i _ => by omega)
  have he := _root_.SerrePositivity.SimplicialChains.Shuffle.prefix_card_add_interval_card J a b
  rw [hp, ← _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_card J a b (by omega), hf] at he
  change (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h) 0 a (by omega)).card +
    (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h) a b (by omega)).card = (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h).card at he
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_edgeJoin_front, _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_edgeJoin_back] at he
  exact he.symm

end SerrePositivity.SimplicialChains.Shuffle
