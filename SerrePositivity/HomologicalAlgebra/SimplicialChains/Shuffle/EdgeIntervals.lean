module

public import SerrePositivity.EInfinity.BarrattEccles.ShufflePaths

/-!
# 格子経路の辺集合の区間制限

概要：Berger–Fresse §1.1.4 の shuffle の切断に必要な辺の有限集合の制限を整備する。
方針：連続する区間の辺を番号零から振り直し、濃度を全単射で比較する。
規約：区間 [a,a+m) は辺の区間であり、頂点は両端を含む。
使われ方：AW 切断点での shuffle 経路の前半・後半を構成する。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.Shuffle

/-- 概要：有限辺集合の連続区間への制限（Berger–Fresse §1.1.4）。
方針：区間の開始位置を足して元の辺集合に属するか判定する。
規約：出力の辺番号は零から m−1。
使われ方：shuffle の前半・後半の水平辺集合。 -/
def edgeInterval {N : ℕ} (S : Finset (Fin N)) (a m : ℕ) (h : a + m ≤ N) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (⟨a + i.val, by omega⟩ : Fin N) ∈ S)

/-- 概要：辺の区間制限の所属条件（Berger–Fresse §1.1.4）。
方針：有限集合の filter の所属を展開する。
規約：区間内の辺番号を元の番号へ戻す。
使われ方：切断後の経路の辺集合を比較する。 -/
@[simp] lemma mem_edgeInterval {N : ℕ} (S : Finset (Fin N)) (a m : ℕ)
    (h : a + m ≤ N) (i : Fin m) :
    i ∈ _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval S a m h ↔ (⟨a + i.val, by omega⟩ : Fin N) ∈ S := by
  simp [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval]

/-- 概要：区間制限の接頭部分の濃度（Berger–Fresse §1.1.4）。
方針：元の辺番号へ戻す写像を有限集合の全単射として使う。
規約：接頭長 k は区間長 m 以下。
使われ方：制限した経路の各頂点の水平座標を計算する。 -/
lemma edgeInterval_prefix_card {N : ℕ} (S : Finset (Fin N)) (a m : ℕ)
    (h : a + m ≤ N) (k : ℕ) (hk : k ≤ m) :
    ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval S a m h).filter (fun i => i.val < k)).card =
      (S.filter (fun i => a ≤ i.val ∧ i.val < a + k)).card := by
  apply Finset.card_bij (fun i _ => (⟨a + i.val, by omega⟩ : Fin N))
  · intro i hi
    simp only [Finset.mem_filter, _root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeInterval] at hi
    simp only [Finset.mem_filter]
    exact ⟨hi.1, by omega, by omega⟩
  · intro i hi j hj hij
    apply Fin.ext
    have he := congrArg Fin.val hij
    dsimp at he
    omega
  · intro i hi
    simp only [Finset.mem_filter] at hi
    let j : Fin m := ⟨i.val - a, by omega⟩
    refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_filter, _root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeInterval]
      have he : (⟨a + j.val, by omega⟩ : Fin N) = i := by
        apply Fin.ext
        dsimp [j]
        omega
      exact ⟨he ▸ hi.1, by dsimp [j]; omega⟩
    · apply Fin.ext
      dsimp [j]
      omega

/-- 概要：辺の区間制限の濃度（Berger–Fresse §1.1.4）。
方針：接頭部分の濃度公式に区間全体の長さを代入する。
規約：長さ零の区間も扱う。
使われ方：shuffle の切断後の経路の型を指定する。 -/
lemma edgeInterval_card {N : ℕ} (S : Finset (Fin N)) (a m : ℕ) (h : a + m ≤ N) :
    (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval S a m h).card = (S.filter (fun i => a ≤ i.val ∧ i.val < a + m)).card := by
  simpa only [Fin.isLt, Finset.filter_true] using _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_prefix_card S a m h m le_rfl

/-- 概要：辺の区間制限を反復すると開始位置が加算される（Berger–Fresse §1.1.4）。
方針：各辺の所属を元の番号へ戻して比較する。
規約：内側の区間は外側の区間に含まれる。
使われ方：shuffle を反復切断する場合の経路の同定。 -/
lemma edgeInterval_edgeInterval {N : ℕ} (S : Finset (Fin N)) (a m : ℕ)
    (h : a + m ≤ N) (b k : ℕ) (hk : b + k ≤ m) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval S a m h) b k hk = _root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval S (a + b) k (by omega) := by
  ext i
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeInterval]
  have he : (⟨a + (b + i.val), by omega⟩ : Fin N) = ⟨a + b + i.val, by omega⟩ := by
    apply Fin.ext
    dsimp
    omega
  rw [he]

/-- 概要：辺の接頭区間を二つの連続区間に分けた濃度公式（Berger–Fresse §1.1.4）。
方針：長い接頭区間を切断点より前か後かで filter により分割する。
規約：区間の終点を超える辺は元の有限集合に存在しないので許してよい。
使われ方：shuffle の後半の座標の差を計算する。 -/
lemma prefix_card_add_interval_card {N : ℕ} (S : Finset (Fin N)) (a k : ℕ) :
    (S.filter (fun i => i.val < a)).card +
        (S.filter (fun i => a ≤ i.val ∧ i.val < a + k)).card =
      (S.filter (fun i => i.val < a + k)).card := by
  have hpre : (S.filter (fun i => i.val < a + k)).filter (fun i => i.val < a) =
      S.filter (fun i => i.val < a) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, _⟩, hia⟩
      exact ⟨hi, hia⟩
    · rintro ⟨hi, hia⟩
      exact ⟨⟨hi, by omega⟩, hia⟩
  have hpost : (S.filter (fun i => i.val < a + k)).filter (fun i => ¬i.val < a) =
      S.filter (fun i => a ≤ i.val ∧ i.val < a + k) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, hend⟩, hstart⟩
      exact ⟨hi, by omega, hend⟩
    · rintro ⟨hi, hstart, hend⟩
      exact ⟨⟨hi, hend⟩, by omega⟩
  have he := Finset.card_filter_add_card_filter_not
    (s := S.filter (fun i => i.val < a + k)) (fun i => i.val < a)
  rw [hpre, hpost] at he
  exact he

end SerrePositivity.SimplicialChains.Shuffle
