module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleDeletionCoordinates

/-!
# 辺数の移送と接頭辺数

概要：Berger–Fresse §1.1.3 の水平辺削除で現れる辺数の等式による移送を整理する。
方針：Fin の等しい長さへの移送が位置番号と接頭区間の濃度を保つことを使う。
規約：p+1+q と p+q+1 の同定で辺の番号の値は変えない。
使われ方：水平辺削除の接頭辺数の公式を元の経路の座標へ戻す。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：辺数の等式に沿う移送は接頭区間内の辺数を保つ（Berger–Fresse §1.1.3）。
方針：等式の帰納法で恒等的な移送に帰着する。
規約：閾値は自然数であり、頂点の型の移送を要求しない。
使われ方：水平辺削除前の辺集合を標準の長さへ移す。 -/
lemma card_filter_finCongr {M N : ℕ} (h : M = N) (s : Finset (Fin M)) (k : ℕ) :
    ((s.map (finCongr h).toEmbedding).filter (fun x => x.val < k)).card =
      (s.filter (fun x => x.val < k)).card := by
  subst N
  simp

/-- 概要：辺数の等式による移送は辺集合の補集合と可換する（Berger–Fresse §1.1.3）。
方針：等式の帰納法で恒等的な有限集合の像を計算する。
規約：補集合は移送前後それぞれの全辺集合で取る。
使われ方：水平辺の補集合である垂直辺も同時に移送する。 -/
lemma map_finCongr_compl {M N : ℕ} (h : M = N) (s : Finset (Fin M)) :
    (s.map (finCongr h).toEmbedding)ᶜ = sᶜ.map (finCongr h).toEmbedding := by
  subst N
  simp

/-- 概要：頂点を飛ばした後の位置番号は元の番号だけで決まる（Berger–Fresse §1.1.3）。
方針：succAbove の二つの場合を値の不等式に直す。
規約：有限順序の長さは左右で異なっていてよい。
使われ方：水平辺削除で辺数を移送した前後の頂点の値を比較する。 -/
lemma succAbove_succ_val_congr {M N : ℕ} (a k : Fin M) (b l : Fin N)
    (ha : a.val = b.val) (hk : k.val = l.val) :
    (a.succ.succAbove k).val = (b.succ.succAbove l).val := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, ha, hk]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ, hk]

end SerrePositivity.EInfinity.BarrattEccles
