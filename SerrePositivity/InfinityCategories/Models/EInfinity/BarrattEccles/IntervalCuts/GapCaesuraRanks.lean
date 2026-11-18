module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapValidity
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutGeometry

/-!
模型。文献の定義との比較は後で
# 非退化隙間の区切り位置と境界順位

概要：Berger–Fresse §2.2.7 の隙間に対する全区切り位置の上界を計算する。
方針：同色の二出現が隙間を跨ぐことを使い、前方区切り数を全区切り数へ移す。
規約：辺切断自身が退化する場合も含む。
使われ方：切断点障害の左右削除係数と全区切り集合の共通係数を比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非退化な直前隙間では全区切りが切断点より前（BF §2.2.7）。
方針：区切りと後の同色出現が隙間を跨ぐことを使う。
規約：元の辺切断の非零性は不要。
使われ方：左削除の共通係数の順位。 -/
lemma caesura_before_gap_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.castSucc) {a : Fin l} (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u a) : a < p := by
  obtain ⟨b, hab, hu⟩ := ha
  exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapNondegenerate_iff_straddles u p.castSucc).mp h a b hab hu.symm).1

/-- 概要：非退化な直後隙間では全区切りが切断点以下（BF §2.2.7）。
方針：区切りが隙間番号より前であることを自然数の上界へ直す。
規約：切断点自身が区切りの場合を含む。
使われ方：右削除の最後の区切り順位。 -/
lemma caesura_le_gap_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.succ) {a : Fin l} (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u a) : a ≤ p := by
  obtain ⟨b, hab, hu⟩ := ha
  have hs := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapNondegenerate_iff_straddles u p.succ).mp h a b hab hu.symm).1
  exact Nat.le_of_lt_add_one hs

/-- 概要：直前隙間の切断点の活動順位は全区切り数（BF §2.2.7）。
方針：全区切りは切断点より前で、追加した切断点自身は順位から除かれる。
規約：切断点は区切りではない。
使われ方：左削除係数の位置符号を共通係数へ移す。 -/
lemma positionRank_gap_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.castSucc) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u p) p = (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u)).card := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionRank
  congr 1
  ext a
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨rfl | ha, hap⟩
    · exact False.elim ((lt_irrefl _) hap)
    · exact ha
  · intro ha
    exact ⟨Or.inr ha, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_gap_pivot h ha⟩

/-- 概要：直後隙間の切断点が区切りならその順位+1は全区切り数（BF §2.2.7）。
方針：切断点以前の全区切り集合から切断点を一つ除いて数える。
規約：切断点の区切り所属を要求する。
使われ方：最後の同色出現の削除符号を全区切り数の冪へ直す。 -/
lemma caesuraRank_gap_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.succ) (hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u p + 1 = (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u)).card := by
  have hs : Finset.univ.filter (fun a => a < p ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u a) =
      (Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u)).erase p := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hap, ha⟩
      exact ⟨ne_of_lt hap, ha⟩
    · rintro ⟨hap, ha⟩
      exact ⟨lt_of_le_of_ne (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_le_gap_pivot h ha) hap, ha⟩
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank
  rw [hs]
  exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
