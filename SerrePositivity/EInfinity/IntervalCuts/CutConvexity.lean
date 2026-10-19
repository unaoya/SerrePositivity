module

public import SerrePositivity.EInfinity.IntervalCuts.CutValidity

/-!
# 非零な区間切断の凸性

概要：Berger–Fresse §2.2.7 の切断点色の境界和を連続する切断の望遠和へ移す。
方針：全ての同色対が切断点を厳密に跨ぐ条件で非零切断を特徴付ける。
規約：任意の有限語を扱い、全射性や隣接非退化性を追加しない。
使われ方：非零切断の区間の内部項を相殺し、両端だけを残す。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

/-- 概要：非零切断の条件は全ての同色対を厳密に跨ぐこと（BF §2.2.1）。
方針：左右の単射性を同色の二位置の順序ごとに判定する。
規約：同色三出現があれば条件は自動的に矛盾する。
使われ方：切断点の移動と非零切断集合の凸性。 -/
lemma edgeNondegenerate_iff_straddles {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) :
    EdgeNondegenerate u p ↔ ∀ i j, i < j → u i = u j → i < p ∧ p < j := by
  constructor
  · exact fun h _ _ hij hu => repeated_straddles h hij hu
  · intro h
    rw [edgeNondegenerate_iff]
    constructor
    · intro i j hi hj hu
      by_contra he
      rcases lt_or_gt_of_ne he with hij | hji
      · exact (not_lt_of_ge hj) (h i j hij hu).2
      · exact (not_lt_of_ge hi) (h j i hji hu.symm).2
    · intro i j hi hj hu
      by_contra he
      rcases lt_or_gt_of_ne he with hij | hji
      · exact (not_lt_of_ge hi) (h i j hij hu).1
      · exact (not_lt_of_ge hj) (h j i hji hu.symm).1

/-- 概要：二つの非零切断の間の全ての切断も非零（BF §2.2.7）。
方針：各同色対が両端を跨ぐことから中間の切断点も跨ぐ。
規約：両端を含む順序区間。
使われ方：切断点色の境界項を一つの望遠和にまとめる。 -/
lemma edgeNondegenerate_between {n l : ℕ} {u : Fin l → Fin n} {a b p : Fin l}
    (ha : EdgeNondegenerate u a) (hb : EdgeNondegenerate u b) (hap : a ≤ p) (hpb : p ≤ b) :
    EdgeNondegenerate u p := by
  apply (edgeNondegenerate_iff_straddles u p).mpr
  intro i j hij hu
  exact ⟨lt_of_lt_of_le (repeated_straddles ha hij hu).1 hap,
    lt_of_le_of_lt hpb (repeated_straddles hb hij hu).2⟩

end SerrePositivity.EInfinity.IntervalCuts
