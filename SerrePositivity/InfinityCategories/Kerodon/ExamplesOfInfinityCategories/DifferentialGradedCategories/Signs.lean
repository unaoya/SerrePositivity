module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex
public import Mathlib.Data.Finset.Prod

/-! # dg nerve の二重削除の符号

概要：二点の削除順を交換すると係数の符号が反転することを証明する。
方針：右側点数は、一方の削除順でだけ一減ることを使う。
規約：HA Construction 1.3.1.6、符号は `(-1)^{#{k∈I : j<k}}`。
使われ方：HA Proposition 1.3.1.10 の残差恒等式の二重削除項の相殺。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

variable {α : Type*} [LinearOrder α]

/-- 概要：単体の方程式の符号は内部点より右にある点数の負一冪。
方針：濃度を整数へ写して整数の単位群の符号を用いる。
規約：HA Construction 1.3.1.6。使われ方：削除・切断の符号計算。 -/
def sign (I : Finset α) (j : α) : ℤˣ := ((I.filter (j < ·)).card : ℤ).negOnePow

/-- 概要：数える点以下の点を消しても右側部分集合は変わらない。
方針：filter と erase を交換し、数えない点の削除を消去する。
規約：HA Construction 1.3.1.6。使われ方：二重削除の第一の濃度計算。 -/
lemma right_filter_erase_le (I : Finset α) {j k : α} (hjk : j ≤ k) :
    (I.erase j).filter (k < ·) = I.filter (k < ·) := by
  rw [Finset.filter_erase]
  apply Finset.erase_eq_of_notMem
  simp only [Finset.mem_filter, not_and]
  intro _
  exact not_lt_of_ge hjk

/-- 概要：右側に属する点を消すと右側点数は一減る。
方針：filter と erase の交換と削除の濃度の等式を使う。
規約：HA Construction 1.3.1.6。使われ方：二重削除の第二の濃度計算。 -/
lemma right_card_erase_lt (I : Finset α) {j k : α} (hk : k ∈ I) (hjk : j < k) :
    ((I.erase k).filter (j < ·)).card + 1 = (I.filter (j < ·)).card := by
  rw [Finset.filter_erase]
  exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hk, hjk⟩)

/-- 概要：j<k の二点を消す順序を交換すると符号が逆になる。
方針：二つの指数の和の差が一であることを負一冪の加法則で移す。
規約：HA Construction 1.3.1.6。使われ方：二重削除の相殺の基本等式。 -/
lemma sign_erase_of_lt (I : Finset α) {j k : α} (hk : k ∈ I) (hjk : j < k) :
    sign I j * sign (I.erase j) k = -(sign I k * sign (I.erase k) j) := by
  unfold sign
  rw [right_filter_erase_le I hjk.le, ← Int.negOnePow_add, ← Int.negOnePow_add]
  have hc := right_card_erase_lt I hk hjk
  have he : ((I.filter (j < ·)).card : ℤ) + ((I.filter (k < ·)).card : ℤ) =
      (((I.filter (k < ·)).card : ℤ) + (((I.erase k).filter (j < ·)).card : ℤ)) + 1 := by omega
  rw [he, Int.negOnePow_add, Int.negOnePow_one, mul_neg_one]

/-- 概要：相異なる二点の削除順を交換すると係数が逆になる。
方針：二点の大小で場合分けし、逆向きの場合は両辺の負を取る。
規約：HA Construction 1.3.1.6。使われ方：有限和の交換対称性による消去。 -/
lemma sign_erase_swap (I : Finset α) {j k : α} (hj : j ∈ I) (hk : k ∈ I) (hjk : j ≠ k) :
    sign I j * sign (I.erase j) k = -(sign I k * sign (I.erase k) j) := by
  rcases lt_or_gt_of_ne hjk with h | h
  · exact sign_erase_of_lt I hk h
  · have he := congrArg Neg.neg (sign_erase_of_lt I hj h)
    simpa only [neg_neg] using he.symm

/-- 概要：同じ二点を消す二つの順序の寄与は相殺する。
方針：erase の可換性と係数の符号反転を使う。
規約：HA Proposition 1.3.1.10。使われ方：残差恒等式の二重削除項。 -/
lemma double_erase_pair {M : Type*} [AddCommGroup M] (I : Finset α) (f : Finset α → M)
    {j k : α} (hj : j ∈ I) (hk : k ∈ I) (hjk : j ≠ k) :
    sign I j • (sign (I.erase j) k • f ((I.erase j).erase k)) +
      sign I k • (sign (I.erase k) j • f ((I.erase k).erase j)) = 0 := by
  rw [smul_smul, smul_smul, sign_erase_swap I hj hk hjk, Finset.erase_right_comm]
  simp [Units.smul_def]

/-- 概要：指定した内部点集合の全ての二重削除項の和は零。
方針：相異なる点の組を交換する固定点のない対合で有限和を相殺する。
規約：HA Proposition 1.3.1.10。使われ方：単体の方程式を二度展開する際の線形部分。 -/
lemma sum_double_erase {M : Type*} [AddCommGroup M] (I K : Finset α) (hKI : K ⊆ I)
    (f : Finset α → M) :
    ∑ jk ∈ K.offDiag, sign I jk.1 • (sign (I.erase jk.1) jk.2 •
      f ((I.erase jk.1).erase jk.2)) = 0 := by
  have hmem : ∀ jk ∈ K.offDiag, jk.swap ∈ K.offDiag := by
    intro jk hjk
    have h := Finset.mem_offDiag.mp hjk
    exact Finset.mem_offDiag.mpr ⟨h.2.1, h.1, Ne.symm h.2.2⟩
  refine Finset.sum_involution (fun jk _ => jk.swap) ?_ ?_ hmem ?_
  · intro jk hjk
    have h := Finset.mem_offDiag.mp hjk
    exact double_erase_pair I f (hKI h.1) (hKI h.2.1) h.2.2
  · intro jk hjk _ he
    have h := Finset.mem_offDiag.mp hjk
    exact h.2.2 (congrArg Prod.snd he)
  · intro jk _
    exact Prod.swap_swap jk

/-- 概要：j≤k なら、j からの右切断で k より右の点数は変わらない。
方針：k より右の点は自動的に j 以上である。
規約：HA Proposition 1.3.1.10。使われ方：二度切断する項の符号。 -/
lemma sign_right_cut (I : Finset α) {j k : α} (hjk : j ≤ k) :
    sign (I.filter (j ≤ ·)) k = sign I k := by
  have he : (I.filter (j ≤ ·)).filter (k < ·) = I.filter (k < ·) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hjk.trans h.2.le⟩, h.2⟩⟩
  simp only [sign, he]

/-- 概要：切断点を含む右側集合の濃度は、狭義右側集合より一大きい。
方針：切断点の挿入で右側集合を表す。
規約：HA Proposition 1.3.1.10。使われ方：後に作用する成分の次数の符号。 -/
lemma right_cut_card (I : Finset α) {k : α} (hk : k ∈ I) :
    (I.filter (k ≤ ·)).card = (I.filter (k < ·)).card + 1 := by
  have he : I.filter (k ≤ ·) = insert k (I.filter (k < ·)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hkx⟩
      rcases hkx.eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨hx, h⟩
    · rintro (rfl | ⟨hx, hkx⟩)
      · exact ⟨hk, le_rfl⟩
      · exact ⟨hx, hkx.le⟩
  rw [he, Finset.card_insert_of_notMem]
  simp

/-- 概要：j<k のとき j より右の点は、k までの部分と k より右の部分に分かれる。
方針：二つの部分集合の非交和を濃度で数える。
規約：HA Proposition 1.3.1.10。使われ方：二重切断の指数の和の比較。 -/
lemma left_right_sign_card (I : Finset α) {j k : α} (hjk : j < k) :
    ((I.filter (· ≤ k)).filter (j < ·)).card + (I.filter (k < ·)).card =
      (I.filter (j < ·)).card := by
  have hu : (I.filter (· ≤ k)).filter (j < ·) ∪ I.filter (k < ·) = I.filter (j < ·) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨⟨hx, _⟩, hjx⟩ | ⟨hx, hkx⟩)
      · exact ⟨hx, hjx⟩
      · exact ⟨hx, hjk.trans hkx⟩
    · rintro ⟨hx, hjx⟩
      by_cases hxk : x ≤ k
      · exact Or.inl ⟨⟨hx, hxk⟩, hjx⟩
      · exact Or.inr ⟨hx, lt_of_not_ge hxk⟩
  have hd : Disjoint ((I.filter (· ≤ k)).filter (j < ·)) (I.filter (k < ·)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact not_lt_of_ge (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      (Finset.mem_filter.mp hy).2
  have hc := Finset.card_union_of_disjoint hd
  rw [hu] at hc
  exact hc.symm

/-- 概要：二度切断する二つの順序の係数は、Leibniz の符号も含めて逆になる。
方針：左右の点数の分割と右切断の濃度を使い、指数の差を偶数と一の和にする。
規約：HA Proposition 1.3.1.10。使われ方：結合律で一致する三重合成項の相殺。 -/
lemma sign_double_cut (I : Finset α) {j k : α} (hk : k ∈ I) (hjk : j < k) :
    sign I j * sign (I.filter (j ≤ ·)) k =
      -(sign I k * (2 - ((I.filter (k ≤ ·)).card : ℤ)).negOnePow *
        sign (I.filter (· ≤ k)) j) := by
  rw [sign_right_cut I hjk.le]
  unfold sign
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add]
  have hLR := left_right_sign_card I hjk
  have hR := right_cut_card I hk
  have h₁ : ((I.filter (j < ·)).card : ℤ) + ((I.filter (k < ·)).card : ℤ) =
      (((I.filter (· ≤ k)).filter (j < ·)).card : ℤ) +
        2 * ((I.filter (k < ·)).card : ℤ) := by omega
  have h₂ : ((I.filter (k < ·)).card : ℤ) + (2 - ((I.filter (k ≤ ·)).card : ℤ)) +
      (((I.filter (· ≤ k)).filter (j < ·)).card : ℤ) =
        (((I.filter (· ≤ k)).filter (j < ·)).card : ℤ) + 1 := by omega
  rw [h₁, h₂, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one,
    Int.negOnePow_add, Int.negOnePow_one, mul_neg_one, neg_neg]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
