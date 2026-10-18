module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSwapOrder

/-!
# shuffle 経路の隣接交換と符号反転

概要：Berger–Fresse §1.1.3 の shuffle の境界の相殺に使う経路の交換を構成する。
方針：水平辺集合を隣接する二位置の互換で移し、昇順列挙と signature を比較する。
規約：符号反転には交換する辺が水平と垂直の一方ずつであることを要求する。
使われ方：shuffle の境界に現れる混合角の二項を対にする。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：経路の二つの辺の位置を交換する（Berger–Fresse §1.1.3）。
方針：水平辺集合に互換を適用して水平辺数を保存する。
規約：定義自体は隣接性や辺の向きの条件を要求しない。
使われ方：境界の相殺に使う経路の対を構成する。 -/
def ShufflePath.swapSteps {p q : ℕ} (s : ShufflePath p q) (a b : Fin (p + q)) :
    ShufflePath p q :=
  ⟨s.val.map (Equiv.swap a b).toEmbedding, by simpa using s.property⟩

/-- 概要：交換後の水平辺の所属は互換による逆像で判定できる（Berger–Fresse §1.1.3）。
方針：同値による有限集合の像の所属を計算する。
規約：互換は自己逆である。
使われ方：交換の反復と辺の向きの変化を計算する。 -/
@[simp] lemma ShufflePath.mem_swapSteps {p q : ℕ} (s : ShufflePath p q)
    (a b x : Fin (p + q)) : x ∈ (s.swapSteps a b).val ↔ Equiv.swap a b x ∈ s.val := by
  simp only [ShufflePath.swapSteps, Finset.mem_map_equiv, Equiv.symm_swap]

/-- 概要：同じ辺の交換を二度行うと元の経路に戻る（Berger–Fresse §1.1.3）。
方針：水平辺の所属について互換の自己逆性を使う。
規約：隣接性を仮定しない。
使われ方：境界項の相殺のための involution の法則となる。 -/
@[simp] lemma ShufflePath.swapSteps_swapSteps {p q : ℕ} (s : ShufflePath p q)
    (a b : Fin (p + q)) : (s.swapSteps a b).swapSteps a b = s := by
  apply Subtype.ext
  ext x
  simp

/-- 概要：垂直辺集合も水平辺集合と同じ互換で移る（Berger–Fresse §1.1.3）。
方針：補集合の所属を互換による逆像で判定する。
規約：補集合は全辺集合の中で取る。
使われ方：垂直辺の昇順列挙を比較する。 -/
lemma ShufflePath.swapSteps_compl {p q : ℕ} (s : ShufflePath p q)
    (a b : Fin (p + q)) :
    (s.swapSteps a b).valᶜ = s.valᶜ.map (Equiv.swap a b).toEmbedding := by
  ext x
  simp only [Finset.mem_compl, ShufflePath.mem_swapSteps, Finset.mem_map_equiv,
    Equiv.symm_swap]

/-- 概要：異なる向きの二辺を交換した後も二辺の向きは異なる（Berger–Fresse §1.1.3）。
方針：交換後の各端点の所属を交換前の反対側の所属で判定する。
規約：辺の隣接性は不要である。
使われ方：相殺の involution が混合角の集合を保つことを示す。 -/
lemma ShufflePath.swapSteps_crossed {p q : ℕ} (s : ShufflePath p q)
    (a b : Fin (p + q)) (hcross : a ∈ s.val ↔ b ∉ s.val) :
    a ∈ (s.swapSteps a b).val ↔ b ∉ (s.swapSteps a b).val := by
  simp only [ShufflePath.mem_swapSteps, Equiv.swap_apply_left, Equiv.swap_apply_right]
  tauto

/-- 概要：異なる向きの二辺の交換は経路を固定しない（Berger–Fresse §1.1.3）。
方針：第一の端点の所属が反転することを使う。
規約：隣接していない辺についても成立する。
使われ方：混合角の境界項の相殺に固定点がないことを保証する。 -/
lemma ShufflePath.swapSteps_ne_self {p q : ℕ} (s : ShufflePath p q)
    (a b : Fin (p + q)) (hcross : a ∈ s.val ↔ b ∉ s.val) : s.swapSteps a b ≠ s := by
  intro h
  have hm : a ∈ (s.swapSteps a b).val ↔ a ∈ s.val := by rw [h]
  simp only [ShufflePath.mem_swapSteps, Equiv.swap_apply_left] at hm
  tauto

/-- 概要：異なる向きの隣接辺の交換は shuffle 置換への一つの互換の合成である（Berger–Fresse §1.1.3）。
方針：水平・垂直の各ブロックの昇順列挙が隣接交換で移ることを使う。
規約：hcross は一方の辺だけが水平であることを表す。
使われ方：交換による signature の反転を証明する。 -/
lemma ShufflePath.permutation_swapSteps {p q : ℕ} (s : ShufflePath p q)
    (a b : Fin (p + q)) (hab : b.val = a.val + 1) (hcross : a ∈ s.val ↔ b ∉ s.val) :
    (s.swapSteps a b).permutation = Equiv.swap a b * s.permutation := by
  have hs : ¬ (a ∈ s.val ∧ b ∈ s.val) := fun h => (hcross.mp h.1) h.2
  have hc : ¬ (a ∈ s.valᶜ ∧ b ∈ s.valᶜ) := fun h =>
    (Finset.mem_compl.mp h.1) (hcross.mpr (Finset.mem_compl.mp h.2))
  apply Equiv.ext
  intro x
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective x
  cases j with
  | inl j =>
    change (s.swapSteps a b).permutation (Fin.castAdd q j) =
      Equiv.swap a b (s.permutation (Fin.castAdd q j))
    rw [ShufflePath.permutation_castAdd, ShufflePath.permutation_castAdd]
    simp only [Finset.coe_orderIsoOfFin_apply]
    exact congrFun (orderEmbOfFin_map_perm s.val s.property (Equiv.swap a b)
      (swap_adjacent_strictMonoOn a b hab s.val hs)) j
  | inr j =>
    change (s.swapSteps a b).permutation (Fin.natAdd p j) =
      Equiv.swap a b (s.permutation (Fin.natAdd p j))
    rw [ShufflePath.permutation_natAdd, ShufflePath.permutation_natAdd]
    simp only [Finset.coe_orderIsoOfFin_apply]
    simp only [s.swapSteps_compl a b]
    exact congrFun (orderEmbOfFin_map_perm s.valᶜ s.compl_card (Equiv.swap a b)
      (swap_adjacent_strictMonoOn a b hab s.valᶜ hc)) j

/-- 概要：異なる向きの隣接辺の交換で shuffle の符号が反転する（Berger–Fresse §1.1.3）。
方針：shuffle 置換への互換の合成と、互換の signature が −1 であることを使う。
規約：符号は整数の単元としての等式。
使われ方：混合角の境界項の符号つき相殺を与える。 -/
lemma ShufflePath.sign_swapSteps {p q : ℕ} (s : ShufflePath p q)
    (a b : Fin (p + q)) (hab : b.val = a.val + 1) (hcross : a ∈ s.val ↔ b ∉ s.val) :
    (s.swapSteps a b).sign = -s.sign := by
  have hne : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    omega
  rw [ShufflePath.sign, s.permutation_swapSteps a b hab hcross, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap hne, neg_one_mul]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
