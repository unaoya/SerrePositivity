module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleSign

/-!
# shuffle 置換の特徴づけ

概要：Berger–Fresse §1.1.3 の shuffle 置換を二つの昇順ブロックと水平辺集合で特徴づける。
方針：有限集合の昇順列挙の一意性を水平・垂直の各ブロックに適用する。
規約：第一ブロックは位置が p 未満、第二ブロックは p 以上である。
使われ方：一辺を削除した置換を小さい shuffle の置換と同定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：shuffle 置換は第一ブロックをちょうど水平辺集合へ送る（Berger–Fresse §1.1.3）。
方針：入力を水平ブロックと垂直ブロックに分けて昇順列挙の所属を使う。
規約：ブロックの境目は自然数 p で判定する。
使われ方：削除する辺の向きから対応する入力ブロックを判定する。 -/
lemma ShufflePath.permutation_mem_iff {p q : ℕ} (s : ShufflePath p q) (x : Fin (p + q)) :
    s.permutation x ∈ s.val ↔ x.val < p := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective x
  cases j with
  | inl j =>
    change s.permutation (Fin.castAdd q j) ∈ s.val ↔ j.val < p
    rw [s.permutation_castAdd]
    exact iff_of_true (s.val.orderIsoOfFin s.property j).property j.isLt
  | inr j =>
    change s.permutation (Fin.natAdd p j) ∈ s.val ↔ p + j.val < p
    rw [s.permutation_natAdd]
    exact iff_of_false (Finset.mem_compl.mp (s.valᶜ.orderIsoOfFin s.compl_card j).property)
      (by omega)

/-- 概要：shuffle 置換は第一ブロック上で狭義単調である（Berger–Fresse §1.1.3）。
方針：境目未満の入力を Fin p の値として読み直す。
規約：部分集合上の単調性で述べる。
使われ方：一点を削除した置換の第一ブロックの単調性を示す。 -/
lemma ShufflePath.permutation_strictMonoOn_left {p q : ℕ} (s : ShufflePath p q) :
    StrictMonoOn s.permutation {x | x.val < p} := by
  intro x hx y hy hxy
  exact s.permutation_horizontal_strictMono (a := ⟨x.val, hx⟩) (b := ⟨y.val, hy⟩) hxy

/-- 概要：shuffle 置換は第二ブロック上で狭義単調である（Berger–Fresse §1.1.3）。
方針：境目以上の入力から p を引いて Fin q の値として読む。
規約：p 以上という部分集合で述べる。
使われ方：一点を削除した置換の第二ブロックの単調性を示す。 -/
lemma ShufflePath.permutation_strictMonoOn_right {p q : ℕ} (s : ShufflePath p q) :
    StrictMonoOn s.permutation {x | p ≤ x.val} := by
  intro x hx y hy hxy
  change p ≤ x.val at hx
  change p ≤ y.val at hy
  change x.val < y.val at hxy
  let ix : Fin q := ⟨x.val - p, by have h := x.isLt; omega⟩
  let iy : Fin q := ⟨y.val - p, by have h := y.isLt; omega⟩
  have hx' : Fin.natAdd p ix = x := by apply Fin.ext; change p + (x.val - p) = x.val; omega
  have hy' : Fin.natAdd p iy = y := by apply Fin.ext; change p + (y.val - p) = y.val; omega
  rw [← hx', ← hy']
  apply s.permutation_vertical_strictMono
  change x.val - p < y.val - p
  omega

/-- 概要：二ブロックが昇順で水平辺集合と対応する置換は shuffle 置換に一致する（Berger–Fresse §1.1.3）。
方針：水平辺と垂直辺の各昇順列挙の一意性を使う。
規約：任意の置換に対する判定であり、別の shuffle であるとは仮定しない。
使われ方：辺を削除した置換と、経路から定義した小さい shuffle 置換を同定する。 -/
lemma ShufflePath.permutation_eq_of_blocks {p q : ℕ} (s : ShufflePath p q)
    (σ : Equiv.Perm (Fin (p + q)))
    (hleft : StrictMonoOn σ {x | x.val < p})
    (hright : StrictMonoOn σ {x | p ≤ x.val})
    (hmem : ∀ x, σ x ∈ s.val ↔ x.val < p) : σ = s.permutation := by
  have hH := Finset.orderEmbOfFin_unique s.property
    (f := fun j : Fin p => σ (Fin.castAdd q j))
    (fun j => (hmem _).2 j.isLt)
    (fun j k hjk => hleft j.isLt k.isLt hjk)
  have hV := Finset.orderEmbOfFin_unique s.compl_card
    (f := fun j : Fin q => σ (Fin.natAdd p j))
    (fun j => Finset.mem_compl.mpr (fun h => by
      have hh := (hmem _).1 h
      change p + j.val < p at hh
      omega))
    (fun j k hjk => hright (by change p ≤ p + j.val; omega)
      (by change p ≤ p + k.val; omega)
      (by change p + j.val < p + k.val; exact Nat.add_lt_add_left hjk p))
  apply Equiv.ext
  intro x
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective x
  cases j with
  | inl j =>
    change σ (Fin.castAdd q j) = s.permutation (Fin.castAdd q j)
    rw [s.permutation_castAdd, Finset.coe_orderIsoOfFin_apply]
    exact congrFun hH j
  | inr j =>
    change σ (Fin.natAdd p j) = s.permutation (Fin.natAdd p j)
    rw [s.permutation_natAdd, Finset.coe_orderIsoOfFin_apply]
    exact congrFun hV j

end SerrePositivity.EInfinity.BarrattEccles
