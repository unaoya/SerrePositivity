module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleExchange
public import SerrePositivity.EInfinity.BarrattEccles.BlockExchangeSign

/-!
# shuffle の方向交換と置換の符号

概要：Berger–Fresse §1.1.3 の経路の方向交換をブロック交換の置換で記述する。
方針：各ブロックの昇順列挙を比較して置換の積の等式を得る。
規約：方向交換後の全辺数を元の型へ移送して比較する。
使われ方：並列結合則の二入力の交換の Koszul 符号を得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：交換後の水平辺の列挙は元の垂直辺の列挙の移送である（Berger–Fresse §1.1.3）。
方針：像への所属と狭義単調性で昇順列挙の一意性を使う。
規約：入力番号は Fin q である。
使われ方：交換後の shuffle 置換の最初のブロックを比較する。 -/
lemma ShufflePath.exchange_horizontal_enumeration {p q : ℕ} (s : ShufflePath p q)
    (a : Fin q) :
    Fin.cast (Nat.add_comm p q) (s.valᶜ.orderEmbOfFin s.compl_card a) =
      s.exchange.val.orderEmbOfFin s.exchange.property a := by
  have h := Finset.orderEmbOfFin_unique s.exchange.property
    (f := fun b => Fin.cast (Nat.add_comm p q) (s.valᶜ.orderEmbOfFin s.compl_card b))
    (fun b => Finset.mem_map.mpr ⟨_, s.valᶜ.orderEmbOfFin_mem s.compl_card b, rfl⟩)
    ((Fin.cast_strictMono _).comp (s.valᶜ.orderEmbOfFin s.compl_card).strictMono)
  exact congrFun h a

/-- 概要：交換後の垂直辺の列挙は元の水平辺の列挙の移送である（Berger–Fresse §1.1.3）。
方針：補集合の移送の公式と昇順列挙の一意性を使う。
規約：入力番号は Fin p である。
使われ方：交換後の shuffle 置換の最後のブロックを比較する。 -/
lemma ShufflePath.exchange_vertical_enumeration {p q : ℕ} (s : ShufflePath p q)
    (a : Fin p) :
    Fin.cast (Nat.add_comm p q) (s.val.orderEmbOfFin s.property a) =
      s.exchange.valᶜ.orderEmbOfFin s.exchange.compl_card a := by
  have hc : s.exchange.valᶜ = s.val.map (finCongr (Nat.add_comm p q)).toEmbedding := by
    change (s.valᶜ.map (finCongr (Nat.add_comm p q)).toEmbedding)ᶜ = _
    rw [map_finCongr_compl, compl_compl]
  have h := Finset.orderEmbOfFin_unique s.exchange.compl_card
    (f := fun b => Fin.cast (Nat.add_comm p q) (s.val.orderEmbOfFin s.property b))
    (fun b => by rw [hc]; exact Finset.mem_map.mpr ⟨_, s.val.orderEmbOfFin_mem s.property b, rfl⟩)
    ((Fin.cast_strictMono _).comp (s.val.orderEmbOfFin s.property).strictMono)
  exact congrFun h a

/-- 概要：方向を交換した shuffle 置換とブロック交換の積は元の置換である（Berger–Fresse §1.1.3）。
方針：二つの入力ブロックごとに辺の列挙の公式を適用する。
規約：交換後の置換は全辺数の交換則で元の型へ移送する。
使われ方：符号準同型を適用して方向交換の符号を比較する。 -/
lemma ShufflePath.exchange_permutation {p q : ℕ} (s : ShufflePath p q) :
    (finCongr (Nat.add_comm q p)).permCongr s.exchange.permutation *
        blockExchangePermutation p q = s.permutation := by
  apply Equiv.ext
  intro a
  change Fin.cast (Nat.add_comm q p)
      (s.exchange.permutation
        (Fin.cast (Nat.add_comm q p).symm (blockExchangePermutation p q a))) = s.permutation a
  obtain ⟨a | a, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ _).surjective a
  · simp only [finSumFinEquiv_apply_left]
    have hc : Fin.cast (Nat.add_comm q p).symm
        (blockExchangePermutation p q (Fin.castAdd q a)) = Fin.natAdd q a := by
      apply Fin.ext
      simp only [Fin.val_cast, blockExchangePermutation_castAdd_val, Fin.val_natAdd]
    rw [hc, s.exchange.permutation_natAdd, s.permutation_castAdd]
    change Fin.cast (Nat.add_comm q p)
      (s.exchange.valᶜ.orderEmbOfFin s.exchange.compl_card a) =
        s.val.orderEmbOfFin s.property a
    rw [← s.exchange_vertical_enumeration]
    simp
  · simp only [finSumFinEquiv_apply_right]
    have hc : Fin.cast (Nat.add_comm q p).symm
        (blockExchangePermutation p q (Fin.natAdd p a)) = Fin.castAdd p a := by
      apply Fin.ext
      simp only [Fin.val_cast, blockExchangePermutation_natAdd_val, Fin.val_castAdd]
    rw [hc, s.exchange.permutation_castAdd, s.permutation_natAdd]
    change Fin.cast (Nat.add_comm q p)
      (s.exchange.val.orderEmbOfFin s.exchange.property a) =
        s.valᶜ.orderEmbOfFin s.compl_card a
    rw [← s.exchange_horizontal_enumeration]
    simp

/-- 概要：方向交換後の shuffle 符号とブロック交換の符号の積は元の符号である（Berger–Fresse §1.1.3）。
方針：置換の積の等式に符号準同型を適用する。
規約：ブロック交換の符号は (−1)^(pq) とする。
使われ方：並列結合則の符号付き和の係数を比較する。 -/
lemma ShufflePath.exchange_sign_mul {p q : ℕ} (s : ShufflePath p q) :
    s.exchange.sign * (-1 : ℤˣ) ^ (p * q) = s.sign := by
  have h := congrArg Equiv.Perm.sign s.exchange_permutation
  simpa only [Equiv.Perm.sign_mul, Equiv.Perm.sign_permCongr, blockExchangePermutation_sign,
    ShufflePath.sign] using h

/-- 概要：shuffle の方向交換は Koszul 符号 (−1)^(pq) を掛ける（Berger–Fresse §1.1.3）。
方針：ブロック交換の符号の二乗が1であることを用いる。
規約：整数の単元として符号の等式を述べる。
使われ方：交換した二入力の shuffle 和の係数を与える。 -/
lemma ShufflePath.exchange_sign {p q : ℕ} (s : ShufflePath p q) :
    s.exchange.sign = (-1 : ℤˣ) ^ (p * q) * s.sign := by
  have he : (-1 : ℤˣ) ^ (p * q) * (-1 : ℤˣ) ^ (p * q) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc
    s.exchange.sign = s.exchange.sign *
        ((-1 : ℤˣ) ^ (p * q) * (-1 : ℤˣ) ^ (p * q)) := by rw [he, mul_one]
    _ = (s.exchange.sign * (-1 : ℤˣ) ^ (p * q)) * (-1 : ℤˣ) ^ (p * q) := (mul_assoc _ _ _).symm
    _ = s.sign * (-1 : ℤˣ) ^ (p * q) := by rw [s.exchange_sign_mul]
    _ = (-1 : ℤˣ) ^ (p * q) * s.sign := mul_comm _ _

end SerrePositivity.EInfinity.BarrattEccles
