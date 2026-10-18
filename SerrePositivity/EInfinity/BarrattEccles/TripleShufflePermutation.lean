module

public import SerrePositivity.EInfinity.BarrattEccles.TripleShuffleEnumeration
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleBlockPermutation

/-!
# 三入力の shuffle 置換の結合則

概要：Berger–Fresse §1.1.3 の二段の shuffle 置換は括弧付けによらない。
方針：入力を三つの有限ブロックに分け、各色の辺の昇順列挙の一致を使う。
規約：p+q+r と p+(q+r) は標準の有限全単射で移送する。
使われ方：三入力の shuffle の符号の積を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：反復 shuffle の辺の置換は次数移送と可換である（Berger–Fresse §1.1.3）。
方針：各入力ブロックで辺の昇順列挙の一致を適用する。
規約：置換は内側のブロック置換を先に適用する。
使われ方：二つの括弧付けの置換の共役による一致を得る。 -/
lemma tripleShuffle_permutation_apply (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (a : Fin (p + q + r)) :
    Fin.cast (Nat.add_assoc p q r)
        (v.1.permutation (shuffleBlockPermutation v.2.permutation (1 : Equiv.Perm (Fin r)) a)) =
      (tripleShuffleEquiv p q r v).1.permutation
        (shuffleBlockPermutation (1 : Equiv.Perm (Fin p))
          (tripleShuffleEquiv p q r v).2.permutation (Fin.cast (Nat.add_assoc p q r) a)) := by
  obtain ⟨a | a, rfl⟩ := (finSumFinEquiv : Fin (p + q) ⊕ Fin r ≃ _).surjective a
  · obtain ⟨a | a, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin q ≃ _).surjective a
    · simp only [finSumFinEquiv_apply_left]
      have h : Fin.cast (Nat.add_assoc p q r) (Fin.castAdd r (Fin.castAdd q a)) =
          Fin.castAdd (q + r) a := by apply Fin.ext; rfl
      rw [h, shuffleBlockPermutation_castAdd, shuffleBlockPermutation_castAdd]
      simp only [Equiv.Perm.one_apply, ShufflePath.permutation_castAdd]
      exact tripleShuffle_first_enumeration p q r v a
    · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
      have h : Fin.cast (Nat.add_assoc p q r) (Fin.castAdd r (Fin.natAdd p a)) =
          Fin.natAdd p (Fin.castAdd r a) := by apply Fin.ext; rfl
      rw [h, shuffleBlockPermutation_castAdd, shuffleBlockPermutation_natAdd]
      simp only [ShufflePath.permutation_castAdd, ShufflePath.permutation_natAdd]
      exact tripleShuffle_second_enumeration p q r v a
  · simp only [finSumFinEquiv_apply_right]
    have h : Fin.cast (Nat.add_assoc p q r) (Fin.natAdd (p + q) a) =
        Fin.natAdd p (Fin.natAdd q a) := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd]
      omega
    rw [h, shuffleBlockPermutation_natAdd, shuffleBlockPermutation_natAdd]
    simp only [Equiv.Perm.one_apply, ShufflePath.permutation_natAdd]
    exact tripleShuffle_third_enumeration p q r v a

/-- 概要：反復 shuffle 置換の積は次数移送で一致する（Berger–Fresse §1.1.3）。
方針：各点での可換性から置換の外延性を使う。
規約：積の右因子が内側のブロック置換である。
使われ方：符号準同型を適用して反復 shuffle の符号を比較する。 -/
lemma tripleShuffle_permutation (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    (finCongr (Nat.add_assoc p q r)).permCongr
        (v.1.permutation * shuffleBlockPermutation v.2.permutation (1 : Equiv.Perm (Fin r))) =
      (tripleShuffleEquiv p q r v).1.permutation *
        shuffleBlockPermutation (1 : Equiv.Perm (Fin p))
          (tripleShuffleEquiv p q r v).2.permutation := by
  apply Equiv.ext
  intro a
  obtain ⟨b, rfl⟩ := (finCongr (Nat.add_assoc p q r)).surjective a
  simpa using tripleShuffle_permutation_apply p q r v b

/-- 概要：二段の shuffle の符号の積は括弧付けによらない（Berger–Fresse §1.1.3）。
方針：置換の積の等式に符号準同型を適用する。
規約：外側の符号を先に、内側の符号を後に掛ける。
使われ方：shuffle 合成の結合則の二重和の係数を同定する。 -/
lemma tripleShuffle_sign (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    v.1.sign * v.2.sign = (tripleShuffleEquiv p q r v).1.sign *
      (tripleShuffleEquiv p q r v).2.sign := by
  have h := congrArg Equiv.Perm.sign (tripleShuffle_permutation p q r v)
  simpa only [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_mul, shuffleBlockPermutation_sign,
    Equiv.Perm.sign_one, mul_one, one_mul, ShufflePath.sign] using h

end SerrePositivity.EInfinity.BarrattEccles
