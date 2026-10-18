module

public import SerrePositivity.EInfinity.Operad.TensorFamilyPermutationLast
public import SerrePositivity.EInfinity.Operad.SlotTailPermutations

/-!
# 全入力への代入の帰納法における尾の置換

概要：Berger–Moerdijk §1 の全入力への合成で、最後の代入後の尾の置換と全入力の置換を比較する。
方針：ブロック置換の結合性、最後のブロックの分離、arity の等式による移送を使う。
規約：代入後の尾の長さは再帰の定義に合わせて k+l とする。
使われ方：全入力への合成の等変性の帰納段階の始域と終域を接続する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity

open scoped BigOperators

/-- 概要：部分合成後の置換は arity の括弧を直すと前方を固定する尾の置換になる（Berger–Moerdijk §1）。
方針：三つのブロックの置換を定義で展開し、右ブロックの移送を外に出す。
規約：挿入された l 個の入力と元の k 個の後方入力を新しい尾とする。
使われ方：部分合成の等変性を全入力への合成の再帰呼び出しへ渡す。 -/
lemma operadInsertedTailPermutation_reassociate (a k l : ℕ)
    (τ : Equiv.Perm (Fin l)) (ρ : Equiv.Perm (Fin k)) :
    (finCongr (Nat.add_assoc a k l)).permCongr (operadInsertedTailPermutation a k l τ ρ) =
      FiniteBijection.blockEquiv (Equiv.refl (Fin a))
        ((finCongr (Nat.add_comm l k)).permCongr (FiniteBijection.blockEquiv τ ρ)) := by
  rw [operadInsertedTailPermutation, finCongr_permCongr_trans, blockEquiv_permCongr_right]

/-- 概要：再帰で得た前半と尾の置換は全入力と元の尾の置換に一致する（Berger–Moerdijk §1）。
方針：全入力の置換の最後のブロックを分離し、三つのブロックの結合性を使う。
規約：再帰から戻る arity の等式は有限和の最後の項の分離で証明する。
使われ方：全入力への合成の等変性の帰納段階の出力の置換をまとめる。 -/
lemma tensorFamilyPermutation_tail_splitLast (n k : ℕ) (s : Fin (n + 1) → ℕ)
    (τ : ∀ i, Equiv.Perm (Fin (s i))) (ρ : Equiv.Perm (Fin k)) :
    (finCongr (by rw [Fin.sum_univ_castSucc]; omega :
      (∑ i : Fin n, s i.castSucc) + (k + s (Fin.last n)) = (∑ i, s i) + k)).permCongr
        (FiniteBijection.blockEquiv
          (tensorFamilyPermutation n (fun i => s i.castSucc) (fun i => τ i.castSucc))
          ((finCongr (Nat.add_comm (s (Fin.last n)) k)).permCongr
            (FiniteBijection.blockEquiv (τ (Fin.last n)) ρ))) =
      FiniteBijection.blockEquiv (tensorFamilyPermutation (n + 1) s τ) ρ := by
  have ht : tensorFamilyPermutation (n + 1) s τ =
      (finCongr (Fin.sum_univ_castSucc s).symm).permCongr
        (FiniteBijection.blockEquiv
          (tensorFamilyPermutation n (fun i => s i.castSucc) (fun i => τ i.castSucc))
          (τ (Fin.last n))) := by
    exact ((finCongr (Fin.sum_univ_castSucc s)).permCongr).injective
      (by rw [tensorFamilyPermutation_splitLast, finCongr_permCongr_trans]; rfl)
  rw [blockEquiv_permCongr_right, finCongr_permCongr_trans, ht,
    blockEquiv_permCongr_left, blockEquiv_assoc, finCongr_permCongr_trans]

end SerrePositivity.EInfinity
