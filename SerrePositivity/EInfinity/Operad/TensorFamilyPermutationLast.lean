module

public import SerrePositivity.EInfinity.Operad.TensorFamilyPermutations
public import SerrePositivity.EInfinity.Operad.BlockPermutationAssociativity

/-!
# 全入力のブロック置換から最後のブロックを分離する

概要：Berger–Moerdijk §1 の全入力への合成で、先頭から定義した入力置換を最後の入力で分解する。
方針：ブロック置換の結合性と arity の等式による共役を用いて、有限族の長さで帰納する。
規約：内側 arity 0 と空の前半の族を含む。
使われ方：最後の入力から定義したオペラッド合成の等変性を証明する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity

open scoped BigOperators

/-- 概要：ブロック内の置換の連結は最後のブロックの分離と両立する（Berger–Moerdijk §1）。
方針：三つのブロックの結合性で先頭からの再帰を最後のブロックの分離へ組み替える。
規約：出力の長さを前半の arity の総和と最後の arity の和へ移送する。
使われ方：全入力への合成の等変性の帰納法で、最後の内側置換を分離する。 -/
lemma tensorFamilyPermutation_splitLast (n : ℕ) (s : Fin (n + 1) → ℕ)
    (τ : ∀ i, Equiv.Perm (Fin (s i))) :
    (finCongr (Fin.sum_univ_castSucc s)).permCongr (tensorFamilyPermutation (n + 1) s τ) =
      FiniteBijection.blockEquiv
        (tensorFamilyPermutation n (fun i => s i.castSucc) (fun i => τ i.castSucc))
        (τ (Fin.last n)) := by
  induction n with
  | zero =>
    simp only [tensorFamilyPermutation, Fin.sum_univ_zero]
    erw [blockEquiv_zero_right, finCongr_permCongr_trans, blockEquiv_zero_left]
    rfl
  | succ n ih =>
    have ht : tensorFamilyPermutation (n + 1) (fun i => s i.succ) (fun i => τ i.succ) =
        (finCongr (Fin.sum_univ_castSucc (fun i => s i.succ)).symm).permCongr
          (FiniteBijection.blockEquiv
            (tensorFamilyPermutation n (fun i => s i.castSucc.succ) (fun i => τ i.castSucc.succ))
            (τ (Fin.last n).succ)) := by
      have h := ih (fun i => s i.succ) (fun i => τ i.succ)
      exact ((finCongr (Fin.sum_univ_castSucc (fun i => s i.succ))).permCongr).injective
        (by rw [h, finCongr_permCongr_trans]; rfl)
    rw [tensorFamilyPermutation, ht, blockEquiv_permCongr_right, finCongr_permCongr_trans]
    conv_rhs => rw [tensorFamilyPermutation]
    rw [blockEquiv_permCongr_left, blockEquiv_assoc, finCongr_permCongr_trans]
    rfl

end SerrePositivity.EInfinity
