module
public import SerrePositivity.KST.ProExcision.IdealColumnGroup

/-!
# μ 版 A.5 に渡す実三角ブロック群の積

概要：帰納段階のブロック埋め込みとイデアル内の補助列から μ:P×Q→H を構成する。
方針：固定列・固定行から両因子の像の可換性を導き、実群内で積を取る。
規約：KST Lemma 4.16 の非可換再記述、原典の「標的を可換とする」置換を使わない。
使われ方：因子内の帰納仮定と Q の0次入力を Construction A.5 へ渡す。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：first n 行の既存座標は n 以後に挿入した補助座標より前にある。
方針：指定点の手前の succAbove は castSucc に等しい。
規約：KST 4.16 の n,m−1,1,1 の配置。
使われ方：実補助列の三角条件。 -/
lemma insertion_first_rows_lt {ι : Type v} (n m : ℕ)
    (r : ι → Fin (n + m)) (hr : ∀ i, (r i).val < n)
    (p : Fin (n + m + 1)) (hp : n ≤ p.val) (i : ι) : p.succAbove (r i) < p := by
  have h : (r i).castSucc < p := (hr i).trans_le hp
  rw [Fin.succAbove_of_castSucc_lt _ _ h]
  exact h

/-- 概要：実帰納ブロック群の埋め込みとイデアル内の補助列の像は可換。
方針：埋め込みを固定ブロック群に入れ、実行列の固定行・固定列の可換性を使う。
規約：KST 4.16、I の可換性は不要。P と Q のホモトピーの値域を保つ。
使われ方：μ の乗法保存を保証する。 -/
lemma triangularBlockInsertion_commute_column {ι : Type v} [Fintype ι]
    (n m : ℕ) (J : TwoSidedIdeal R) (r : ι → Fin (n + m)) (hr : ∀ i, (r i).val < n)
    (p : Fin (n + m + 1)) (hp : n ≤ p.val)
    (M : triangularBlockGroup n m J) (v : Multiplicative (ι → J)) :
    Commute (triangularBlockGroupInsertion n m J p M)
      (idealBlockColumnHom n (m + 1) J (p.succAbove ∘ r) p
        (insertion_first_rows_lt n m r hr p hp) hp v) := by
  apply Subtype.ext
  exact (fixedBlockSubgroup_commute_column (p.succAbove ∘ r) p
    (fun i ↦ (insertion_first_rows_lt n m r hr p hp i).ne')
    (triangularBlockInsertionFixedHom n m J r hr p M)
    ((idealVectorInclusion J ι).toMultiplicative v)).eq

/-- 概要：三角ブロック群の帰納段階に使う実 μ:P×Q→H。
方針：第一因子の挿入と第二因子の補助列を、証明済みの可換性で群準同型に束ねる。
規約：KST A.5 の μ 版、Lemma 4.16 の非可換な P,Q,H。
使われ方：C(P) 内の帰納仮定と C(Q) 内の0次入力に最後に μ を適用する。 -/
def triangularBlockProductHom {ι : Type v} [Fintype ι]
    (n m : ℕ) (J : TwoSidedIdeal R) (r : ι → Fin (n + m)) (hr : ∀ i, (r i).val < n)
    (p : Fin (n + m + 1)) (hp : n ≤ p.val) :
    triangularBlockGroup n m J × Multiplicative (ι → J) →* triangularBlockGroup n (m + 1) J :=
  commutingProductHom (triangularBlockGroupInsertion n m J p)
    (idealBlockColumnHom n (m + 1) J (p.succAbove ∘ r) p
      (insertion_first_rows_lt n m r hr p hp) hp)
    (triangularBlockInsertion_commute_column n m J r hr p hp)

end SerrePositivity.KST.ProExcision
