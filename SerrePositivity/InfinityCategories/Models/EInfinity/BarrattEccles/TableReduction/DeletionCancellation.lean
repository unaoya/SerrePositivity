module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionSum

/-!
模型。文献の定義との比較は後で
# 全成功削除点上の残余和の相殺

概要：Berger–Fresse §1.4.4 の残余二種類の有限和が零になることを証明する。
方針：逆対応の各二項の相殺を全単射で最終出現側の和へ付け替える。
規約：任意の可換環、全 arity・全次数、退化出力を含む。
使われ方：元の Schedule ごとの remainderTerm の和の消滅へ接続する。
-/

@[expose] public section

noncomputable section

universe u


namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：残余区切り削除と逆対応する最終出現削除の項は相殺（BF §1.4.4）。
方針：実際の逆構成の二項の相殺を有限削除点の評価へ移す。
規約：削除後次数は d。
使われ方：全残余和の一項ごとの相殺。 -/
lemma backwardDeletion_cancel (A : Type u) [CommRing A] {n d : ℕ}
    {w : Fin (d + 2) → Equiv.Perm (Fin n)} (q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CaesuraDeletion w) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletion q).val + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A q.val = 0 := by
  have ht := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletionData q).pair_cancel A q.val.success
  have ht' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A q.val + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletion q).val = 0 := by
    simpa only [Nat.add_sub_cancel, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletion, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reverseDeletionTarget] using ht
  simpa only [add_comm] using ht'

/-- 概要：全成功削除点上の残余和は零（BF §1.4.4）。
方針：二種類に分割し、全単射の逆で片方の有限和を付け替える。
規約：各二項の相殺は変更後の成功から証明済み。
使われ方：元の TR の微分の残余を消す。 -/
lemma sum_remainingValue_zero (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) :
    (∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue A p) = 0 := by
  classical
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_remainingValue_split]
  have he := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionEquiv w).symm.sum_comp (fun p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FinalDeletion w => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionValue A p.val)
  rw [← he, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro q _
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.backwardDeletion_cancel A q

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
