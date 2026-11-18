module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionFiber
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionCancellation

/-!
模型。文献の定義との比較は後で
# 全 Schedule の実際の残余和は零

概要：Berger–Fresse §1.4.4 の TR の微分に残る全ての削除項を相殺する。
方針：Schedule の fiber ごとに全成功削除点の和と同定し、全単射の相殺を適用する。
規約：零性や微分保存を追加仮定せず、退化出力も削除和に保持する。
使われ方：元の正規化 TR の一般の微分保存を完成する。
-/

@[expose] public section

noncomputable section

universe u


namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.Classical in
/-- 概要：一つの Schedule の残余項は成功削除点の fiber の和（BF §1.4.4）。
方針：失敗時は fiber が空、成功時は出力位置の有限和に同定する。
規約：削除後次数は d。
使われ方：全 Schedule の残余和と成功点の和を照合する。 -/
lemma remainderTerm_eq_sum_fiber (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm A w r =
      ∑ p : {p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w // p.schedule = r}, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue A p.val := by
  classical
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm
  split
  · rename_i hnone
    have hempty : IsEmpty {p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w // p.schedule = r} := ⟨by
      intro p
      have hp := p.val.success
      rw [p.property, hnone] at hp
      cases hp⟩
    let _ := hempty
    exact (Fintype.sum_empty _).symm
  · rename_i out h
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_fiber_remainingValue A w r out h, ← Finset.sum_filter]
    congr 1
    ext k
    simp

/-- 概要：全 Schedule の残余和は全成功削除点上の残余和（BF §1.4.4）。
方針：一つの Schedule の fiber の式を加算し fiber ごとの有限和を統合する。
規約：失敗する Schedule も元の和に含む。
使われ方：検証済みの二種類の全単射による相殺を元の remainderTerm へ戻す。 -/
lemma sum_remainderTerm_eq_points (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) :
    (∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm A w r) =
      ∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue A p := by
  classical
  simp_rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm_eq_sum_fiber]
  exact Fintype.sum_fiberwise (fun p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DeletionPoint w => p.schedule) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainingValue A)

/-- 概要：TR の微分の全残余和は零（BF §1.4.4）。
方針：成功削除点の有限和へ移し、二種類の削除の全単射と逆符号で相殺する。
規約：任意の可換環、全 arity、全正次数で追加仮定なし。
使われ方：TR の微分保存と χ の平方零へ進む。 -/
lemma sum_remainderTerm_zero (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) :
    (∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.remainderTerm A w r) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_remainderTerm_eq_points, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_remainingValue_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
