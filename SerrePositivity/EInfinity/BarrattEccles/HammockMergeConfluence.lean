module

public import SerrePositivity.EInfinity.BarrattEccles.HammockReduction
public import SerrePositivity.EInfinity.Hammock.MergeMergeConfluence

/-!
# 任意の可換環上の元の隣接合成の局所合流

概要：元の全次数の二つの隣接合成は、各側0〜1段で同じ元の対象へ到達する。
方針：二重全射の合成則と元の色の回収を、実際の E 代数の弱同値に代入する。
規約：モデル構造は局所的に選ぶ。削除との混合の場合は別に証明する。
使われ方：元の E 代数の縮約済みの代表の一意性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)

/-- 元の隣接二列の合成による未縮約対象。 -/
def algebraHammockMergeRaw {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p : Fin (k + 1)) (hp : d p.castSucc = d p.succ) {n : SimplexCategoryᵒᵖ}
    (τ : (algebraHammockGraph A (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n) :
    algebraHammockRaw A X Y n :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d p,
    (algebraHammockGraphMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp) X Y).app n τ⟩

lemma algebraHammockMergeRaw_reduction {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p : Fin (k + 1)) (hp : d p.castSucc = d p.succ) {n : SimplexCategoryᵒᵖ}
    (τ : (algebraHammockGraph A (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n) :
    algebraHammockRawReduction A X Y ⟨⟨k + 2, d⟩, τ⟩
      (algebraHammockMergeRaw A X Y d p hp τ) := by
  let := modelCategory A
  exact Hammock.Reduction.merge d p hp τ

/-- 同じ位置・接した位置・離れた位置の合成を全次数で同時に扱う。 -/
lemma algebraHammockMergeMerge_join {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p q : Fin (k + 1)) (hp : d p.castSucc = d p.succ) (hq : d q.castSucc = d q.succ)
    {n : SimplexCategoryᵒᵖ}
    (τ : (algebraHammockGraph A (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n) :
    ∃ r : algebraHammockRaw A X Y n,
      Relation.ReflGen (algebraHammockRawReduction A X Y)
        (algebraHammockMergeRaw A X Y d p hp τ) r ∧
      Relation.ReflGen (algebraHammockRawReduction A X Y)
        (algebraHammockMergeRaw A X Y d q hq τ) r := by
  let := modelCategory A
  exact Hammock.merge_merge_join (weakEquivalences (operad A).Algebra) X Y d p q hp hq τ

end SerrePositivity.EInfinity.BarrattEccles
