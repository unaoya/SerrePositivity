module

public import SerrePositivity.EInfinity.BarrattEccles.HammockReduction
public import SerrePositivity.EInfinity.Hammock.EraseEraseConfluence

/-!
# 任意の可換環上の元の恒等列削除の局所合流

概要：元の全次数の二つの恒等列削除は、両側0〜1段で同じ元の対象へ到達する。
方針：実際の E 代数の弱同値に、元の回収・単射性・二列の削除の照合を代入する。
規約：モデル構造は局所的に選び、基本縮約全体の合流性はまだ主張しない。
使われ方：元の E 代数の縮約済みの代表の一意性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory _root_.HomotopicalAlgebra

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)

def algebraHammockEraseSimplex {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (j : Fin w.length) {n : SimplexCategoryᵒᵖ}
    (τ : (algebraHammockGraph A w X Y).obj n) (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j) :
    (algebraHammockGraph A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w j) X Y).obj n := by
  let := modelCategory A
  exact Hammock.eraseSimplex (weakEquivalences (operad A).Algebra) X Y j τ hτ

lemma algebraHammockEraseSimplex_fac {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (j : Fin w.length)
    {n : SimplexCategoryᵒᵖ} (τ : (algebraHammockGraph A w X Y).obj n)
    (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j) :
    (algebraHammockGraphMap A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w j) X Y).app n
        (algebraHammockEraseSimplex A X Y j τ hτ) = τ := by
  let := modelCategory A
  exact Hammock.eraseSimplex_fac (weakEquivalences (operad A).Algebra) X Y j τ hτ

/-- 同じ元の全射列を保持する、基本削除後の未縮約対象。 -/
def algebraHammockEraseRaw {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (j : Fin w.length) {n : SimplexCategoryᵒᵖ}
    (τ : (algebraHammockGraph A w X Y).obj n) (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j) :
    algebraHammockRaw A X Y n :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w j, algebraHammockEraseSimplex A X Y j τ hτ⟩

lemma algebraHammockEraseRaw_reduction {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (j : Fin w.length)
    {n : SimplexCategoryᵒᵖ} (τ : (algebraHammockGraph A w X Y).obj n)
    (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j) :
    algebraHammockRawReduction A X Y ⟨w, τ⟩ (algebraHammockEraseRaw A X Y j τ hτ) := by
  let := modelCategory A
  exact Hammock.Reduction.erase j τ hτ

/-- 元の二つの削除は全次数で、各側0〜1段の同じ元の対象への合流を持つ。 -/
lemma algebraHammockEraseErase_join {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {n : SimplexCategoryᵒᵖ}
    (τ : (algebraHammockGraph A w X Y).obj n) (j k : Fin w.length)
    (hj : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j) (hk : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) k) :
    ∃ q : algebraHammockRaw A X Y n,
      Relation.ReflGen (algebraHammockRawReduction A X Y) (algebraHammockEraseRaw A X Y j τ hj) q ∧
      Relation.ReflGen (algebraHammockRawReduction A X Y)
        (algebraHammockEraseRaw A X Y k τ hk) q := by
  let := modelCategory A
  exact Hammock.erase_erase_join (weakEquivalences (operad A).Algebra) X Y τ j k hj hk

end SerrePositivity.EInfinity.BarrattEccles
