module

public import SerrePositivity.EInfinity.BarrattEccles.HammockErasureConfluence
public import SerrePositivity.EInfinity.BarrattEccles.HammockMergeConfluence
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ReducedSimplicialSet

/-!
# 任意の可換環上の元の hammock の正規化

概要：元の基本縮約の合流性、一意な代表、全単体的な正規化と標準射を提供する。
方針：実際の E 代数の弱同値に元の局所合流・Church–Rosser・正規形を代入する。
規約：モデル構造は局所的に選ぶ。全語の余極限との同型は後続。
使われ方：元の縮約 hammock と単体的局所化の比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory _root_.HomotopicalAlgebra

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)

lemma algebraHammockMergeErase_join {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p : Fin (k + 1)) (hp : d p.castSucc = d p.succ) (j : Fin (k + 2))
    {n : SimplexCategoryᵒᵖ}
    (τ : (algebraHammockGraph A (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n)
    (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j) :
    ∃ s : algebraHammockRaw A X Y n,
      Relation.ReflGen (algebraHammockRawReduction A X Y)
        (algebraHammockMergeRaw A X Y d p hp τ) s ∧
      Relation.ReflGen (algebraHammockRawReduction A X Y)
        (algebraHammockEraseRaw A X Y j τ hτ) s := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.merge_erase_join (weakEquivalences (operad A).Algebra) X Y d p hp j τ hτ

lemma algebraHammockRawReduction_local_join {n : SimplexCategoryᵒᵖ}
    {r s t : algebraHammockRaw A X Y n}
    (hs : algebraHammockRawReduction A X Y r s) (ht : algebraHammockRawReduction A X Y r t) :
    ∃ q, Relation.ReflGen (algebraHammockRawReduction A X Y) s q ∧
      Relation.ReflGen (algebraHammockRawReduction A X Y) t q := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reduction_local_join _ X Y n hs ht

lemma algebraHammockRawReduction_church_rosser {n : SimplexCategoryᵒᵖ}
    {r s t : algebraHammockRaw A X Y n}
    (hs : Relation.ReflTransGen (algebraHammockRawReduction A X Y) r s)
    (ht : Relation.ReflTransGen (algebraHammockRawReduction A X Y) r t) :
    Relation.Join (Relation.ReflTransGen (algebraHammockRawReduction A X Y)) s t := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reduction_church_rosser _ X Y n hs ht

lemma algebraHammockReducedRepresentative_unique {n : SimplexCategoryᵒᵖ}
    {r s t : algebraHammockRaw A X Y n}
    (hs : Relation.ReflTransGen (algebraHammockRawReduction A X Y) r s)
    (ht : Relation.ReflTransGen (algebraHammockRawReduction A X Y) r t)
    (hsr : algebraHammockRawIsReduced A X Y s) (htr : algebraHammockRawIsReduced A X Y t) :
    s = t := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reduced_representative_unique _ X Y n hs ht hsr htr

/-- 同じ元の有限縮約で得る、一意な縮約済みの代表。 -/
def algebraHammockNormalForm {n : SimplexCategoryᵒᵖ}
    (r : algebraHammockRaw A X Y n) : algebraHammockRaw A X Y n := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm _ X Y n r

lemma algebraHammockNormalForm_chain {n : SimplexCategoryᵒᵖ} (r : algebraHammockRaw A X Y n) :
    Relation.ReflTransGen (algebraHammockRawReduction A X Y) r
      (algebraHammockNormalForm A X Y r) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm_chain _ X Y n r

lemma algebraHammockNormalForm_reduced {n : SimplexCategoryᵒᵖ} (r : algebraHammockRaw A X Y n) :
    algebraHammockRawIsReduced A X Y (algebraHammockNormalForm A X Y r) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm_reduced _ X Y n r

lemma algebraHammockNormalForm_eq_self {n : SimplexCategoryᵒᵖ} {r : algebraHammockRaw A X Y n}
    (hr : algebraHammockRawIsReduced A X Y r) : algebraHammockNormalForm A X Y r = r := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm_eq_self _ X Y n hr

lemma algebraHammockNormalForm_value {n : SimplexCategoryᵒᵖ} (r : algebraHammockRaw A X Y n) :
    algebraHammockRawValue A X Y (algebraHammockNormalForm A X Y r) =
      algebraHammockRawValue A X Y r := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm_value _ X Y n r

lemma algebraHammockNormalForm_map {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (r : algebraHammockRaw A X Y n) :
    algebraHammockNormalForm A X Y
        (algebraHammockRawMap A X Y α (algebraHammockNormalForm A X Y r)) =
      algebraHammockNormalForm A X Y (algebraHammockRawMap A X Y α r) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm_map_normalForm _ X Y n α r

/-- 再縮約した全作用素を持つ、元の縮約済みの対象の単体集合。 -/
def algebraHammockReducedSimplicialSet : SSet.{u + 1} := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet (weakEquivalences (operad A).Algebra) X Y

def algebraHammockNormalization :
    algebraHammockRawSimplicialSet A X Y ⟶ algebraHammockReducedSimplicialSet A X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalization (weakEquivalences (operad A).Algebra) X Y

def algebraHammockReducedAugmentation :
    algebraHammockReducedSimplicialSet A X Y ⟶ algebraHammockColimitGraph A X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedAugmentation (weakEquivalences (operad A).Algebra) X Y

lemma algebraHammockNormalization_augmentation :
    algebraHammockNormalization A X Y ≫ algebraHammockReducedAugmentation A X Y =
      algebraHammockRawAugmentation A X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalization_augmentation (weakEquivalences (operad A).Algebra) X Y

end SerrePositivity.EInfinity.BarrattEccles
