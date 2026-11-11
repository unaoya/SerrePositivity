module

public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphProper
public import SerrePositivity.EInfinity.Hammock.ReductionExistence
public import SerrePositivity.EInfinity.Hammock.ReductionNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSimplicialSet

/-!
# 任意の可換環上の元の未縮約 hammock の基本縮約

概要：元の全語の全単体の基本縮約と、縮約済みの代表への到達を構成する。
方針：実際の E 代数の弱同値を、構成済みの元の二操作に代入する。
規約：モデル構造は局所的に選び、合流性や一意性の完成はまだ主張しない。
使われ方：同じ元の E 代数の縮約 hammock と余極限の実同型。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)

abbrev algebraHammockRaw (n : SimplexCategoryᵒᵖ) : Type (u + 1) :=
  let := modelCategory A
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock (weakEquivalences (operad A).Algebra) X Y n

def algebraHammockRawMap {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (r : algebraHammockRaw A X Y n) : algebraHammockRaw A X Y m := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.map _ X Y α r

def algebraHammockRawValue {n : SimplexCategoryᵒᵖ} (r : algebraHammockRaw A X Y n) :
    (algebraHammockColimitGraph A X Y).obj n := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value _ X Y r

def algebraHammockRawIsReduced {n : SimplexCategoryᵒᵖ} (r : algebraHammockRaw A X Y n) : Prop := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced _ X Y r

def algebraHammockRawReduction {n : SimplexCategoryᵒᵖ} (r s : algebraHammockRaw A X Y n) :
    Prop := by
  let := modelCategory A
  exact Hammock.Reduction _ X Y n r s

lemma algebraHammockRawReduction_length_lt {n : SimplexCategoryᵒᵖ}
    {r s : algebraHammockRaw A X Y n} (h : algebraHammockRawReduction A X Y r s) :
    s.1.length < r.1.length := by
  let := modelCategory A
  exact Hammock.Reduction.length_lt h

lemma algebraHammockRawReduction_value_eq {n : SimplexCategoryᵒᵖ}
    {r s : algebraHammockRaw A X Y n} (h : algebraHammockRawReduction A X Y r s) :
    algebraHammockRawValue A X Y r = algebraHammockRawValue A X Y s := by
  let := modelCategory A
  exact Hammock.Reduction.value_eq h

lemma algebraHammockRawReduction_map {n m : SimplexCategoryᵒᵖ}
    {r s : algebraHammockRaw A X Y n} (h : algebraHammockRawReduction A X Y r s) (α : n ⟶ m) :
    algebraHammockRawReduction A X Y (algebraHammockRawMap A X Y α r)
      (algebraHammockRawMap A X Y α s) := by
  let := modelCategory A
  exact Hammock.Reduction.map h α

/-- 全次数の元の未縮約 hammock は、有限回の基本縮約で縮約済みの代表へ到達する。 -/
lemma algebraHammockRaw_existsReducedRepresentative {n : SimplexCategoryᵒᵖ}
    (r : algebraHammockRaw A X Y n) :
    ∃ s, Relation.ReflTransGen (algebraHammockRawReduction A X Y) r s ∧
      algebraHammockRawIsReduced A X Y s := by
  let := modelCategory A
  exact Hammock.exists_reduced_representative _ X Y n r

lemma algebraHammockRaw_existsReducedSameValue {n : SimplexCategoryᵒᵖ}
    (r : algebraHammockRaw A X Y n) :
    ∃ s, algebraHammockRawIsReduced A X Y s ∧
      algebraHammockRawValue A X Y r = algebraHammockRawValue A X Y s := by
  let := modelCategory A
  exact Hammock.exists_reduced_same_value _ X Y n r

lemma algebraHammockRaw_reduced_iff_no_reduction {n : SimplexCategoryᵒᵖ}
    (r : algebraHammockRaw A X Y n) :
    algebraHammockRawIsReduced A X Y r ↔ ∀ s, ¬ algebraHammockRawReduction A X Y r s := by
  let := modelCategory A
  exact Hammock.reduced_iff_no_reduction _ X Y n r

/-- 同じ元の全語の全射列からなる未縮約単体集合。 -/
def algebraHammockRawSimplicialSet : SSet.{u + 1} := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSimplicialSet.simplicialSet (weakEquivalences (operad A).Algebra) X Y

/-- 同じ元の全標準射からなる、元の余極限への射。 -/
def algebraHammockRawAugmentation :
    algebraHammockRawSimplicialSet A X Y ⟶ algebraHammockColimitGraph A X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSimplicialSet.augmentation (weakEquivalences (operad A).Algebra) X Y

lemma algebraHammockRawAugmentation_app (n : SimplexCategoryᵒᵖ) (r : algebraHammockRaw A X Y n) :
    (algebraHammockRawAugmentation A X Y).app n r = algebraHammockRawValue A X Y r := rfl

end SerrePositivity.EInfinity.BarrattEccles
