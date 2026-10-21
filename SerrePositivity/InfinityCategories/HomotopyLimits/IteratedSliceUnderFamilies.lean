module

public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinAssociatorInclusions
public import SerrePositivity.InfinityCategories.Core.JoinLifting

/-!
概要：反復 coslice の族を二度 uncurry し、join の結合同型で再結合する。
方針：元の固定図式と可変終点を同じ join の再結合で保持する。
規約：充填条件を追加仮定しない。使われ方：HTT 5.5.4 の局所同値の pushout 保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {K L X A A' : SSet.{u}} {p : K ⟶ X} (q : L ⟶ sliceUnder p)

/-- 反復 coslice の族を元の展開した図式の coslice の族に写す。 -/
def iteratedSliceUnderForwardFamily (s : A ⟶ sliceUnder q) :
    A ⟶ sliceUnder (sliceUnderUncurry q) :=
  sliceUnderCurry ((joinAssociator K L A).hom ≫
    sliceUnderUncurry (sliceUnderUncurry s)) (by
      rw [← Category.assoc, joinAssociator_leftPair,
        ← sliceUnderUncurry_precomp, sliceUnderUncurry_fixed])
/-- 順方向の族は join の結合同型による二重の展開を表す。 -/
lemma iteratedSliceUnderForwardFamily_uncurry (s : A ⟶ sliceUnder q) :
    sliceUnderUncurry (iteratedSliceUnderForwardFamily q s) =
      (joinAssociator K L A).hom ≫ sliceUnderUncurry (sliceUnderUncurry s) :=
  sliceUnderUncurry_curry _ _
/-- 逆方向の二重 curry の内側の族。 -/
def iteratedSliceUnderInnerFamily (s : A ⟶ sliceUnder (sliceUnderUncurry q)) :
    join L A ⟶ sliceUnder p :=
  sliceUnderCurry ((joinAssociator K L A).inv ≫ sliceUnderUncurry s) (by
    rw [← Category.assoc, joinAssociator_inv_first, Category.assoc,
      sliceUnderUncurry_fixed, sliceUnderUncurry_fixed])
/-- 内側の族を展開すると join の結合同型の逆になる。 -/
lemma iteratedSliceUnderInnerFamily_uncurry (s : A ⟶ sliceUnder (sliceUnderUncurry q)) :
    sliceUnderUncurry (iteratedSliceUnderInnerFamily q s) =
      (joinAssociator K L A).inv ≫ sliceUnderUncurry s :=
  sliceUnderUncurry_curry _ _
/-- 内側の族の左因子への制限は元の図式を保つ。 -/
lemma iteratedSliceUnderInnerFamily_fixed (s : A ⟶ sliceUnder (sliceUnderUncurry q)) :
    joinInl L A ≫ iteratedSliceUnderInnerFamily q s = q := by
  apply sliceUnderUncurry_injective p
  rw [sliceUnderUncurry_precomp, iteratedSliceUnderInnerFamily_uncurry,
    ← Category.assoc, joinAssociator_inv_leftPair, sliceUnderUncurry_fixed]
/-- 元の展開した図式の族から反復 coslice の族を回収する。 -/
def iteratedSliceUnderBackwardFamily (s : A ⟶ sliceUnder (sliceUnderUncurry q)) :
    A ⟶ sliceUnder q :=
  sliceUnderCurry (iteratedSliceUnderInnerFamily q s) (iteratedSliceUnderInnerFamily_fixed q s)
/-- 逆方向の一度の展開は内側の族。 -/
lemma iteratedSliceUnderBackwardFamily_uncurry (s : A ⟶ sliceUnder (sliceUnderUncurry q)) :
    sliceUnderUncurry (iteratedSliceUnderBackwardFamily q s) = iteratedSliceUnderInnerFamily q s :=
  sliceUnderUncurry_curry _ _
/-- 順方向の後の逆方向は元の族を厳密に回収する。 -/
lemma iteratedSliceUnderFamily_backward_forward (s : A ⟶ sliceUnder q) :
    iteratedSliceUnderBackwardFamily q (iteratedSliceUnderForwardFamily q s) = s := by
  apply sliceUnderUncurry_injective q
  rw [iteratedSliceUnderBackwardFamily_uncurry]
  apply sliceUnderUncurry_injective p
  rw [iteratedSliceUnderInnerFamily_uncurry, iteratedSliceUnderForwardFamily_uncurry,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
/-- 逆方向の後の順方向は元の族を厳密に回収する。 -/
lemma iteratedSliceUnderFamily_forward_backward (s : A ⟶ sliceUnder (sliceUnderUncurry q)) :
    iteratedSliceUnderForwardFamily q (iteratedSliceUnderBackwardFamily q s) = s := by
  apply sliceUnderUncurry_injective (sliceUnderUncurry q)
  rw [iteratedSliceUnderForwardFamily_uncurry, iteratedSliceUnderBackwardFamily_uncurry,
    iteratedSliceUnderInnerFamily_uncurry, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
/-- 順方向は任意のパラメータの前合成と可換。 -/
lemma iteratedSliceUnderForwardFamily_naturality (f : A' ⟶ A) (s : A ⟶ sliceUnder q) :
    iteratedSliceUnderForwardFamily q (f ≫ s) = f ≫ iteratedSliceUnderForwardFamily q s := by
  apply sliceUnderUncurry_injective (sliceUnderUncurry q)
  rw [iteratedSliceUnderForwardFamily_uncurry, sliceUnderUncurry_precomp,
    sliceUnderUncurry_precomp, sliceUnderUncurry_precomp, iteratedSliceUnderForwardFamily_uncurry]
  have h := joinAssociator_naturality (𝟙 K) (𝟙 L) f
  rw [joinMap_id] at h
  simpa only [Category.assoc] using
    congrArg (fun r ↦ r ≫ sliceUnderUncurry (sliceUnderUncurry s)) h.symm
/-- 逆方向は任意のパラメータの前合成と可換。 -/
lemma iteratedSliceUnderBackwardFamily_naturality (f : A' ⟶ A)
    (s : A ⟶ sliceUnder (sliceUnderUncurry q)) :
    iteratedSliceUnderBackwardFamily q (f ≫ s) = f ≫ iteratedSliceUnderBackwardFamily q s := by
  have hinj : Function.Injective (iteratedSliceUnderForwardFamily q (A := A')) := by
    intro a b hab
    have h := congrArg (iteratedSliceUnderBackwardFamily q) hab
    simpa only [iteratedSliceUnderFamily_backward_forward] using h
  apply hinj
  rw [iteratedSliceUnderFamily_forward_backward, iteratedSliceUnderForwardFamily_naturality,
    iteratedSliceUnderFamily_forward_backward]

end SerrePositivity.InfinityCategories.HomotopyLimits
