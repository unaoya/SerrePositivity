module
public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinAssociatorInclusions
public import SerrePositivity.InfinityCategories.Core.JoinLifting
public import SerrePositivity.InfinityCategories.Core.RightFibration
/-!
概要：coslice 内の slice と slice 内の coslice の全パラメータの図式を交換する。
方針：二重の普遍錐を展開し、join の三因子を再結合して二度 curry する。
規約：固定された外側二因子の全図式を保持。使われ方：右 Kan 比較の三角形の共通模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
variable {K L X A : SSet.{u}} {p : K ⟶ X} (q : L ⟶ sliceUnder p)
/-- 同じ固定二因子の全図式を、反対側の slice の図式として読む。 -/
def mixedSliceTranspose : K ⟶ sliceOver (q ≫ sliceUnderProjection p) :=
  sliceOverCurry (sliceUnderUncurry q) (sliceUnderUncurry_projection q)
/-- 固定二因子の転置は、同じ元の全 join 図式を展開する。 -/
lemma mixedSliceTranspose_uncurry :
    sliceOverUncurry (mixedSliceTranspose q) = sliceUnderUncurry q :=
  sliceOverUncurry_curry _ _
/-- coslice 内の slice の族の、交換後の内側の族。 -/
def mixedSliceForwardInner (s : A ⟶ sliceOver q) :
    join K A ⟶ sliceOver (q ≫ sliceUnderProjection p) :=
  sliceOverCurry ((joinAssociator K A L).hom ≫
    sliceUnderUncurry (sliceOverUncurry s)) (by
      rw [← Category.assoc, joinAssociator_last, Category.assoc,
        sliceUnderUncurry_projection, ← Category.assoc, sliceOverUncurry_fixed])
/-- 交換後の内側の族の展開。 -/
lemma mixedSliceForwardInner_uncurry (s : A ⟶ sliceOver q) :
    sliceOverUncurry (mixedSliceForwardInner q s) =
      (joinAssociator K A L).hom ≫ sliceUnderUncurry (sliceOverUncurry s) :=
  sliceOverUncurry_curry _ _
/-- 交換後も、固定された外側二因子の全図式は厳密に一致する。 -/
lemma mixedSliceForwardInner_fixed (s : A ⟶ sliceOver q) :
    joinInl K A ≫ mixedSliceForwardInner q s = mixedSliceTranspose q := by
  apply sliceOverUncurry_injective (q ≫ sliceUnderProjection p)
  rw [sliceOverUncurry_precomp, mixedSliceForwardInner_uncurry, ← Category.assoc,
    joinAssociator_outerPair, ← sliceUnderUncurry_precomp,
    sliceOverUncurry_fixed, mixedSliceTranspose_uncurry]
/-- coslice 内の slice の全族を、同じ固定図式の slice 内の coslice へ写す。 -/
def mixedSliceForwardFamily (s : A ⟶ sliceOver q) :
    A ⟶ sliceUnder (mixedSliceTranspose q) :=
  sliceUnderCurry (mixedSliceForwardInner q s) (mixedSliceForwardInner_fixed q s)
/-- 順方向を一度展開すると、指定した内側の族へ厳密に戻る。 -/
lemma mixedSliceForwardFamily_uncurry (s : A ⟶ sliceOver q) :
    sliceUnderUncurry (mixedSliceForwardFamily q s) = mixedSliceForwardInner q s :=
  sliceUnderUncurry_curry _ _
/-- slice 内の coslice の族の、逆交換後の内側の族。 -/
def mixedSliceBackwardInner (s : A ⟶ sliceUnder (mixedSliceTranspose q)) :
    join A L ⟶ sliceUnder p :=
  sliceUnderCurry ((joinAssociator K A L).inv ≫
    sliceOverUncurry (sliceUnderUncurry s)) (by
      rw [← Category.assoc, joinAssociator_inv_first, Category.assoc,
        sliceOverUncurry_projection, ← Category.assoc, sliceUnderUncurry_fixed,
        ← sliceOverUncurry_projection, mixedSliceTranspose_uncurry, sliceUnderUncurry_fixed])
/-- 逆交換後の内側の族の展開。 -/
lemma mixedSliceBackwardInner_uncurry (s : A ⟶ sliceUnder (mixedSliceTranspose q)) :
    sliceUnderUncurry (mixedSliceBackwardInner q s) =
      (joinAssociator K A L).inv ≫ sliceOverUncurry (sliceUnderUncurry s) :=
  sliceUnderUncurry_curry _ _
/-- 逆交換も、元の固定図式 q を全単体で保つ。 -/
lemma mixedSliceBackwardInner_fixed (s : A ⟶ sliceUnder (mixedSliceTranspose q)) :
    joinInr A L ≫ mixedSliceBackwardInner q s = q := by
  apply sliceUnderUncurry_injective p
  rw [sliceUnderUncurry_precomp, mixedSliceBackwardInner_uncurry, ← Category.assoc,
    joinAssociator_inv_outerPair, ← sliceOverUncurry_precomp,
    sliceUnderUncurry_fixed, mixedSliceTranspose_uncurry]
/-- slice 内の coslice の全族を、元の coslice 内の slice へ戻す。 -/
def mixedSliceBackwardFamily (s : A ⟶ sliceUnder (mixedSliceTranspose q)) :
    A ⟶ sliceOver q :=
  sliceOverCurry (mixedSliceBackwardInner q s) (mixedSliceBackwardInner_fixed q s)
/-- 逆方向を一度展開すると、指定した内側の族へ厳密に戻る。 -/
lemma mixedSliceBackwardFamily_uncurry (s : A ⟶ sliceUnder (mixedSliceTranspose q)) :
    sliceOverUncurry (mixedSliceBackwardFamily q s) = mixedSliceBackwardInner q s :=
  sliceOverUncurry_curry _ _
/-- 全族の交換の逆・順の合成は、元の全族そのもの。 -/
lemma mixedSliceFamily_backward_forward (s : A ⟶ sliceOver q) :
    mixedSliceBackwardFamily q (mixedSliceForwardFamily q s) = s := by
  apply sliceOverUncurry_injective q
  apply sliceUnderUncurry_injective p
  rw [mixedSliceBackwardFamily_uncurry, mixedSliceBackwardInner_uncurry,
    mixedSliceForwardFamily_uncurry, mixedSliceForwardInner_uncurry,
    Iso.inv_hom_id_assoc]
/-- 全族の交換の順・逆の合成も、元の全族そのもの。 -/
lemma mixedSliceFamily_forward_backward (s : A ⟶ sliceUnder (mixedSliceTranspose q)) :
    mixedSliceForwardFamily q (mixedSliceBackwardFamily q s) = s := by
  apply sliceUnderUncurry_injective (mixedSliceTranspose q)
  apply sliceOverUncurry_injective (q ≫ sliceUnderProjection p)
  rw [mixedSliceForwardFamily_uncurry, mixedSliceForwardInner_uncurry,
    mixedSliceBackwardFamily_uncurry, mixedSliceBackwardInner_uncurry,
    Iso.hom_inv_id_assoc]
end SerrePositivity.InfinityCategories
