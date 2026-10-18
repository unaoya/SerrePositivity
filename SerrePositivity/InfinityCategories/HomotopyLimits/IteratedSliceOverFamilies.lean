module

public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinAssociatorInclusions
public import SerrePositivity.InfinityCategories.Core.JoinLifting

/-!
概要：反復 slice と再結合した図式の slice の任意の族を比較する。
方針：slice の普遍性を二度使い、join の結合同型で括弧付けを移す。
規約：全ての単体集合・図式・パラメータを扱い、充填性は仮定しない。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6 の native な錐の比較 span の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {K L X A A' : SSet.{u}} {p : K ⟶ X} (q : L ⟶ sliceOver p)

/-- 概要：反復 slice の族を、元の図式を展開した slice の族へ移す。
方針：二度の uncurry の後に join の結合同型の逆を前合成して curry する。
規約：固定図式は sliceOverUncurry q。
使われ方：Kerodon 7.4.1.6 の錐への射から錐の図式上の切断への比較。 -/
def iteratedSliceOverForwardFamily (s : A ⟶ sliceOver q) :
    A ⟶ sliceOver (sliceOverUncurry q) :=
  sliceOverCurry ((joinAssociator A L K).inv ≫
    sliceOverUncurry (sliceOverUncurry s)) (by
      rw [← Category.assoc, joinAssociator_inv_rightPair,
        ← sliceOverUncurry_precomp, sliceOverUncurry_fixed])

/-- 概要：反復 slice からの族の比較を展開すると再結合した二重の uncurry になる。
方針：slice の curry と uncurry の往復則を使う。
規約：実際の順方向の比較射の評価式。
使われ方：HTT 4.2.4.1 の共通模型の標準射の追跡。 -/
lemma iteratedSliceOverForwardFamily_uncurry (s : A ⟶ sliceOver q) :
    sliceOverUncurry (iteratedSliceOverForwardFamily q s) =
      (joinAssociator A L K).inv ≫ sliceOverUncurry (sliceOverUncurry s) :=
  sliceOverUncurry_curry _ _

/-- 概要：再結合した図式の slice の族から、二重の curry の内側の族を得る。
方針：一度展開し、join の結合同型を前合成して元の図式上で curry する。
規約：始域は A⋆L、終域は sliceOver p。
使われ方：Kerodon 7.4.1.6 の反復 slice の比較の逆方向の構成。 -/
def iteratedSliceOverInnerFamily (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    join A L ⟶ sliceOver p :=
  sliceOverCurry ((joinAssociator A L K).hom ≫ sliceOverUncurry s) (by
    rw [← Category.assoc, joinAssociator_last, Category.assoc,
      sliceOverUncurry_fixed, sliceOverUncurry_fixed])

/-- 概要：内側の族の展開は元の族の展開を再結合したもの。
方針：curry と uncurry の往復則を使う。
規約：順方向の join の結合同型を使う。
使われ方：HTT 4.2.4.1 の二つの比較の往復の検証。 -/
lemma iteratedSliceOverInnerFamily_uncurry (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    sliceOverUncurry (iteratedSliceOverInnerFamily q s) =
      (joinAssociator A L K).hom ≫ sliceOverUncurry s :=
  sliceOverUncurry_curry _ _

/-- 概要：内側の族は後ろの L の面で指定された反復 slice の図式 q に一致する。
方針：uncurry で検出し、固定面の包含と結合同型の可換式を使う。
規約：固定条件は同値でなく厳密な射の等式。
使われ方：Kerodon 7.4.1.6 の逆方向の二度目の curry の入力。 -/
lemma iteratedSliceOverInnerFamily_fixed (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    joinInr A L ≫ iteratedSliceOverInnerFamily q s = q := by
  apply sliceOverUncurry_injective p
  rw [sliceOverUncurry_precomp, iteratedSliceOverInnerFamily_uncurry,
    ← Category.assoc, joinAssociator_rightPair, sliceOverUncurry_fixed]

/-- 概要：展開した図式の slice の族を反復 slice の族へ戻す。
方針：再結合した図式を二度 curry し、検証済みの固定面の条件を使う。
規約：逆向きも充填や同値の選択を含まない。
使われ方：HTT 4.2.4.1 の反復 slice の厳密な同型の逆射。 -/
def iteratedSliceOverBackwardFamily (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    A ⟶ sliceOver q :=
  sliceOverCurry (iteratedSliceOverInnerFamily q s) (iteratedSliceOverInnerFamily_fixed q s)

/-- 概要：逆方向の族を一度展開すると内側の族に戻る。
方針：curry と uncurry の往復則を使う。
規約：固定条件の証明の選択には依存しない。
使われ方：Kerodon 7.4.1.6 の比較の逆関係の検証。 -/
lemma iteratedSliceOverBackwardFamily_uncurry (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    sliceOverUncurry (iteratedSliceOverBackwardFamily q s) = iteratedSliceOverInnerFamily q s :=
  sliceOverUncurry_curry _ _

/-- 概要：反復 slice の族を移して戻すと元の族に一致する。
方針：二度の uncurry で検出し、結合同型と逆の合成を消去する。
規約：全パラメータ A の族について厳密な往復則。
使われ方：HTT 4.2.4.1 の native な共通模型の同定。 -/
lemma iteratedSliceOverFamily_backward_forward (s : A ⟶ sliceOver q) :
    iteratedSliceOverBackwardFamily q (iteratedSliceOverForwardFamily q s) = s := by
  apply sliceOverUncurry_injective q
  rw [iteratedSliceOverBackwardFamily_uncurry]
  apply sliceOverUncurry_injective p
  rw [iteratedSliceOverInnerFamily_uncurry, iteratedSliceOverForwardFamily_uncurry,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 概要：展開した図式の slice の族を戻して移すと元の族に一致する。
方針：uncurry で検出し、結合同型の逆と順方向の合成を消去する。
規約：全パラメータ A の族について厳密な往復則。
使われ方：Kerodon 7.4.1.6 の図式上の錐の模型の同定。 -/
lemma iteratedSliceOverFamily_forward_backward (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    iteratedSliceOverForwardFamily q (iteratedSliceOverBackwardFamily q s) = s := by
  apply sliceOverUncurry_injective (sliceOverUncurry q)
  rw [iteratedSliceOverForwardFamily_uncurry, iteratedSliceOverBackwardFamily_uncurry,
    iteratedSliceOverInnerFamily_uncurry, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 概要：反復 slice の族の順方向の比較はパラメータの前合成と可換。
方針：二度の uncurry の自然性と join の結合同型の逆の自然性を使う。
規約：パラメータ間の射は任意。
使われ方：HTT 4.2.4.1 の族の全単射から実際の単体集合の同型を作る段階。 -/
lemma iteratedSliceOverForwardFamily_naturality (f : A' ⟶ A) (s : A ⟶ sliceOver q) :
    iteratedSliceOverForwardFamily q (f ≫ s) = f ≫ iteratedSliceOverForwardFamily q s := by
  apply sliceOverUncurry_injective (sliceOverUncurry q)
  rw [iteratedSliceOverForwardFamily_uncurry, sliceOverUncurry_precomp,
    sliceOverUncurry_precomp, sliceOverUncurry_precomp, iteratedSliceOverForwardFamily_uncurry]
  have h := joinAssociator_inv_naturality f (𝟙 L) (𝟙 K)
  rw [joinMap_id] at h
  simpa only [Category.assoc] using
    congrArg (fun r ↦ r ≫ sliceOverUncurry (sliceOverUncurry s)) h.symm

/-- 概要：反復 slice の族の逆方向の比較もパラメータの前合成と可換。
方針：順方向の単射性で検出し、自然性と二つの往復則を使う。
規約：選択した逆ではなく構成済みの逆方向の族の自然性。
使われ方：Kerodon 7.4.1.6 の実際の同型の両逆則。 -/
lemma iteratedSliceOverBackwardFamily_naturality (f : A' ⟶ A)
    (s : A ⟶ sliceOver (sliceOverUncurry q)) :
    iteratedSliceOverBackwardFamily q (f ≫ s) = f ≫ iteratedSliceOverBackwardFamily q s := by
  have hinj : Function.Injective (iteratedSliceOverForwardFamily q (A := A')) := by
    intro a b hab
    have h := congrArg (iteratedSliceOverBackwardFamily q) hab
    simpa only [iteratedSliceOverFamily_backward_forward] using h
  apply hinj
  rw [iteratedSliceOverFamily_forward_backward, iteratedSliceOverForwardFamily_naturality,
    iteratedSliceOverFamily_forward_backward]

end SerrePositivity.InfinityCategories.HomotopyLimits
