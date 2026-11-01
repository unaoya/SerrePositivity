module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryTensorGluing

/-!
# 二つの単射のpushout-productから以前の族と指定部分と基底を同時に保つ持ち上げを構成する

## 概要
二つの単射のpushout-productから以前の族と指定部分と基底を同時に保つ持ち上げを構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。

## 規約と注意
二つの単射とすべての単射に対する右持ち上げ性を持つ射を指定し、重なり上での族の一致を仮定する。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0544][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0544
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative lifting with arbitrary parameter shapes over a fixed base

Both the earlier parameter family and the entire prescribed subobject
family are retained. In particular, simplex boundaries of every dimension
may be filled while all degenerate inputs remain fixed. No model structure
or Kan condition on the source and base is required.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.RelativeProductLifting
variable {E B A X U V : SSet.{v}} (p : E ⟶ B)
  (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)
  (i : A ⟶ X) [Mono i] (j : U ⟶ V) [Mono j]
  (earlier : X ⊗ U ⟶ E) (prescribed : A ⊗ V ⟶ E) (base : X ⊗ V ⟶ B)
  (hc : i ▷ U ≫ earlier = A ◁ j ≫ prescribed)
  (he : earlier ≫ p = X ◁ j ≫ base) (ha : prescribed ≫ p = i ▷ V ≫ base)

include hp hc he ha in
/-- 二つの単射のpushout-productから以前の族と指定部分と基底を同時に保つ持ち上げを構成する。

二つの単射とすべての単射に対する右持ち上げ性を持つ射を指定し、重なり上での族の一致を仮定する。
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。
-/
lemma exists_lift : ∃ f : X ⊗ V ⟶ E,
    X ◁ j ≫ f = earlier ∧ i ▷ V ≫ f = prescribed ∧ f ≫ p = base := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i j
  have : Mono (Arrow.mk i).hom := inferInstanceAs (Mono i)
  have : Mono (Arrow.mk j).hom := inferInstanceAs (Mono j)
  have : Mono pp.ι :=
    CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.instMonoHomObjArrowFunctorPushoutProduct
      (X := Arrow.mk i) (Y := Arrow.mk j)
  have : HasLiftingProperty pp.ι p := hp _ inferInstance
  let b := pp.isPushout.desc earlier prescribed hc
  have hw : b ≫ p = pp.ι ≫ base := by
    apply pp.isPushout.hom_ext
    · dsimp only [b]
      rw [← Category.assoc, pp.isPushout.inl_desc, he, ← Category.assoc, pp.inl_ι]
      rfl
    · dsimp only [b]
      rw [← Category.assoc, pp.isPushout.inr_desc, ha, ← Category.assoc, pp.inr_ι]
      rfl
  let sq : CommSq b pp.ι p base := ⟨hw⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [show X ◁ j = pp.inl ≫ pp.ι from pp.inl_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  · rw [show i ▷ V = pp.inr ≫ pp.ι from pp.inr_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _

/-- 以前の族と指定部分と基底を保持する一つの実際の持ち上げを選ぶ。

二つの単射とすべての単射に対する右持ち上げ性を持つ射を指定し、重なり上での族の一致を仮定する。
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。
-/
def lift : X ⊗ V ⟶ E := (exists_lift p hp i j earlier prescribed base hc he ha).choose

lemma lift_earlier : X ◁ j ≫ lift p hp i j earlier prescribed base hc he ha = earlier :=
  (exists_lift p hp i j earlier prescribed base hc he ha).choose_spec.1

lemma lift_prescribed : i ▷ V ≫ lift p hp i j earlier prescribed base hc he ha = prescribed :=
  (exists_lift p hp i j earlier prescribed base hc he ha).choose_spec.2.1

lemma lift_base : lift p hp i j earlier prescribed base hc he ha ≫ p = base :=
  (exists_lift p hp i j earlier prescribed base hc he ha).choose_spec.2.2

end SerrePositivity.SimplicialModel.RelativeProductLifting
