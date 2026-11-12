module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalCofibrations
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.DiagonalRelativeMatching

/-!
# 各行が弱同値である二重単体写像の対角も弱同値となる

## 概要
各行が弱同値である二重単体写像の対角も弱同値となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
対角の右随伴と境界内部Homの比較を使い、相対matching射を計算する。
必要な持ち上げ条件またはBrownの補題を、この実際の比較へ適用する。

## 規約と注意
単射がcofibration、hornの右クラスがfibrationである指定した値モデルを仮定する。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0387][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0387
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The diagonal Quillen adjunction and bisimplicial weak equivalences

The right adjoint's relative matching maps are boundary pullback-Homs.
The proved SM7 condition therefore supplies the right Quillen condition.
All bisimplicial sets are Reedy cofibrant, so Brown's lemma proves that
rowwise weak equivalences induce actual diagonal weak equivalences.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.Quillen

namespace SerrePositivity.BisimplicialModel
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma relativeMatching_fibration {Z Y : SSet.{v}} (p : Z ⟶ Y) [Fibration p] (n : ℕ) :
    fibrations SSet.{v} (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (internalHomRight.map p)) := by
  have : HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SSet.{v})) :=
    SimplicialModel.simplicial_SM7 hcof hfib
  have hi : Cofibration (SSet.boundary.{v} n).ι := by
    rw [cofibration_iff, hcof]
    infer_instance
  have h := HasQuillenPullbackHom.fibration (SSet.boundary.{v} n).ι p
    (boundaryPullbackHom p n) hi inferInstance
  exact ((fibrations SSet.{v}).arrow_iso_iff (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.relativeMatchingArrowIso p n)).mpr
    (mem_fibrations (boundaryPullbackHom p n).π)

include hcof hfib in
lemma relativeMatching_weakEquivalence {Z Y : SSet.{v}} (p : Z ⟶ Y)
    [Fibration p] [WeakEquivalence p] (n : ℕ) :
    weakEquivalences SSet.{v} (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (internalHomRight.map p)) := by
  have : HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SSet.{v})) :=
    SimplicialModel.simplicial_SM7 hcof hfib
  have hi : Cofibration (SSet.boundary.{v} n).ι := by
    rw [cofibration_iff, hcof]
    infer_instance
  have h := HasQuillenPullbackHom.weakEquivalence (SSet.boundary.{v} n).ι p
    (boundaryPullbackHom p n) hi inferInstance (Or.inr inferInstance)
  exact ((weakEquivalences SSet.{v}).arrow_iso_iff (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.relativeMatchingArrowIso p n)).mpr
    (mem_weakEquivalences (boundaryPullbackHom p n).π)

include hcof hfib in
lemma internalHomRight_isRightQuillen :
    let := simplexOpModelCategory SSet.{v}; IsRightQuillen internalHomRight.{v} := by
  let := simplexOpModelCategory SSet.{v}
  constructor
  · intro Z Y p hp j
    have : Fibration p := ⟨hp⟩
    induction j using Opposite.rec with | _ j =>
      induction j using SimplexCategory.rec with | _ n =>
        exact relativeMatching_fibration hcof hfib p n
  · intro Z Y p hp
    have : Fibration p := ⟨hp.1⟩
    have : WeakEquivalence p := ⟨hp.2⟩
    apply (reedyRight_trivialFibrations_iff simplexOp (internalHomRight.map p)).mp
    intro j
    induction j using Opposite.rec with | _ j =>
      induction j using SimplexCategory.rec with | _ n =>
        exact ⟨relativeMatching_fibration hcof hfib p n,
          relativeMatching_weakEquivalence hcof hfib p n⟩

include hcof hfib in
/-- 指定した単体モデルとReedyモデルのもとで対角関手が左Quillen関手となる。

単射がcofibration、hornの右クラスがfibrationである指定した値モデルを仮定する。
対角の右随伴と境界内部Homの比較を使い、相対matching射を計算する。
必要な持ち上げ条件またはBrownの補題を、この実際の比較へ適用する。
-/
lemma diagonal_isLeftQuillen :
    let := simplexOpModelCategory SSet.{v}; IsLeftQuillen diagonal.{v} := by
  let := simplexOpModelCategory SSet.{v}
  have : IsRightQuillen internalHomRight.{v} := internalHomRight_isRightQuillen hcof hfib
  exact (isLeftQuillen_iff_isRightQuillen diagonalInternalHomAdjunction).mpr inferInstance

include hcof hfib in
/- 旧宣言の技術注記：
Every rowwise weak equivalence of bisimplicial sets is a diagonal weak equivalence.
-/
/-- 各行が弱同値である二重単体写像の対角も弱同値となる。

単射がcofibration、hornの右クラスがfibrationである指定した値モデルを仮定する。
対角の右随伴と境界内部Homの比較を使い、相対matching射を計算する。
必要な持ち上げ条件またはBrownの補題を、この実際の比較へ適用する。
-/
lemma diagonal_map_weakEquivalence {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : B ⟶ B')
    (hf : ∀ n, weakEquivalences SSet.{v} (f.app n)) :
    weakEquivalences SSet.{v} (diagonal.map f) :=
  diagonal_map_weakEquivalence_of_isLeftQuillen hcof (diagonal_isLeftQuillen hcof hfib) f hf

end SerrePositivity.BisimplicialModel
