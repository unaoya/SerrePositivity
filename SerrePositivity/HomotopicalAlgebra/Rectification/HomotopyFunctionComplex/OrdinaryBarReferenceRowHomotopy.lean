module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarReferenceRows
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopyUniverse
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseLiftPadding

/-!
# 中断した任意モデル源への一般化：OrdinaryBarReferenceRowHomotopy

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The labelled reference-to-row cone gives an actual bar-valued interval。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0206][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0206
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The labelled reference-to-row cone gives an actual bar-valued interval

The row endpoint factors through the original small augmentation on
simplex nerves, followed by the same original rowNerveMap.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

def bridge : SSet.uliftFunctor.{v, max u v}.obj (nerve (OrdinaryBarTotalCone.Total R)) ⟶
    OrdinaryBarEvaluation.bar R where
  app n := ↾fun x => (OrdinaryBarNerveBridge.rawBridge R).app n x.down
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun f => f x.down) ((OrdinaryBarNerveBridge.rawBridge R).naturality θ)

abbrev fromReference := NerveHomotopyUniverse.map (OrdinaryBarReferenceRows.referenceElements R) ≫
  bridge R
abbrev fromRows := NerveHomotopyUniverse.map (OrdinaryBarReferenceRows.rowElements R) ≫ bridge R

def homotopy : SSet.Homotopy (fromReference R) (fromRows R) :=
  HomotopyClasses.postHomotopy (bridge R)
    (NerveHomotopyUniverse.homotopy (OrdinaryBarReferenceRows.comparison R))

def nerveAugmentation : SSet.uliftFunctor.{max u v, v}.obj
    (nerve (OrdinaryBarReferenceRows.raw R).Elements) ⟶ OrdinaryBarEvaluatedEndpoint.SmallNerve R :=
  SSet.uliftFunctor.{max u v, v}.map ((SimplexNerve.functor.{v}).map
    (OrdinaryBarReferenceRows.augmentation R))

lemma row_factorization : fromRows R =
    nerveAugmentation R ≫ OrdinaryBarEvaluatedEndpoint.rowNerveMap R := rfl

def referenceComposite := SSet.uliftFunctor.{max u v, v}.map
  (SimplexNerve.augmentation.app (OrdinaryBarReferenceRows.raw R)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.paddingIso.{v, u}.app (OrdinaryBarReferenceRows.raw R)).inv ≫
      OrdinaryBarReference.sectionMap R

lemma reference_factorization : fromReference R = referenceComposite R := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply OrdinaryBarFirstEndpoint.chain_ext R _ _
  · apply CategoryTheory.Functor.ext (fun _ => rfl)
  · change (((BarConstruction.TotalNerve.simplex
      (BarConstruction.commaValues OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw
        ((RightResolutionMapping.projection (C := C)).obj R))
      (x.down ⋙ OrdinaryBarReferenceRows.referenceElements R)) ⋙
        BarConstruction.commaElements OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw
          ((RightResolutionMapping.projection (C := C)).obj R) n).obj 0) = _
    rw [Functor.comp_obj, BarConstruction.TotalNerve.first_vertex]
    rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy
