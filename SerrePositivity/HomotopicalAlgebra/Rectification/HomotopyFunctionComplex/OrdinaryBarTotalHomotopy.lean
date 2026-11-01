module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation
public import SerrePositivity.CategoryTheory.NerveHomotopyUniverse
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 中断した任意モデル源への一般化：OrdinaryBarTotalHomotopy

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual nerve homotopy of the whole labelled total comparison。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0233][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0233
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual nerve homotopy of the whole labelled total comparison

The source is the nerve of the original bar simplex category. The target
retains comma objects, degrees, and Hom labels. This is an auxiliary
homotopy; no comparison between this nerve and the original bar is assumed.
-/

@[expose] public section
universe v u uH vH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

abbrev firstMap := NerveHomotopyUniverse.map (OrdinaryBarTotalCone.first R)
abbrev evaluatedMap := NerveHomotopyUniverse.map
  (OrdinaryBarTotalEvaluation.evaluationElements R a b ⋙
    OrdinaryBarTotalEvaluation.rowElements R)

def homotopy : SSet.Homotopy (firstMap R) (evaluatedMap R a b) :=
  NerveHomotopyUniverse.homotopy (OrdinaryBarTotalEvaluation.comparison R a b)

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma image_eq : L.map (firstMap R) = L.map (evaluatedMap R a b) :=
  AnodyneHomotopy.map_homotopy_eq L hL (homotopy R a b)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy
