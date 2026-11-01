module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionMixedReassociation
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterComposition

/-!
# 中断した任意モデル源への一般化：ResolutionMixedReassociationEquality

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Reassociation is equality transport of the same entire indexing functor。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0324][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0324
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reassociation is equality transport of the same entire indexing functor
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open ResolutionMixedDiagram ResolutionMixedReassociation

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociationEquality
variable (C : Type u) [Category.{v} C] [ModelCategory C]

lemma finalLeft_eq : finalLeft C = cornerD C :=
  Functor.ext_of_iso (toFinal C) (assocEq C) (fun _ => rfl)

lemma toFinal_eq : toFinal C = eqToIso (finalLeft_eq C) := by
  apply Iso.ext
  apply NatTrans.ext
  funext p
  exact (eqToHom_app (finalLeft_eq C) p).symm

end SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociationEquality
