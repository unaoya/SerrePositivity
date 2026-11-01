module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBiparameterMapLaws
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# 中断した任意モデル源への一般化：NerveArrowComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The two whole coherent endpoint systems of comparison along every arrow。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0456][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0456
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The two whole coherent endpoint systems of comparison along every arrow
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.NerveArrowComparison
open NerveBiparameterMaps
variable {D : Type uD} [Category.{vD} D] (V K F : D ⥤ SSet.{w})
  (i : V ⟶ K) (b : V ⟶ F)

abbrev source (K : D ⥤ SSet.{w}) := (Arrow.leftFunc : Arrow D ⥤ D) ⋙ K
abbrev target (K : D ⥤ SSet.{w}) := (Arrow.rightFunc : Arrow D ⥤ D) ⋙ K
abbrev transport (K : D ⥤ SSet.{w}) : source K ⟶ target K :=
  Functor.whiskerRight Arrow.leftToRight K
abbrev sourceMap {V K : D ⥤ SSet.{w}} (i : V ⟶ K) : source V ⟶ source K :=
  Functor.whiskerLeft Arrow.leftFunc i
abbrev targetMap {V K : D ⥤ SSet.{w}} (i : V ⟶ K) : target V ⟶ target K :=
  Functor.whiskerLeft Arrow.rightFunc i

lemma square : sourceMap b ≫ transport F = transport V ≫ targetMap b := by
  apply NatTrans.ext
  funext e
  exact (b.naturality e.hom).symm

abbrev boundary : source V ⟶ target F := sourceMap b ≫ transport F

variable (a : NerveBiparameter.System K F)
  (ha : a ≫ restriction V K F i = NerveNaturalBoundary.ofNatTrans V F b)

/-- Reindex the given whole system at sources, then use the actual value transport. -/
def left : NerveBiparameter.System (source K) (target F) :=
  NerveBiparameterMaps.mapTarget (source K) (source F) (target F) (transport F)
    (reindex K F Arrow.leftFunc a)

/-- Reindex the same whole system at targets, then use actual parameter transport. -/
def right : NerveBiparameter.System (source K) (target F) :=
  restrict (source K) (target K) (target F) (transport K)
    (reindex K F Arrow.rightFunc a)

include ha in
lemma source_boundary : reindex K F Arrow.leftFunc a ≫
    restriction (source V) (source K) (source F) (sourceMap i) =
      NerveNaturalBoundary.ofNatTrans (source V) (source F) (sourceMap b) := by
  rw [← reindex_restriction, ha, reindex_natural]

include ha in
lemma target_boundary : reindex K F Arrow.rightFunc a ≫
    restriction (target V) (target K) (target F) (targetMap i) =
      NerveNaturalBoundary.ofNatTrans (target V) (target F) (targetMap b) := by
  rw [← reindex_restriction, ha, reindex_natural]

include ha in
lemma left_boundary : left K F a ≫ restriction (source V) (source K) (target F)
    (sourceMap i) = NerveNaturalBoundary.ofNatTrans (source V) (target F) (boundary V F b) := by
  change (reindex K F Arrow.leftFunc a ≫ NerveBiparameterMaps.targetMap
    (source K) (source F) (target F) (transport F)) ≫ _ = _
  rw [Category.assoc, target_restriction, ← Category.assoc, source_boundary V K F i b a ha,
    mapTarget_natural]

include ha in
lemma right_boundary : right K F a ≫ restriction (source V) (source K) (target F)
    (sourceMap i) = NerveNaturalBoundary.ofNatTrans (source V) (target F) (boundary V F b) := by
  change (reindex K F Arrow.rightFunc a ≫
    restriction (source K) (target K) (target F) (transport K)) ≫ _ = _
  rw [Category.assoc, restriction_comp, square V K i, ← restriction_comp, ← Category.assoc,
    target_boundary V K F i b a ha, restrict_natural, ← square V F b]

end SerrePositivity.SimplicialModel.NerveArrowComparison
