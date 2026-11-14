-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Descent.InterfaceLimitCone（仮。E3 の CAlg 版界面の欄 limitCone・limit_isLimit）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §2.3、単位 A5-1。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface

-- 本ファイルは drafts/A4/InterfaceFields.lean、drafts/A5/PerfectSiteComparison.lean、drafts/Sheaves/CAlgValued.lean を import する。

/-!
# E3 の界面の欄 `limitCone`・`limit_isLimit` の構成（BS 著者版 Prop 8.5 の系）

## 概要
`TheoryPerfectoidizationInterface` の欄 `limitCone S : TheoryBSLimitConeData R p perfd unit h0 S` と `limit_isLimit S` を、Prop 8.5 の系 1
（Type u 版 `perfectoidization_isLimit_u`）から作る。錐の頂点は (S^∧)_perfd、脚は比較写像の脚 Δ_perf → B_T の mod d（= T）。

## 方針
S^∧ への帰着は既存の `PerfUnder_u p (completionRing p S) ≌ PerfUnder_u p S`（Interface.lean:347）。D(R) 版の `underlying` の各欄
（`sourceCone`・`overSource`・`projectionEdge`・`projection`・`projection_unit`・`projection_naturality`・`projection_compat`）は
CAlg の錐の U 像と H⁰ で埋める。極限性は D(R) で示して U が反映すること（G-A5-16）で CAlg_R へ。

## 規約
欄の型は EInfinity/Perfectoidization/Interface.lean の `TheoryBSLimitConeData` の現行の型。2b の改名表が来たら追従。

## 使われ方
`TheoryPerfectoidizationInterface` の構成（A9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-- 概要：Perfd_{S/}（Type u）上の図式 T ↦ T（CAlg_R）の、頂点 (S^∧)_perfd の錐。
方針：`perfectionComparisonLeg`（PerfectSite） の mod d を `perfectSiteEquivPerfectoidUnder` で Type u の添字へ（κ を超える T へは弱始対象を経由して延ばす：
S3 の錐の構成）。`PerfUnder_u p (S^∧) ≌ PerfUnder_u p S` で S^∧ に帰着。
規約：`JoinCone (targetCAlgDiagram R p S)`、頂点は `(e3Perfd p R).app _ (nerveVertex S)`。
使われ方：`e3LimitCone`。 -/
def perfectoidizationCone (S : A_R R) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (theoryTargetDiagram (E := E) R p S) := sorry

/-- 概要：頂点は `e3Perfd` の値そのもの。
方針：定義。
規約：`TheoryBSLimitConeData.vertex_eq`。
使われ方：`e3LimitCone`。 -/
theorem perfectoidizationCone_vertex (S : A_R R) :
    (perfectoidizationCone (E := E) p R S).vertex = (e3Perfd (E := E) p R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S) := by sorry

/-- 概要：D(R) 版の錐のデータ（`BSLimitConeData`）：通常の錐 `sourceCone`（S → T）、単位での因数分解 `overSource`、脚の辺 `projectionEdge`、
H⁰ の環準同型 `projection` と三つの整合。
方針：CAlg の錐の U 像、`e3Unit` の成分、H⁰ の関手性。`projection T` は CAlg の射 (S^∧)_perfd → T の H⁰（T は離散なので H⁰(T) = T）。
規約：`BSLimitConeData R p (e3Perfd ≫ U) (underlyingUnit R e3Unit) e3H0RingData S`。
使われ方：`e3LimitCone.underlying`。 -/
def perfectoidizationConeUnderlying (S : A_R R) :
    BSLimitConeData R p (e3Perfd (E := E) p R ≫ E.forget R) (theoryUnderlyingUnit (E := E) R (e3Unit (E := E) p R)) (e3H0RingData (E := E) p R) S := sorry

/-- 概要：E3 の `limitCone`：CAlg_R の錐、頂点の一致、D(R) 版、`overSource`・`overSource_unit`、U との比較 `comparison` と境界・頂点の整合。
方針：上の二つと `forget_isLimitCone`（S4 の CAlg 版）。
規約：`TheoryBSLimitConeData`。
使われ方：`TheoryPerfectoidizationInterface.limitCone`。 -/
def e3LimitCone (S : A_R R) :
    TheoryBSLimitConeData (E := E) R p (e3Perfd (E := E) p R) (e3Unit (E := E) p R) (e3H0RingData (E := E) p R) S := sorry

/-- 概要：E3 の `limit_isLimit`：`e3LimitCone S` の錐は極限の錐。
方針：`perfectoidization_isLimit_u`（Prop 8.5 の系 1、Type u 版）を S^∧ に適用し、`PerfUnder_u p (S^∧) ≌ PerfUnder_u p S` で移す。
CAlg_R の極限性は D(R) で示して `forget_reflects_isLimitCone`（G-A5-16）。
規約：`IsLimitCone`。
使われ方：`TheoryPerfectoidizationInterface.limit_isLimit`。 -/
theorem e3LimitCone_isLimit (S : A_R R) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (e3LimitCone (E := E) p R hR S).cone := by
  sorry -- Prop 8.5（A5-2〜A5-4）を待つ

end SerrePositivity.BhattScholze.Perfectoidization.Derived
