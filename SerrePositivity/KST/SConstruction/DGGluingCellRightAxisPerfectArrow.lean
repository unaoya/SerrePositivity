module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphPerfectFunctor
public import SerrePositivity.KST.SConstruction.DGGluingAxesComparisons
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Size

/-!
概要：元 gluing の固定 cell source 上で右軸から恒等への実 Perf 比較を構成する。
方針：元全 Hom 比較を二つの graph 解像度へ移し、各右制限の射影性だけを明示する。
規約：同じ cell source を保持し、未供給射影性を実証済みと数えない。
使われ方：LT の実中央比較への二つの D 供給証拠の特殊化口。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (z : C) (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "P" => DGCategoryCellResolution.Source R (B)

/-- 概要：元 gluing の右射影と元右軸包含の同じ dg 合成。
方針：元実二関手を合成する。規約：元閉零対象を保持。
使われ方：元右軸 graph の入力関手。 -/
def dgGluingCellRightAxisEndofunctor : DGFunctor R (B) (B) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).comp (dgGluingRightAxis R C D M z hz)

/-- 概要：固定 cell source で必要な二つの右制限の射影性の残入力。
方針：右軸と恒等の同じ標準 graph 解像度を指定する。
規約：両証拠の存在は未証明。使われ方：D の最小追加供給の二特殊化。 -/
structure DGGluingCellRightAxisProjectiveInput where
  right : DGCellResolvedGraphProjectiveCondition R (B)
    (dgGluingCellRightAxisEndofunctor R C D M z hz)
  identity : DGCellResolvedGraphProjectiveCondition R (B) (DGFunctor.id (B))

variable (h : DGGluingCellRightAxisProjectiveInput R C D M z hz)

/-- 概要：同じ cell source 上の実右軸 graph 解像度を実 Perf 関手へ制限する。
方針：同じ追加射影性と証明済み Perf 性を使う。
規約：元始域と全 Hom を保持。使われ方：実中央比較の右軸成分。 -/
def dgGluingCellRightAxisPerfectSource : DGFunctor R (P) (PerfectDGModule R (P)) :=
  dgCellResolvedGraphPerfectFunctor R (B) (dgGluingCellRightAxisEndofunctor R C D M z hz) h.right

/-- 概要：同じ cell source 上の恒等 graph 解像度を実 Perf 関手へ制限する。
方針：同じ追加射影性と証明済み Perf 性を使う。
規約：元始域と全 Hom を保持。使われ方：実中央比較の恒等成分。 -/
def dgGluingCellRightAxisPerfectTarget : DGFunctor R (P) (PerfectDGModule R (P)) :=
  dgCellResolvedGraphPerfectFunctor R (B) (DGFunctor.id (B)) h.identity

/-- 概要：同じ固定 cell source 上の右軸から恒等への全 dg 比較。
方針：元全 Hom 比較を同じ graph 解像度と実 Perf 制限へ移す。
規約：追加射影性の二証拠だけに条件付き。使われ方：resolved 商への実比較の延長。 -/
def dgGluingCellRightAxisPerfectComparison :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R)))
      (dgGluingCellRightAxisPerfectSource R C D M z hz h)
      (dgGluingCellRightAxisPerfectTarget R C D M z hz h) :=
  dgCellResolvedGraphPerfectComparison R (B)
    (dgGluingCellRightAxisEndofunctor R C D M z hz) (DGFunctor.id (B))
    h.right h.identity (dgGluingAxisRightComparison R C D M z hz)
end SerrePositivity.KST.SConstruction
