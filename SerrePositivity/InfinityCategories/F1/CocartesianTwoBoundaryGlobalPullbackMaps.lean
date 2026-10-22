module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoBoundaryCoherentHomProjections
public import SerrePositivity.InfinityCategories.F1.CocartesianNativeGlobalDiagramRestriction

/-!
概要：元の大域全 Hom 上で、coherent な境界比較と元の分類作用を同じ pullback へ写す。
方針：両側とも同じ分類先の境界表示同型を使う。
規約：元の全 Hom と元の分類主写像を保持する。
使われ方：両成分の指定同型の貼合せと、実際の境界への復帰。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (j : Fin 2) (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 元の全 native Hom の制限と同じ coherent 境界比較を、分類先の pullback へ写す。 -/
def cocartesianTwoBoundaryCorrectedGlobalPullbackMap :=
  (cocartesianNativeGlobalDiagramRestriction p.val.hom q.val.hom (HornBoundaryOver.apex 1 σ) ≫
    cocartesianTwoBoundaryCoherentHomComparison j p q) ≫
      (cocartesianTwoBoundaryTargetPresentationIso p q).hom

/-- 元の分類主写像の全 Hom 作用を同じ境界へ制限し、同じ pullback へ写す。 -/
def cocartesianTwoBoundaryOriginalGlobalPullbackMap :=
  (cocartesianStraighteningHomInterval p q ≫
    intervalDiagramGlobalDiagramRestriction P Q (HornBoundaryOver.apex 1 σ)) ≫
      (cocartesianTwoBoundaryTargetPresentationIso p q).hom

end SerrePositivity.InfinityCategories
