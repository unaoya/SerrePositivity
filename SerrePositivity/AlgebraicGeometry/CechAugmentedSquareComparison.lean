module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareMap
public import SerrePositivity.AlgebraicGeometry.CechZeroTermExtensionConeAcyclic
public import SerrePositivity.AlgebraicGeometry.CechDoubleConeAcyclic
public import SerrePositivity.AlgebraicGeometry.AugmentedCechConeComparison

/-!
概要：可換四角の実際の射に沿って、増大項を含む全複体の完全性を比較する。
方針：零次項拡張、二重 cone の交換、増大項の比較を自然な射で接続する。
規約：基底・中心・制限・増大写像の可換性を保持する。
使われ方：共通細分の比較写像から、射影四角形の完全性を移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
namespace CechAugmentedSquare.Map
variable {s t : CechAugmentedSquare.{u} R}

set_option backward.isDefEq.respectTransparency false in
/-- 二辺の cone が完全で、基底と中心の項が同型な四角形の射は、全複体の完全性を比較する。 -/
theorem totalComplex_acyclic_iff_of_cones (m : CechAugmentedSquare.Map s t)
    (hC : (cechRefinementCone s.C t.C m.left).Acyclic)
    (hE : (cechRefinementCone s.E t.E m.right).Acyclic)
    (hbase : Function.Bijective m.base) (hcenter : Function.Bijective m.center) :
    s.totalComplex.Acyclic ↔ t.totalComplex.Acyclic := by
  let α := cechZeroTermExtensionMap m.left m.center
  have hα : (cechRefinementCone s.source t.source α).Acyclic :=
    cechZeroTermExtensionMap_cone_acyclic m.left m.center hC hcenter
  have hsq : s.difference ≫ m.right = α ≫ t.difference :=
    cechZeroTermDifference_naturality s.restriction t.restriction s.center t.center
      s.center_cycle t.center_cycle m.left m.right m.center m.restriction m.center_naturality
  have hk := cechRefinementConeMap_cone_acyclic
    s.difference t.difference α m.right hsq hα hE
  exact augmentedCechCone_acyclic_iff_of_comparison
    s.source s.E t.source t.E s.difference t.difference
    s.base t.base s.augmentation t.augmentation s.augmentation_cycle t.augmentation_cycle
    (cechRefinementConeMap α m.right hsq) m.base hbase m.augmentation hk

end CechAugmentedSquare.Map
end SerrePositivity.AlgebraicGeometry
