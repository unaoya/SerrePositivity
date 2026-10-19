module
public import SerrePositivity.KST.SConstruction.ObjectRawBoundaryEdges
public import SerrePositivity.KST.SConstruction.ObjectCoreWeakEquivalence

/-! # 元の object S と元の全零境界商の局所化同値
概要：元の object S から元の境界商への既存の比較射が anodyne 局所化で可逆となる。
方針：object/core 比較・座標同型・元の全零境界商の三つの既存比較を合成する。
規約：object S₀ の離散頂点の商へ置換しない。使われ方：三角圏 K₀ 値の関手の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.SimplicialModel

/-- 元の object S から元の境界商への比較は anodyne 局所化で可逆。 -/
lemma objectRawBoundaryComparison_localized_isIso (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (objectRawBoundaryComparison X)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := objectToCoreSRealization_localized_isIso X.carrier
  have := boundaryReductionQuotient_image_isIso Q (Localization.inverts Q anodyneExtensions) 0 X
  rw [objectRawBoundaryComparison, Q.map_comp, Q.map_comp]
  infer_instance

end SerrePositivity.KST.SConstruction
