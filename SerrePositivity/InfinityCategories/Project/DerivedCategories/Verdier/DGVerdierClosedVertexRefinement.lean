module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierVertexLegTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGClosedEdgeCompositionEquality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofRefinements

/-! # 頂点錐の辺族に依存しない一つの閉始点細分

概要：元の頂点錐と一つの追加実閉分母だけから、共通閉細分分母と実 apex を固定する。
方針：閉分母の合成表示を保持する。使われ方：高次の全辺錐に共通な頂点脚の構成。
規約：辺族や各充填の選択をデータに含めない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f)

/-- 頂点錐の同じ追加実閉分母。辺の族や充填の選択に依存しない。 -/
structure DGVerdierClosedVertexRefinement where
  q : D
  s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ C.denominator.obj.left
  denominator : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P

variable (R : DGVerdierClosedVertexRefinement A D C)

/-- 元の共通閉分母を同じ追加閉分母で細分した、一つの閉実分母。 -/
def DGVerdierClosedVertexRefinement.commonDenominator : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofRefine A D P x C.denominator R.s R.denominator

/-- 全辺に共通する、同じ閉細分分母の実 over 頂点。 -/
def DGVerdierClosedVertexRefinement.commonApex : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x R.commonDenominator

end SerrePositivity.InfinityCategories.Project.DerivedCategories
