module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedOverMapVertex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGClosedRoofSliceMap

/-! # 厳密屋根 nerve から実 Verdier over 圏への写像

概要：厳密閉分母の屋根比較を、実 Verdier 分母の全部分 over 圏へ因子化する。
方針：指定零単体の一致を全頂点条件へ移し、全部分複体へ持ち上げる。
規約：同値性や cofinality は仮定しない。使われ方：局所化の実屋根比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 厳密屋根比較の指定頂点は元の閉分母の実 over 頂点。 -/
lemma dgClosedRoofSliceMap_vertex (P : Set D) (x : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofSliceMap A D P x).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s).val := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap A D x).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s.obj) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex A D s.obj.hom
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedNerveOverMap_vertex A D x s.obj

/-- 厳密屋根比較の全零単体の像は実 Verdier 分母。 -/
lemma dgClosedRoofSliceMap_mem (P : Set D) (x : D)
    (s : (nerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofSliceMap A D P x).app (Opposite.op ⦋0⦌) s) := by
  have hs : s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (nerveEquiv s) := ComposableArrows.ext₀ rfl
  rw [hs, dgClosedRoofSliceMap_vertex]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex A D (nerveEquiv s).obj.hom)).edge ∈ _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge]
  exact (nerveEquiv s).property

/-- 元の厳密閉分母の屋根 nerve から実 Verdier over 圏への比較写像。 -/
def dgClosedRoofVerdierMap (P : Set D) (x : D) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofSliceMap A D P x)
    (dgClosedRoofSliceMap_mem A D P x)

/-- 全部分圏への包含後は元の ambient slice 比較そのもの。 -/
lemma dgClosedRoofVerdierMap_ι (P : Set D) (x : D) :
    dgClosedRoofVerdierMap A D P x ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofSliceMap A D P x := rfl

/-- 実分母全部分圏への因子化は、元の始域への実射影を厳密に保つ。 -/
lemma dgClosedRoofVerdierMap_source (P : Set D) (x : D) :
    dgClosedRoofVerdierMap A D P x ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofNerveSourceMap A D P x ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A D := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource, ← Category.assoc, dgClosedRoofVerdierMap_ι,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofSliceMap_projection]

/-- 因子化した比較も元の指定閉分母の頂点を厳密に保つ。 -/
lemma dgClosedRoofVerdierMap_vertex (P : Set D) (x : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    (dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s := by
  apply Subtype.ext
  exact dgClosedRoofSliceMap_vertex A D P x s

end SerrePositivity.InfinityCategories.Project.DerivedCategories
