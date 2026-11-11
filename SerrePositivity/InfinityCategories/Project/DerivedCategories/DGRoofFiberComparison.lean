module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofFiberProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientPinchedSlice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-! # 実屋根の商比較の全 fiber と Hom 鎖写像の一致

概要：任意の実分母頂点の fiber 上の商比較は、元の商の全 Hom 鎖写像の pinched 作用。
方針：元の実 target slice への単射な包含後で比較し、両 fiber 同型の射影公式を使う。
規約：単体集合の射の厳密な等式。使われ方：有限相対充填の実屋根への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の実屋根比較が、同じ指定実分母頂点の fiber に誘導する写像。 -/
def dgRoofCorrespondenceFiberMap (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y) σ ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y) σ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_projection A D P x y) σ

/-- fiber 上の比較は、元の実屋根への包含と厳密に可換。 -/
lemma dgRoofCorrespondenceFiberMap_ι (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgRoofCorrespondenceFiberMap A D P x y σ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y) σ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y) σ ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι _ _ _ _ σ

/-- 実屋根の商比較の全 fiber は、元の商の Hom 鎖写像の実 pinched 写像と一致。 -/
theorem dgRoofCorrespondenceFiberMap_comparison (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgRoofCorrespondenceFiberMap A D P x y σ ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y σ).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y σ).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val) y) := by
  let q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj q))
  have : Mono j := by dsimp only [j]; infer_instance
  apply (cancel_mono j).mp
  dsimp only [j]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso_hom_target]
  rw [← Category.assoc (dgRoofCorrespondenceFiberMap A D P x y σ),
    dgRoofCorrespondenceFiberMap_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_target]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y) σ),
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso_hom_target]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientTargetSliceMap_pinched]

/-- 両 fiber 同型で共役した実商比較は、元の全 Hom 鎖写像そのもの。 -/
lemma dgRoofCorrespondenceFiberMap_conjugate (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y σ).inv ≫
      dgRoofCorrespondenceFiberMap A D P x y σ ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y σ).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val) y) := by
  rw [dgRoofCorrespondenceFiberMap_comparison, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
