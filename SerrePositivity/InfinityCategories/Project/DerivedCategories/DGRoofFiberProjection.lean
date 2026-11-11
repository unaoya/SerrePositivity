module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofCorrespondenceMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofFiberTransport

/-! # 実屋根 fiber の pinched 同型と元の slice 射影

概要：fiber の全同型は、元の slice への指定射影を厳密に回収する。
方針：pinched 同型を消去し、固定始域輸送と pullback fiber 同型の射影式を使う。
規約：実分母頂点は任意。使われ方：実商比較の fiber 上の鎖写像との照合。
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

omit [Small.{u} D] in
/-- 元の屋根 fiber の同型から slice へ戻すと、元の実射側射影そのもの。 -/
lemma dgRoofCorrespondenceFiberIso_hom_target (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso A D P x y σ).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y) σ ≫ pullback.fst _ _ := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceFiberIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofVertexFiberTransport_ι _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence_source_vertex A D P x σ)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso_hom_ι _ _ σ

/-- 商側の屋根 fiber の同型も、元の実射側の商 slice 射影を回収する。 -/
lemma dgQuotientRoofCorrespondenceFiberIso_hom_target (P : Set D) (x y : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso A D P x y σ).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverVertexSource A D x σ.val))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y) σ ≫
      pullback.fst _ _ := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceFiberIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofVertexFiberTransport_ι _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence_source_vertex A D P x σ)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso_hom_ι _ _ σ

end SerrePositivity.InfinityCategories.Project.DerivedCategories
