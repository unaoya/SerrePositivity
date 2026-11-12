module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofSliceVertices

/-! # dg nerve の実 Verdier 分母の全部分 over 圏

概要：指定頂点へ入る実辺が Verdier 分母である実 slice 頂点の全部分 ∞ 圏を取る。
方針：頂点から回収した実辺の条件と、全部分複体の quasicategory 性を使う。
規約：元の閉零圏の厳密 over 圏とは別の対象。使われ方：屋根比較の実添字 ∞ 圏。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 指定終点の実 slice 頂点の、回収した実辺が Verdier 分母である条件。 -/
def IsDGVerdierOverVertex (P : Set D) (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋0⦌) : Prop :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ σ).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P

/-- 指定終点へ入る実 Verdier 分母の全部分 ∞ 圏。 -/
def dgVerdierOver (P : Set D) (x : D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsDGVerdierOverVertex A D P x)

/-- 実 Verdier 分母の全部分 over 圏は quasicategory。 -/
instance dgVerdierOver_quasicategory (P : Set D) (x : D) :
    Quasicategory (dgVerdierOver A D P x : SSet.{max u v}) := by
  dsimp only [dgVerdierOver]
  infer_instance

/-- 実分母の over 圏から、元の始点への射影。 -/
def dgVerdierOverSource (P : Set D) (x : D) :
    (dgVerdierOver A D P x : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (dgVerdierOver A D P x).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _

/-- 厳密閉分母の各対象を、同じ実分母を持つ実 over 圏の頂点へ送る。 -/
def dgClosedVerdierDenominatorVertex (P : Set D) (x : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) : (dgVerdierOver A D P x : SSet) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex A D s.obj.hom, by
    intro α
    rw [SimplexCategory.hom_zero_zero α]
    simp only [op_id, Functor.map_id_apply]
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex A D s.obj.hom)).edge ∈ _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge]
    exact s.property⟩

omit [Small.{u} D] in
/-- 頂点比較は、元の閉分母の始点を厳密に保つ。 -/
lemma dgClosedVerdierDenominatorVertex_source (P : Set D) (x : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) :
    (dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌)
      (dgClosedVerdierDenominatorVertex A D P x s) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) s.obj.left) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_projection A D s.obj.hom

end SerrePositivity.InfinityCategories.Project.DerivedCategories
