module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierVertexLegTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofTetrahedronInitialDiagonal

/-! # 指定辺錐の回収四面体の共通始対象と二つの脚面

概要：同じ頂点錐の任意の合成二単体の回収四面体は、共通分母始域と固定脚面を持つ。
方針：合成二単体の面と元の脚の端点を、回収四面体の対角辺へ渡す。
規約：充填の選択に依存しない。使われ方：任意の辺錐の同じ閉始点細分。
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
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (e : K _⦋1⦌)
variable (H : Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))

/-- 元の辺錐の回収四面体の始点対角辺は、同じ共通閉分母の実辺。 -/
lemma dgVerdierEdgeConeTetrahedron_diagonal :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ H.simplex.val))) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D C.denominator.obj.hom).edge := by
  have ha : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1 H.simplex) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x C.denominator :=
    (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋1⦌ =>
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 1 t) H.d₁).trans (C.leg (K.δ 0 e)).src_eq
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_initialDiagonal _ H.simplex.val).trans
    ((congrArg (fun v => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) v).edge)
        (congrArg Subtype.val ha)).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D C.denominator.obj.hom))

/-- 指定辺錐の回収四面体の始対象は、共通閉分母の同じ始対象。 -/
lemma dgVerdierEdgeConeTetrahedron_source :
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ H.simplex.val)).obj 0 =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) C.denominator.obj.left :=
  congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 => t.obj 0) (dgVerdierEdgeConeTetrahedron_diagonal A D C e H)

/-- 指定辺錐の二つの脚面の回収三角形は、元の各頂点の固定脚三角形。 -/
lemma dgVerdierEdgeConePositiveFace_triangle (i : Fin 2) :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ i.succ H.simplex.val)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C (K.δ i e) := by
  fin_cases i
  · exact congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋1⦌ =>
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ t.val)) H.d₁
  · exact congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋1⦌ =>
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ t.val)) H.d₂

end SerrePositivity.InfinityCategories.Project.DerivedCategories
