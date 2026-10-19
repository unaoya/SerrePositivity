module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierVertexLegTriangle
public import SerrePositivity.InfinityCategories.Derived.RoofTetrahedronInitialDiagonal

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) (e : K _⦋1⦌)
variable (H : Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
  ((edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))

/-- 元の辺錐の回収四面体の始点対角辺は、同じ共通閉分母の実辺。 -/
lemma dgVerdierEdgeConeTetrahedron_diagonal :
    (dgNerve A D).δ 1 ((dgNerve A D).δ 1
      (SSet.yonedaEquiv (roofPointSliceTetrahedron _ H.simplex.val))) =
      (dgClosedEdge A D C.denominator.obj.hom).edge := by
  have ha : (dgVerdierOver A D P x : SSet).δ 1
      ((dgVerdierOver A D P x : SSet).δ 1 H.simplex) =
      dgClosedVerdierDenominatorVertex A D P x C.denominator :=
    (congrArg (fun t : (dgVerdierOver A D P x : SSet) _⦋1⦌ =>
      (dgVerdierOver A D P x : SSet).δ 1 t) H.d₁).trans (C.leg (K.δ 0 e)).src_eq
  exact (roofPointSliceTetrahedron_initialDiagonal _ H.simplex.val).trans
    ((congrArg (fun v => (roofPointSliceVertexEdge
      ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x)) v).edge)
        (congrArg Subtype.val ha)).trans (dgClosedOverVertex_edge A D C.denominator.obj.hom))

/-- 指定辺錐の回収四面体の始対象は、共通閉分母の同じ始対象。 -/
lemma dgVerdierEdgeConeTetrahedron_source :
    (SSet.yonedaEquiv (roofPointSliceTetrahedron _ H.simplex.val)).obj 0 =
      ForgetEnrichment.to (Complex A) C.denominator.obj.left :=
  congrArg (fun t : Simplex A D 1 => t.obj 0) (dgVerdierEdgeConeTetrahedron_diagonal A D C e H)

/-- 指定辺錐の二つの脚面の回収三角形は、元の各頂点の固定脚三角形。 -/
lemma dgVerdierEdgeConePositiveFace_triangle (i : Fin 2) :
    SSet.yonedaEquiv (roofPointSliceTriangle _ ((sliceOver _).δ i.succ H.simplex.val)) =
      dgVerdierDiagramLegTriangle A D C (K.δ i e) := by
  fin_cases i
  · exact congrArg (fun t : (dgVerdierOver A D P x : SSet) _⦋1⦌ =>
      SSet.yonedaEquiv (roofPointSliceTriangle _ t.val)) H.d₁
  · exact congrArg (fun t : (dgVerdierOver A D P x : SSet) _⦋1⦌ =>
      SSet.yonedaEquiv (roofPointSliceTriangle _ t.val)) H.d₂

end SerrePositivity.InfinityCategories
