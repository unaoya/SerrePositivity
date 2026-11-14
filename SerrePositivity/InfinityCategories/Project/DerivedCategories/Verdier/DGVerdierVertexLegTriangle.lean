module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGVerdierDiagramHornSource

/-! # 実分母頂点図式の各脚の実三角形と共通端点

概要：各頂点脚の over 三角形を固定し、図式辺ホーンの二面が同じ脚の三角形と一致する。
方針：over 始脚の式で対角分母と両端点を回収し、ホーン指定面の厳密等式を使う。
規約：脚の三角形を図式辺から独立に固定する。使われ方：有限同時細分の脚の辺間一致。
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
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f)

/-- 各頂点脚に付随する実三角形を、図式辺から独立に固定する。 -/
def dgVerdierDiagramLegTriangle (v : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2 :=
  (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      (((C.leg v).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι)).edge))

/-- 各脚三角形の対角辺は元の同じ共通閉分母の実辺。 -/
lemma dgVerdierDiagramLegTriangle_diagonal (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 1 (dgVerdierDiagramLegTriangle A D C v) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D C.denominator.obj.hom).edge := by
  let a := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  let E := (C.leg v).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι)
  exact (SSet.stdSimplex.yonedaEquiv_δ_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a E.edge) 1).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a E.edge 1).trans
      ((congrArg (fun v => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a v).edge) E.src_eq).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedOverVertex_edge A D C.denominator.obj.hom)))

/-- 各脚三角形の零面は、その元の指定終頂点の分母辺。 -/
lemma dgVerdierDiagramLegTriangle_face0 (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ 0 (dgVerdierDiagramLegTriangle A D C v) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) (f.app _ v).val).edge := by
  let a := (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  let E := (C.leg v).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι)
  exact (SSet.stdSimplex.yonedaEquiv_δ_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a E.edge) 0).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a E.edge 0).trans
      (congrArg (fun v => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a v).edge) E.tgt_eq))

/-- 各脚三角形の始対象は、元の共通閉分母の同じ始対象。 -/
lemma dgVerdierDiagramLegTriangle_source (v : K _⦋0⦌) :
    (dgVerdierDiagramLegTriangle A D C v).obj 0 =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) C.denominator.obj.left :=
  congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 => t.obj 0) (dgVerdierDiagramLegTriangle_diagonal A D C v)

/-- 各脚三角形の終対象は、同じ指定対象 x。 -/
lemma dgVerdierDiagramLegTriangle_target (v : K _⦋0⦌) :
    (dgVerdierDiagramLegTriangle A D C v).obj 2 = x :=
  congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 1 => t.obj 1) (dgVerdierDiagramLegTriangle_diagonal A D C v)

/-- 各辺ホーンの面 023 は、その終頂点の同じ固定脚三角形。 -/
lemma dgVerdierDiagramCanonicalFace1_leg (e : K _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e) 1 (by decide) =
      dgVerdierDiagramLegTriangle A D C (K.δ 0 e) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e) 1 (by decide)).trans
    ((SSet.yonedaEquiv_comp (horn.ι (3 : Fin 4) 1 (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e)).symm.trans
        (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn_face1 A D P x (C.leg (K.δ 1 e))
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))))

/-- 各辺ホーンの面 013 は、その始頂点の同じ固定脚三角形。 -/
lemma dgVerdierDiagramCanonicalFace2_leg (e : K _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e) 2 (by decide) =
      dgVerdierDiagramLegTriangle A D C (K.δ 1 e) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornCanonicalFace_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e) 2 (by decide)).trans
    ((SSet.yonedaEquiv_comp (horn.ι (3 : Fin 4) 2 (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e)).symm.trans
        (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn_face2 A D P x (C.leg (K.δ 1 e))
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
