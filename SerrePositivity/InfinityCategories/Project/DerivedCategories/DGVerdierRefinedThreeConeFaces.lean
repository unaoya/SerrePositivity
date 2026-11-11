module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierRefinedThreeSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementCongruence

/-! # 細分後の実分母三単体の三面は同じ細分辺錐

概要：回収三単体の三つの錐面を、元の指定辺錐の同じ閉始点細分へ厳密に同定する。
方針：元の正番号面の四面体と始対象を照合し、一般閉始点細分の合同性を使う。
規約：元の零面・追加実閉辺を保持。使われ方：有限二次図式の共通面の組み立て。
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
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))


/-- 元のホーンの各正番号面は、指定辺錐の回収四面体そのもの。 -/
lemma dgVerdierTriangleCanonicalFace_cone (i : Fin 3) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornCanonicalFace (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)
      i.succ.castSucc (Fin.castSucc_ne_last _) =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ (H i).simplex.val) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornCanonicalFace_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)
    i.succ.castSucc (Fin.castSucc_ne_last _)).trans
      ((SSet.yonedaEquiv_comp (horn.ι (4 : Fin 5) i.succ.castSucc (Fin.castSucc_ne_last _))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).symm.trans
          (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn_face_cone A D C σ H i)))

/-- 指定辺錐の回収四面体の始対象は、同じ元のホーンの回収始対象。 -/
lemma dgVerdierTriangleConeTetrahedron_source (i : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 0 =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ (H i).simplex.val)).obj 0 := by
  fin_cases i
  · exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => t.obj 0)
      (dgVerdierTriangleCanonicalFace_cone A D C σ H 0)
  · exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => t.obj 0)
      (dgVerdierTriangleCanonicalFace_cone A D C σ H 1)
  · exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 3 => t.obj 0)
      (dgVerdierTriangleCanonicalFace_cone A D C σ H 2)

variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
variable (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)

/-- 元の各指定辺錐を、同じ追加実閉辺で始点細分した実分母二単体。 -/
def dgVerdierDiagramRefinedEdgeCone (i : Fin 3) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement A D P x (H i).simplex q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (dgVerdierTriangleConeTetrahedron_source A D C σ H i))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P s
      (dgVerdierTriangleConeTetrahedron_source A D C σ H i) hs)

/-- 細分後の実分母三単体の各正番号面は、同じ閉射で細分した元の指定辺錐。 -/
lemma dgVerdierDiagramRefinedThreeSimplex_face_cone (F : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s)
    (i : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedThreeSimplex A D C σ H q s hs F hF) =
        dgVerdierDiagramRefinedEdgeCone A D C σ H q s hs i := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_injective
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr
    (dgVerdierTriangleCanonicalFace_cone A D C σ H i) q q s
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (dgVerdierTriangleConeTetrahedron_source A D C σ H i))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s _).symm
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement_tetrahedron A D P x (H i).simplex q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (dgVerdierTriangleConeTetrahedron_source A D C σ H i))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P s
      (dgVerdierTriangleConeTetrahedron_source A D C σ H i) hs)
  fin_cases i
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex_face1 A D C σ H q s F hF).trans
      ((congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm hc).trans hr.symm)
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex_face2 A D C σ H q s F hF).trans
      ((congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm hc).trans hr.symm)
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex_face3 A D C σ H q s F hF).trans
      ((congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm hc).trans hr.symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
