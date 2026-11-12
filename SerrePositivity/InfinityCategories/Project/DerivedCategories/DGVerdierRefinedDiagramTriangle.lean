module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornRefinementFiller

/-! # 実分母図式辺の閉始点細分後の実四面体と over 三角形

概要：任意の実図式辺に追加閉分母と実充填四面体を供給し、指定辺を保つ over 二単体へ戻す。
方針：最後辺の実分母性で原始元を供給し、終端面の厳密一致から over へ戻す。
規約：細分始頂点の実分母部分圏への所属は別に照合する。使われ方：有限共通始錐の整合性。
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
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (e : K _⦋1⦌)

omit [Small.{u} D] in
/-- 細分した実図式辺ホーンの充填は、元の指定実図式辺の三角形を厳密に保つ。 -/
lemma dgVerdierDiagramRefinedFiller_face0 (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e)).obj 0))
    (F : Δ[3] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e) q s) :
    SSet.stdSimplex.δ (0 : Fin 4) ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι.app _ (f.app _ e)) := by
  rw [← horn.ι_ι_assoc (3 : Fin 4) 0 (by decide), hF,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement_preserves_face0]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierConeEdgeHorn_face0 A D P x (C.leg (K.δ 1 e))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e))

/-- 同じ閉細分充填から回収する、終点を元の x に固定した実 over 二単体。 -/
def dgVerdierDiagramRefinedOverTriangle (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e)).obj 0))
    (F : Δ[3] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e) q s) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron _
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι)) F
    (dgVerdierDiagramRefinedFiller_face0 A D C e q s F hF)

omit [Small.{u} D] in
/-- 回収した実 over 二単体の零面は、元の指定図式辺と厳密に同じ。 -/
lemma dgVerdierDiagramRefinedOverTriangle_face0 (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e)).obj 0))
    (F : Δ[3] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e) q s) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))).δ 0
      (dgVerdierDiagramRefinedOverTriangle A D C e q s F hF) =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x).ι.app _ (f.app _ e) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_injective
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron_face _ _ F
    (dgVerdierDiagramRefinedFiller_face0 A D C e q s F hF) 0).trans
      (dgVerdierDiagramRefinedFiller_face0 A D C e q s F hF)

/-- 指定した実図式辺のホーン全体は、一つの追加実閉分母の後で実際に充填できる。 -/
theorem dgVerdierDiagramEdge_exists_refinedFiller [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] :
    ∃ (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e)).obj 0)),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
        ∃ F : Δ[3] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D, (horn 3 3).ι ≫ F =
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e) q s :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHorn_exists_sourceRefinement_filler P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramEdgeHorn A D C e)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLastClosed_mem A D P x C e)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
