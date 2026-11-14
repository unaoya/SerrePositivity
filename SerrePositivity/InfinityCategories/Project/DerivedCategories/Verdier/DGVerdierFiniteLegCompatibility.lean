module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierFiniteVertexLegs

/-! # 有限辺充填の二脚と頂点ごとの単一実脚の一致

概要：各辺の充填から回収した二脚が、全頂点に固定した同じ実脚と一致する。
方針：回収三角形の厳密一致を over 一単体の単射性へ渡す。
規約：型付き辺の厳密等式。使われ方：一つの頂点錐の全指定有限辺上の合成整合性。
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
variable {C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f} {m : ℕ} {e : Fin m → K _⦋1⦌}
variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement A D C e)

/-- 各辺の始点側の実脚は、その頂点に固定した同じ単一実脚。 -/
lemma DGVerdierFiniteEdgeRefinement.sourceLeg_eq_vertexLeg (i : Fin m) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.sourceLeg A D T i =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.vertexLeg A D T (K.δ 1 (e i)) := by
  apply Truncated.Edge.ext
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_injective
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 2
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverTriangle A D C (e i) (T.refinements i).q
      (T.refinements i).s (T.refinements i).filler (T.refinements i).fac)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.vertexLegSimplex A D T (K.δ 1 (e i)))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.vertexLegSimplex_triangle A D T (K.δ 1 (e i))]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverTriangle]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron_face]
  change SSet.stdSimplex.δ (2 : Fin 4) ≫ (T.refinements i).filler =
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.legTriangle A D T (K.δ 1 (e i)))
  rw [← horn.ι_ι_assoc (3 : Fin 4) 2 (by decide)]
  exact ((congrArg (fun G => horn.ι (3 : Fin 4) 2 (by decide) ≫ G)
    (T.refinements i).fac).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement_face2 _ _ _)).trans
        (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.refinedFace2_legTriangle A D T i))

/-- 各辺の終点側の実脚は、その頂点に固定した同じ単一実脚。 -/
lemma DGVerdierFiniteEdgeRefinement.targetLeg_eq_vertexLeg (i : Fin m) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.targetLeg A D T i =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.vertexLeg A D T (K.δ 0 (e i)) := by
  apply Truncated.Edge.ext
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_injective
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverTriangle A D C (e i) (T.refinements i).q
      (T.refinements i).s (T.refinements i).filler (T.refinements i).fac)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.vertexLegSimplex A D T (K.δ 0 (e i)))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.vertexLegSimplex_triangle A D T (K.δ 0 (e i))]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverTriangle]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron_face]
  change SSet.stdSimplex.δ (1 : Fin 4) ≫ (T.refinements i).filler =
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.legTriangle A D T (K.δ 0 (e i)))
  rw [← horn.ι_ι_assoc (3 : Fin 4) 1 (by decide)]
  exact ((congrArg (fun G => horn.ι (3 : Fin 4) 1 (by decide) ≫ G)
    (T.refinements i).fac).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornSourceRefinement_face1 _ _ _)).trans
        (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.refinedFace1_legTriangle A D T i))

/-- 同じ頂点錐の二脚と各指定実辺は、同時供給した実合成二単体を持つ。 -/
def DGVerdierFiniteEdgeRefinement.vertexConeCompStruct (i : Fin m) :
    Truncated.Edge.CompStruct
      (T.vertexCone.leg (K.δ 1 (e i)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (e i)).map ((truncation 2).map f))
      (T.vertexCone.leg (K.δ 0 (e i))) := by
  rw [show T.vertexCone.leg (K.δ 1 (e i)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.sourceLeg A D T i from
        (DGVerdierFiniteEdgeRefinement.sourceLeg_eq_vertexLeg A D T i).symm,
    show T.vertexCone.leg (K.δ 0 (e i)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.targetLeg A D T i from
        (DGVerdierFiniteEdgeRefinement.targetLeg_eq_vertexLeg A D T i).symm]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierFiniteEdgeRefinement.compStruct A D T i

/-- 有限頂点の実図式の指定有限辺族には、一つの頂点錐と全辺の合成二単体が存在する。 -/
theorem dgVerdierDiagramFiniteEdges_exists_vertexCone
    (P : Set D) (x : D) {K : SSet.{max u v}} [Finite (K _⦋0⦌)]
    (f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}))
    {m : ℕ} (e : Fin m → K _⦋1⦌) :
    ∃ C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f, ∀ i,
      Nonempty (Truncated.Edge.CompStruct
        (C.leg (K.δ 1 (e i)))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (e i)).map ((truncation 2).map f))
        (C.leg (K.δ 0 (e i)))) := by
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramVertexCone_nonempty A D P x f
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierFiniteEdgeRefinement_nonempty A D C e
  exact ⟨T.vertexCone, fun i =>
    ⟨DGVerdierFiniteEdgeRefinement.vertexConeCompStruct A D T i⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
