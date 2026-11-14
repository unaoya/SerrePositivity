module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierClosedVertexLegs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierEdgeConeSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGOverTwoSimplexRefinedFaces

/-! # 同じ閉始点細分による実辺錐と固定頂点脚の合成二単体

概要：元の任意の辺錐を同じ閉分母で細分し、その二脚を頂点ごとの固定実脚へ同定する。
方針：正番号面の三角形を元の固定脚三角形の細分と比較し、over 辺の単射性を使う。
規約：同じ指定二単体の台を保つ。使われ方：有限高次図式の共通頂点錐と辺整合性。
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
variable {C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement A D C)

variable (e : K _⦋1⦌)
variable (H : Truncated.Edge.CompStruct (C.leg (K.δ 1 e))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f)) (C.leg (K.δ 0 e)))

/-- 元の指定辺錐を、共通の同じ追加閉分母で細分した実分母二単体。 -/
def DGVerdierClosedVertexRefinement.edgeCone : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋2⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement A D P x H.simplex R.q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdgeConeTetrahedron_source A D C e H).symm)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P R.s
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdgeConeTetrahedron_source A D C e H).symm R.denominator)

/-- 細分した辺錐の零面は、元の指定実図式辺そのもの。 -/
lemma DGVerdierClosedVertexRefinement.edgeCone_face0 :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0
      (DGVerdierClosedVertexRefinement.edgeCone A D R e H) = f.app _ e :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement_face0 A D P x H.simplex R.q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdgeConeTetrahedron_source A D C e H).symm)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_mem A D P R.s
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdgeConeTetrahedron_source A D C e H).symm R.denominator)).trans H.d₀

/-- 細分した辺錐の各脚面は、その図式頂点ごとに固定した同じ単一実脚。 -/
lemma DGVerdierClosedVertexRefinement.edgeCone_face_positive (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ i.succ (DGVerdierClosedVertexRefinement.edgeCone A D R e H) =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexCone A D R).leg (K.δ i e)).edge := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_injective
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  let sH := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdgeConeTetrahedron_source A D C e H).symm
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ i.succ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement A D x H.simplex.val R.q sH)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexLegSimplex A D R (K.δ i e))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexLegSimplex_triangle A D R (K.δ i e)]
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexInitialRefinement_face_positive A D x H.simplex.val R.q sH i
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdgeConePositiveFace_triangle A D C e H i) R.q R.q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D sH (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverTwoSimplexPositiveFace_source A D x H.simplex.val i))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C (K.δ i e)).symm)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D sH _).trans
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D R.s _).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D R.s _).symm))
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_triangle A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle A D C (K.δ i e))
    R.q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D R.s
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramLegTriangle_source A D C (K.δ i e)).symm)
  exact hf.trans (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (hc.trans ht))

/-- 元の任意の辺錐から、同じ共通頂点錐の二脚の合成整合性を構成する。 -/
def DGVerdierClosedVertexRefinement.edgeCompStruct :
    Truncated.Edge.CompStruct ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexCone A D R).leg (K.δ 1 e))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map f))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierClosedVertexRefinement.vertexCone A D R).leg (K.δ 0 e)) where
  simplex := DGVerdierClosedVertexRefinement.edgeCone A D R e H
  d₂ := DGVerdierClosedVertexRefinement.edgeCone_face_positive A D R e H 1
  d₀ := DGVerdierClosedVertexRefinement.edgeCone_face0 A D R e H
  d₁ := DGVerdierClosedVertexRefinement.edgeCone_face_positive A D R e H 0

end SerrePositivity.InfinityCategories.Project.DerivedCategories
