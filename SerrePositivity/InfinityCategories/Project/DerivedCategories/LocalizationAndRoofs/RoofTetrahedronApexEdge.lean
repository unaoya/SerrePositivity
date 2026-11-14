module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofSliceTetrahedronInverse

/-! # 実四面体から戻した over 二単体の始頂点の分母辺

概要：回収 over 二単体の始頂点の指定辺を、元の四面体の面 023 の対角辺と同定する。
方針：二単体の一面の回収公式と、その over 辺の始脚公式を合成する。
規約：実一次単体の厳密一致。使われ方：閉細分後の始頂点の実分母性の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)
variable {b c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋0⦌}
variable (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a)) b c)

/-- 回収 over 三角形の始頂点の構造辺は、元の面 023 の対角辺 03 そのもの。 -/
lemma roofPointSliceTwoSimplexOfTetrahedron_apex_edge (F : Δ[3] ⟶ X)
    (hF₀ : SSet.stdSimplex.δ (0 : Fin 4) ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a e.edge) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1 ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron a e F hF₀)))).edge =
      X.δ 1 ((SSet.yonedaEquiv (X := X)) (SSet.stdSimplex.δ (1 : Fin 4) ≫ F)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle_leg a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron a e F hF₀)) 1).symm.trans
      ((SSet.stdSimplex.yonedaEquiv_δ_comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTriangle a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron a e F hF₀))) (1 : Fin 3)).trans
          (congrArg (fun t => X.δ 1 ((SSet.yonedaEquiv (X := X)) t))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTwoSimplexOfTetrahedron_face a e F hF₀ 1)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
