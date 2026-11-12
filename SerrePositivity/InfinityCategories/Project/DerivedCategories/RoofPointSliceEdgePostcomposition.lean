module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofPointSliceEdges
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.RoofTargetFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice

/-! # 実辺の slice 頂点の後合成と pinched 表示

概要：実辺の指定 slice 表示は、任意の後合成および pinched Hom の頂点表示と一致する。
方針：台の join 射を Yoneda の自然性で比較する。
規約：全て厳密な頂点等式。使われ方：屋根評価三角形を任意標的の実屋根へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 指定実辺の slice 頂点の後合成は、実像辺の slice 頂点そのもの。 -/
lemma roofPointSliceEdgeVertex_postcomp {X Y : SSet.{u}} (F : X ⟶ Y) {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap F y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex e) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex (e.map ((truncation 2).map F)) := by
  apply Subtype.ext
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_val]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm e.edge) ≫ F =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋1⦌) e.edge)
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]

/-- 実辺の pinched 頂点を slice fiber に含めると、その実辺の指定 slice 頂点。 -/
lemma roofPinchedVertex_slice {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).hom.app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x y).symm e)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceEdgeVertex e := by
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
