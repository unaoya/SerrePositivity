module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointHomEdgeLift

/-!
概要：底を保つ全 Hom の比較辺の族の終点係数を、元の Hom のパラメータそのものと同定する。
方針：底の合成族・終点側への制限・元の点 Hom の射影を uncurry して続けて計算する。
規約：等号による点図式の移送を消すだけで、元のパラメータは変更しない。
使われ方：指定余錐の共通脚の終点係数の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 比較辺の全 Hom の族の底を終点で読むと、元の全 Hom の標準点図式の族そのもの。 -/
lemma pointRestrictionFullEdgeFamily_tip_uncurry {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : F ⟶ B) [InnerFibration q]
    (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌)
    {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) d) y)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullEdgeFamily p q r hr d e y) ≫ q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso p d y).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm d ≫ p)) y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullEdgeFamily_base,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionBaseEdgeFamily_target,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionEdgeFamily_base, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderUncurry_eqToHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialRestrictionEdgeBase_eq p q r hr d e)]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
