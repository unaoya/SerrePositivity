module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotRightFrameCoherent
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHomInfinity

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じBE right frameの全標的図式を、同じCAlg源の正本共変Hom関手へ結ぶ。
方針：既存の六辺の全比較に、既存Yoneda比較と同じ局所化二胞体を合成する。
規約：IS-W2 R03の既存全比較の係数移送。点ごとのHom同値で代用しない。
使われ方：元の重み付きframe錐と同じnative錐の全制限の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotHomInfinityModelCategory : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotHomInfinityFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 同じ実frame Homの全標的図式と、同じCAlg源に沿う正本Homの全関手同型。 -/
def strictBETotFrameHomInfinityIso (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) [IsCofibrant X] :
    FunctorIso
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject X)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) ≫
        homInfinityCovariant
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))) := by
  let c := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotRightFrameCoherentComparison A X
  have h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameTerminalHomIso
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject X)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) c.2
  exact c.1.trans (by simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_vertex] using h)

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
