module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotModelSource
public import SerrePositivity.EInfinity.BarrattEccles.RightFrames
public import SerrePositivity.EInfinity.BarrattEccles.MappingFactorizations
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelRightFrameComparison

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じBE right frameの実Homと、元の全CAlg源のnative pinched Homを比較する。
方針：既存の一般モデル圏の比較へ、同じBEモデル・frame・全局所化を代入。
規約：IS-W2 R03の係数移送・表示の法則。全代数源・同じ比較を保持。
使われ方：実frame錐と指定native全Tot錐の制限比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]
local instance _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.instModelCategoryAlgebraOperad_1 : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.instHasFunctorialFactorizationAlgebraOperadCofibrationsTrivialFibrations : (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
    (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
attribute [local instance] rightFrameHom_kanComplex

/-- 同じ全BE源の両端を持つ、実right frame Homとnative pinched Homの全同値。 -/
def strictBETotRightFramePinchedEquivalence
    (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) [IsCofibrant X] (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u+1,u}).obj ((rightFrameHom (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) X).obj Y))
      (pinchedHom ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelRightFramePinchedEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_isLocalization A) X Y
  simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_vertex] using h

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
