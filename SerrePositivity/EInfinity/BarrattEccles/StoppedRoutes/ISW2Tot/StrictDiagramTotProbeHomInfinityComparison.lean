module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotFrameHomInfinity
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotProbeNativeHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.VertexIsoUniverseLift

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じprobe比較を、正本共変Hom関手の全標的の同型として消す。
方針：同じ源の頂点同型を反転・宇宙持ち上げし、元のco-Yonedaで写す。
規約：IS-W2 R03の係数移送則。点ごとの逆を独立に選ばない。
使われ方：元の任意の試験対象の実frame Homとnative全錐の制限の比較。
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
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotProbeHomInfinityModelCategory : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotProbeHomInfinityFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance strictBETotProbeHomInfinityCofibrant (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A X

/-- 元のprobe比較は、同じ正本共変Hom関手の全標的で同じ源の同型を与える。 -/
def strictBETotProbeHomInfinitySourceIso (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    FunctorIso
      (homInfinityCovariant ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X))))
      (homInfinityCovariant ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex X))) := by
  have h := liftVertexIso.{u+1,u+2} (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeSourceIso A X).op
  have k := h.map (coyonedaInfinityMap (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
  rw [coyonedaInfinityMap_vertex, coyonedaInfinityMap_vertex] at k
  exact k

/-- 元の任意の試験対象の実frame Homは、同じ正本Hom関手へ全標的で自然同型。 -/
def strictBETotProbeFrameHomInfinityIso (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    FunctorIso
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
          (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) 0)
      ((SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) ≫
        homInfinityCovariant
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotFrameHomInfinityIso A (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X)).trans
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeHomInfinitySourceIso A X).precomp
      ((SSet.uliftFunctor.{u+2,u+1}).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)))

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
