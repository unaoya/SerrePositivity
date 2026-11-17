module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotRightFrameComparison
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitProbeComparison
public import SerrePositivity.EInfinity.BarrattEccles.CAlgQuasiIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentPinchedTransport

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の任意のBE試験対象のprobeを、同じnative Homの始点から消す。
方針：元のprobe比較の実辺の可逆性と、既存pinched前合成の同値を合成。
規約：IS-W2 R03の係数移送則。probe・CAlg源・実比較を変更しない。
使われ方：普遍probe錐のHom比較を元の指定頂点へ戻す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotProbeNativeModelCategory : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotProbeNativeCofibrant (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A X
attribute [local instance] rightFrameHom_kanComplex

/-- 元のprobe比較の実辺が表す、元の同じCAlg源の頂点の同型。 -/
def strictBETotProbeSourceIso (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    VertexIso ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X)))
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)) := by
  have h := _root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource_map_weak A (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A X)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison_quasiIso A X)
  exact @asIso _ _ _ _
    (Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A X)).map (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A)).toTruncated) h

/-- 始点同型の順方向は元のprobe比較の同じ実辺の類。 -/
theorem strictBETotProbeSourceIso_hom (X : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeSourceIso A X).hom = Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A X)).map (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A)).toTruncated := rfl

/-- 元の任意の試験対象に対する無条件の実right-frame Homと同じnative Homの比較。 -/
def strictBETotProbeNativeHomEquivalence (X Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u+1,u}).obj
        ((rightFrameHom (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X)).obj Y))
      (pinchedHom ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))) := by
  exact (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotRightFramePinchedEquivalence A (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X) Y).trans
    (pinchedPrecomposeEquivalence _ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeSourceIso A X))

/-- 実比較の順射は、同じframe比較と同じprobe比較の逆による前合成。 -/
theorem strictBETotProbeNativeHomEquivalence_hom (X Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeNativeHomEquivalence A X Y).hom =
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotRightFramePinchedEquivalence A (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A X) Y).hom ≫
        SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeSourceIso A X).inv := rfl

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
