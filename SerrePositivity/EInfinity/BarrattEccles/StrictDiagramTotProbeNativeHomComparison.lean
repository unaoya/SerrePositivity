module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotRightFrameComparison
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitProbeComparison
public import SerrePositivity.EInfinity.BarrattEccles.CAlgQuasiIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentPinchedTransport

/-!
概要：元の任意のBE試験対象のprobeを、同じnative Homの始点から消す。
方針：元のprobe比較の実辺の可逆性と、既存pinched前合成の同値を合成。
規約：IS-W2 R03の係数移送則。probe・CAlg源・実比較を変更しない。
使われ方：普遍probe錐のHom比較を元の指定頂点へ戻す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotProbeNativeModelCategory : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotProbeNativeCofibrant (X : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A X) := framedLimitProbe_cofibrant A X
attribute [local instance] rightFrameHom_kanComplex

/-- 元のprobe比較の実辺が表す、元の同じCAlg源の頂点の同型。 -/
def strictBETotProbeSourceIso (X : (operad A).Algebra) :
    VertexIso ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (framedLimitProbe A X)))
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)) := by
  have h := algebraCAlgSource_map_weak A (framedLimitProbeComparison A X)
    (framedLimitProbeComparison_quasiIso A X)
  exact @asIso _ _ _ _
    (Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk (framedLimitProbeComparison A X)).map (algebraCAlgSource A)).toTruncated) h

/-- 始点同型の順方向は元のprobe比較の同じ実辺の類。 -/
theorem strictBETotProbeSourceIso_hom (X : (operad A).Algebra) :
    (strictBETotProbeSourceIso A X).hom = Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk (framedLimitProbeComparison A X)).map (algebraCAlgSource A)).toTruncated := rfl

/-- 元の任意の試験対象に対する無条件の実right-frame Homと同じnative Homの比較。 -/
def strictBETotProbeNativeHomEquivalence (X Y : (operad A).Algebra) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u+1,u}).obj
        ((rightFrameHom (rightFrameFamily A) (framedLimitProbe A X)).obj Y))
      (pinchedHom ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex X))
        ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))) := by
  exact (strictBETotRightFramePinchedEquivalence A (framedLimitProbe A X) Y).trans
    (pinchedPrecomposeEquivalence _ (strictBETotProbeSourceIso A X))

/-- 実比較の順射は、同じframe比較と同じprobe比較の逆による前合成。 -/
theorem strictBETotProbeNativeHomEquivalence_hom (X Y : (operad A).Algebra) :
    (strictBETotProbeNativeHomEquivalence A X Y).hom =
      (strictBETotRightFramePinchedEquivalence A (framedLimitProbe A X) Y).hom ≫
        SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose
          ((algebraCAlgSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y))
          (strictBETotProbeSourceIso A X).inv := rfl

end SerrePositivity.EInfinity.BarrattEccles
