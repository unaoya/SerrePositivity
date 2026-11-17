module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotProbeSourceFunctor
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitComparison

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の普遍BK錐への始域の前合成を、元のweighted Hom同値による同じ射の像と合わせる。
方針：全始域の係数同型の自然性と、既存probe比較・weighted Hom同値の始域自然性を合成する。
規約：IS-W2 R02〜R03の既存の単位・始域自然性の法則。元の射f・probeを保持する。
使われ方：元のnative錐の制限と、元の計算対象へのHomの対応の正規化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.Opposite
open _root_.SerrePositivity.DiagramModel
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotUniversalSourceNaturalityModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- 元の同じ普遍BK錐を、元のfのprobeによる前合成で移す。 -/
def strictBETotBKProbeArrowCone (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    {Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (f : Y ⟶ (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F) :
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight
      Kᵒᵖᵒᵖ ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F Y :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomCone A K F ≫
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomSourceFunctor A K F).map f.op

/-- 元のfから得たBK錐は、元のweighted Hom同値による同じfの像。 -/
theorem strictBETotBKProbeArrowCone_comparison (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    {Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (f : Y ⟶ (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKProbeArrowCone A K F f ≫ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficientsIso A K F Y).hom =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison K ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y)
          (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A Y ≫ f) := by
  let T := (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F
  have hi : (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomSourceFunctor A K F).map f.op ≫
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficientsIso A K F Y).hom =
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficientsIso A K F T).hom ≫
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficientsSourceFunctor A K F).map f.op :=
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficientsSourceIso A K F).hom.naturality f.op
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotBKProbeArrowCone, Category.assoc, hi, ← Category.assoc,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomCone_back, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKProbeWeightedCone,
    Category.assoc, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalProbeWeightedCone_comparison]
  change _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison K ≫
    (_root_.SerrePositivity.EInfinity.BarrattEccles.weightedCotensorHomEquiv A K F (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weight K) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A T)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A T) ≫
        (FrameWeightRealization.hom Kᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram A K F)).map
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A).map f).op) = _
  rw [← _root_.SerrePositivity.EInfinity.BarrattEccles.weightedCotensorHomEquiv_precomp]
  have hc (Z : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
      (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparisonNatTrans A).app Z = _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A Z := rfl
  have hn : (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A).map f ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A T =
      _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A Y ≫ f := by
    have h := (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparisonNatTrans A).naturality f
    simp only [Functor.id_map, hc] at h
    exact h
  rw [hn]
  rfl

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
