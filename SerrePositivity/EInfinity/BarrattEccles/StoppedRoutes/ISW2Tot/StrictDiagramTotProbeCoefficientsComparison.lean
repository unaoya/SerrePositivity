module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotBKSections
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedPointMap

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の右frame Hom係数と、全Hom∞比較の入口の同じrightFrameHom図式を全自然に合わせる。
方針：各射をopにする既存のrightFrameHomOpIsoを、元の全図式の射に沿って束ねる。
規約：IS-W2 R02〜R03の係数移送則。pointwiseな同値を自然性の代わりにしない。
使われ方：同じBK普遍錐を全Hom∞比較へ送る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.Opposite _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeCoefficientComparisonModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A

/-- 元の二重反対添字で、同じprobeから全right frameへのHomを集める。 -/
def strictBETotProbeRightHomDiagram (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    Kᵒᵖᵒᵖ ⥤ SSet.{u} :=
  (opOpEquivalence K).functor ⋙ F ⋙ rightFrameHom (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y)

/-- 既存の反対圏Homの同型は、同じ元の全添字図式について自然同型。 -/
def strictBETotProbeCoefficientsIso (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F Y ≅ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficients A K F Y :=
  NatIso.ofComponents
    (fun i => rightFrameHomOpIso (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y) (F.obj i.unop.unop))
    (by
      intro i j f
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro g
      rfl)

/-- 同じ指定BK普遍錐を全rightFrameHom図式へ送った自然変換。 -/
def strictBETotUniversalBKRightHomCone (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    bousfieldKanWeight Kᵒᵖᵒᵖ ⟶
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKProbeWeightedCone A K F ≫
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficientsIso A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).inv

/-- 同じ係数同型で戻すと、元の指定BK普遍錐そのものに戻る。 -/
theorem strictBETotUniversalBKRightHomCone_back (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomCone A K F ≫
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficientsIso A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).hom =
        _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKProbeWeightedCone A K F := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomCone, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 全rightFrameHom図式へ送った、同じ指定BK切断の零単体。 -/
def strictBETotUniversalBKRightHomPoint (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (weightedSections (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F))) _⦋0⦌ :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint Kᵒᵖᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomCone A K F)

/-- 同じ係数同型は、元の指定BK点を全rightFrameHom図式の同じ点へ運ぶ。 -/
theorem strictBETotUniversalBKRightHomPoint_comparison (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    ((weightedSectionsMap (bousfieldKanWeight Kᵒᵖᵒᵖ)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeCoefficientsIso A K F ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A K).obj F)).inv).app (op ⦋0⦌))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKProbeConePoint A K F) = _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniversalBKRightHomPoint A K F := by
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint_map Kᵒᵖᵒᵖ _ _

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
