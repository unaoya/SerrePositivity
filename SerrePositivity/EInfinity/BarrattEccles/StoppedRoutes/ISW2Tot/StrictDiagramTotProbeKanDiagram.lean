module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotProbeKanCoefficients

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じBE TotのBK係数を、既存の全frame比較のcoherent図式と照合する。
方針：同じ第零Kan係数を全添字関手で引き戻し、既存のcoherent nerveの前合成則を使う。
規約：IS-W2 R02〜R03の合成・係数移送則。全高次単体を保持する。
使われ方：指定BK切断からnative錐の分類図式への入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeKanDiagramModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotProbeKanDiagramFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance strictBETotProbeKanDiagramCof (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A Y

/-- 元の同じraw係数を宇宙変更してEx∞に送った全Kan図式。 -/
def strictBETotProbeKanDiagram (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    AsSmall.{u+1} Kᵒᵖᵒᵖ ⥤ KanObject.{u+1} :=
  AsSmall.down ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamily
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeRightHomDiagram A K F Y ⋙ SSet.uliftFunctor.{u+1,u})

/-- 元の同じ全Kan図式は、全frame比較の第零図式を元の添字関手で引き戻したもの。 -/
theorem strictBETotProbeKanDiagram_frame (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y = _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeFrameIndex A K F ⋙
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockKanDiagram
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
          (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) 0 := rfl

/-- 同じ全Kan図式をcoherentに実現しても、元の全frame比較の前合成そのものになる。 -/
theorem strictBETotProbeKanDiagram_coherent (F : K ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    kanDiagramCoherentNerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram A K F Y) =
      (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeFrameIndex A K F)) ≫
        _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockCoherentDiagram
          ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).atObject
            (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y)) (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) 0 := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeKanDiagram_frame]
  exact (kanDiagramCoherentNerve_precomp _ _).symm

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
