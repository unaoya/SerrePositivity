module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotProbeKanCoefficients

/-!
概要：同じBE TotのBK係数を、既存の全frame比較のcoherent図式と照合する。
方針：同じ第零Kan係数を全添字関手で引き戻し、既存のcoherent nerveの前合成則を使う。
規約：IS-W2 R02〜R03の合成・係数移送則。全高次単体を保持する。
使われ方：指定BK切断からnative錐の分類図式への入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeKanDiagramModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotProbeKanDiagramFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotProbeKanDiagramCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y

/-- 元の同じraw係数を宇宙変更してEx∞に送った全Kan図式。 -/
def strictBETotProbeKanDiagram (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    AsSmall.{u+1} Kᵒᵖᵒᵖ ⥤ KanObject.{u+1} :=
  AsSmall.down ⋙ FrameHom.kanHomFamily
    (strictBETotProbeRightHomDiagram A K F Y ⋙ SSet.uliftFunctor.{u+1,u})

/-- 元の同じ全Kan図式は、全frame比較の第零図式を元の添字関手で引き戻したもの。 -/
theorem strictBETotProbeKanDiagram_frame (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    strictBETotProbeKanDiagram A K F Y = strictBETotProbeFrameIndex A K F ⋙
      FrameHom.rightFrameHammockKanDiagram
        ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
          (framedLimitProbe A Y)) (rightFrameFamily A) 0 := rfl

/-- 同じ全Kan図式をcoherentに実現しても、元の全frame比較の前合成そのものになる。 -/
theorem strictBETotProbeKanDiagram_coherent (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    kanDiagramCoherentNerve (strictBETotProbeKanDiagram A K F Y) =
      (SSet.uliftFunctor.{u+2,u+1}).map (nerveMap (strictBETotProbeFrameIndex A K F)) ≫
        FrameHom.rightFrameHammockCoherentDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
            (framedLimitProbe A Y)) (rightFrameFamily A) 0 := by
  rw [strictBETotProbeKanDiagram_frame]
  exact (kanDiagramCoherentNerve_precomp _ _).symm

end SerrePositivity.EInfinity.BarrattEccles
