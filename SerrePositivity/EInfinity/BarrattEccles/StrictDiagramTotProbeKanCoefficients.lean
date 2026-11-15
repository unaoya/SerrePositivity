module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotProbeCoefficientsComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotFrameHomInfinity
public import SerrePositivity.EInfinity.HomotopyWeight.BousfieldKanUniversePoints
public import SerrePositivity.EInfinity.HomotopyWeight.BousfieldKanExInfinityUnit

/-!
概要：同じBE TotのBK錐を全Hom∞比較の同じ第零係数へ送る。
方針：元の宇宙変更の指定射と同じEx∞単位を合成する。
規約：IS-W2 R02〜R03の既存の係数移送則。別のframeやprobeを選ばない。
使われ方：元の指定BK点を同じcoherentな分類図式へ運ぶ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra Opposite SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotProbeKanCoefficientsModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotProbeKanCoefficientsFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotProbeKanCoefficientsCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y

/-- 元の二重反対添字を、全frame比較と同じ大きさに持ち上げる全関手。 -/
def strictBETotProbeFrameIndex (F : K ⥤ (operad A).Algebra) :
    AsSmall.{u+1} Kᵒᵖᵒᵖ ⥤ AsSmall.{u+1} (operad A).Algebra :=
  AsSmall.down ⋙ (opOpEquivalence K).functor ⋙ F ⋙ AsSmall.up

/-- 同じraw係数の宇宙変更とEx∞は、既存の全Hom比較の第零図式そのもの。 -/
theorem strictBETotProbeKanCoefficients_eq (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) :
    (weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj (strictBETotProbeRightHomDiagram A K F Y) ⋙
      exInfinity = strictBETotProbeFrameIndex A K F ⋙
        FrameHom.rightFrameHammockKanDiagram
          ((SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
            (framedLimitProbe A Y)) (rightFrameFamily A) 0 ⋙ kanObjectForget := rfl

/-- 元の同じprobeのraw Hom係数のKan性。 -/
theorem strictBETotProbeRightHomDiagram_kanComplex (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : Kᵒᵖᵒᵖ) :
    KanComplex ((strictBETotProbeRightHomDiagram A K F Y).obj i) :=
  rightFrameHom_kanComplex (rightFrameFamily A) (framedLimitProbe A Y) (F.obj i.unop.unop)

/-- 同じ宇宙変更済みの係数のKan性。 -/
theorem strictBETotProbeUniverseCoefficients_kanComplex (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex (((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
      (strictBETotProbeRightHomDiagram A K F Y)).obj i) := by
  have := strictBETotProbeRightHomDiagram_kanComplex A K F Y (AsSmall.down.obj i)
  change KanComplex ((SSet.uliftFunctor.{u+1,u}).obj
    ((strictBETotProbeRightHomDiagram A K F Y).obj (AsSmall.down.obj i)))
  infer_instance

/-- 同じ係数単位が誘導するBK切断写像はホモトピー同値。 -/
theorem strictBETotProbeBKExInfinityUnit_homotopyEquivalence
    (F : K ⥤ (operad A).Algebra) (Y : (operad A).Algebra) :
    IsSimplicialHomotopyEquivalence (weightedSectionsMap
      (bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ))
      (HomotopyWeight.bousfieldKanExInfinityCoefficientUnit (AsSmall.{u+1} Kᵒᵖᵒᵖ)
        ((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
          (strictBETotProbeRightHomDiagram A K F Y)))) := by
  have (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) := strictBETotProbeUniverseCoefficients_kanComplex A K F Y i
  exact HomotopyWeight.bousfieldKanExInfinityUnit_homotopyEquivalence _ _

/-- 元の同じ普遍BK錐を、指定downと同じEx∞単位へ合成する。 -/
def strictBETotUniversalBKExInfinityCone (F : K ⥤ (operad A).Algebra) :
    bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ) ⟶
      (weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
        (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F)) ⋙ exInfinity :=
  HomotopyWeight.bousfieldKanUniverseCone Kᵒᵖᵒᵖ (strictBETotUniversalBKRightHomCone A K F) ≫
    HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _ _

/-- 元の指定BK点は、同じ宇宙変更と係数単位により同じEx∞錐の零単体へ移る。 -/
theorem strictBETotUniversalBKExInfinityCone_point (F : K ⥤ (operad A).Algebra) :
    ((weightedSectionsMap (bousfieldKanWeight (AsSmall.{u+1} Kᵒᵖᵒᵖ))
      (HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _
        ((weightedDiagramUniverse.{u,u+1} Kᵒᵖᵒᵖ).obj
          (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F))))).app (op ⦋0⦌))
        (((bousfieldKanUniverseSectionsIso.{u,u+1} Kᵒᵖᵒᵖ
          (strictBETotProbeRightHomDiagram A K F ((framedLimitFunctor A K).obj F))).hom).app (op ⦋0⦌)
            (ULift.up (strictBETotUniversalBKRightHomPoint A K F))) =
      HomotopyWeight.nativeWeightedPoint _ (strictBETotUniversalBKExInfinityCone A K F) := by
  rw [strictBETotUniversalBKRightHomPoint, HomotopyWeight.bousfieldKanUniverseSectionsIso_point,
    HomotopyWeight.bousfieldKanExInfinityUnit_point]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
