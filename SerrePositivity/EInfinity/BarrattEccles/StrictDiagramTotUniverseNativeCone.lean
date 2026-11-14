module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotBKNativeSections

/-!
概要：元の同じ普遍BK点の像から、元の頂点を持つ実際のjoin錐を作る。
方針：元の係数単位とR03bの切断比較を適用し、指定頂点の錐と切断の既存全単射で戻す。
規約：大きいAsSmall添字の図式についての一つの錐。全図式射の錐族・極限性は別途示す。
使われ方：IS-W2 R02〜R03の元の指定頂点と錐切断の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
local instance strictBETotUniverseNativeConeModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotUniverseNativeConeFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotUniverseNativeConeCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y

local instance strictBETotUniverseNativeConeCoefficientKan (F : K ⥤ (operad A).Algebra)
    (Y : (operad A).Algebra) (i : AsSmall.{u+1} Kᵒᵖᵒᵖ) :
    KanComplex ((strictBETotProbeKanDiagram A K F Y ⋙ kanObjectForget).obj i) := by
  change KanComplex (exInfinity.obj _)
  infer_instance
attribute [local instance] bousfieldKanHolim_kanComplex

/-- 元の普遍BK点を、同じnative錐切断模型へ送った零単体。 -/
def strictBETotUniverseNativeConePoint (F : K ⥤ (operad A).Algebra) :
    (coherentConeSectionSpace (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A K).obj F)))) _⦋0⦌ :=
  ((strictBETotBKNativeSectionsEquivalence A K F ((framedLimitFunctor A K).obj F)).hom.app
    (Opposite.op ⦋0⦌))
      (HomotopyWeight.nativeWeightedPoint _ (strictBETotUniversalBKExInfinityCone A K F))

/-- 指定された元の頂点を持つ、実際の同じ全図式上のjoin錐。 -/
def strictBETotUniverseNativeCone (F : K ⥤ (operad A).Algebra) :
    JoinCone (strictBETotUniverseSourceDiagram A K F) :=
  ((fixedVertexConeSpaceEquiv (strictBETotUniverseSourceDiagram A K F)
    ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((framedLimitFunctor A K).obj F)))).symm
        (strictBETotUniverseNativeConePoint A K F)).val

/-- 錐の左境界は、元のTotの指定された同じ頂点のYoneda写像。 -/
theorem strictBETotUniverseNativeCone_vertexMap (F : K ⥤ (operad A).Algebra) :
    joinInl (Δ[0] : SSet.{u+1}) _ ≫ (strictBETotUniverseNativeCone A K F).val =
      SSet.yonedaEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A K).obj F))) :=
  ((fixedVertexConeSpaceEquiv (strictBETotUniverseSourceDiagram A K F)
    ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((framedLimitFunctor A K).obj F)))).symm
        (strictBETotUniverseNativeConePoint A K F)).property

/-- 同じ錐を元の指定頂点の切断へ戻すと、元のBK点の同じ像へ戻る。 -/
theorem strictBETotUniverseNativeCone_section (F : K ⥤ (operad A).Algebra) :
    fixedVertexConeSpaceEquiv (strictBETotUniverseSourceDiagram A K F)
      ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A K).obj F)))
      ⟨strictBETotUniverseNativeCone A K F, strictBETotUniverseNativeCone_vertexMap A K F⟩ =
        strictBETotUniverseNativeConePoint A K F :=
  (fixedVertexConeSpaceEquiv (strictBETotUniverseSourceDiagram A K F)
    ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((framedLimitFunctor A K).obj F)))).apply_symm_apply _

end SerrePositivity.EInfinity.BarrattEccles
